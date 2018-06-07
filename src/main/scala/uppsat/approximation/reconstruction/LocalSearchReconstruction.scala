package uppsat.approximation.reconstruction

import uppsat.globalOptions._
import uppsat.approximation.ModelReconstruction

import scala.collection.mutable.{ListBuffer, Set}
import uppsat.ast.ConcreteFunctionSymbol

import scala.collection.mutable.{HashMap, MultiMap}
import uppsat.ast.AST
import uppsat.ast.IndexedFunctionSymbol
import uppsat.ModelEvaluator
import uppsat.ModelEvaluator.Model
import uppsat.theory.FloatingPointTheory
import uppsat.theory.BooleanTheory._
import uppsat.theory.BooleanTheory.BoolEquality
import uppsat.theory.IntegerTheory.{IntEquality, IntegerPredicateSymbol}
import uppsat.theory.FloatingPointTheory.{FPConstantFactory, FPEqualityFactory, FPFPEqualityFactory, FPPredicateSymbol, FPSpecialValuesFactory, FPVar, FloatingPointLiteral, FloatingPointPredicateSymbol, RMVar, RoundingModeEquality}
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.approximation.toolbox.Toolbox

import scala.collection.mutable.Queue
import scala.collection.mutable.Stack
import uppsat.globalOptions


trait LocalSearchReconstruction extends ModelReconstruction {

  def getLastOneIndex(ints: List[Int]): Int = {
    for (i <- (ints.size - 2) to 0 by -1) {
      if (ints(i) == 1)
        return i
    }
    -1
  }

  def copyModel(model: Model): Model = {
    val newModel = new Model()
    newModel.variableValuation = model.variableValuation
    newModel.subexprValuation = model.subexprValuation
    newModel
  }

  def hasModel(models: ListBuffer[(Model, Double)], model : Model): Boolean = {
    var hasModel = false
    models.foreach(x => if(x._1.variableValuation == model.variableValuation
      && x._1.subexprValuation == model.subexprValuation) hasModel = true)
    hasModel
  }

  def modByLastOne(fpConstant: FPConstantFactory, shift: Int, sort:FPSort): ConcreteFunctionSymbol = {
    val (sign, ebits, sbits) = (fpConstant.sign, fpConstant.eBits, fpConstant.sBits)
    val lastOneIndex = getLastOneIndex(sbits)

    var modifyIndex = lastOneIndex + shift
    if (!(modifyIndex < sbits.size))
      modifyIndex = sbits.size - 1
    var neweBits = ebits
    var newsBits = sbits
    if (modifyIndex < 0) {
      val exp = FloatingPointTheory.unbiasExp(ebits, ebits.length)
      val newExp = exp - 1
      neweBits = FloatingPointTheory.intToBits(FloatingPointTheory.biasExp(newExp, ebits.length), ebits.length)
      newsBits = List.fill(exp)(1) ++ sbits.drop(exp + 2)
    } else {
      newsBits = sbits.updated(modifyIndex, 1)

      if (sbits(modifyIndex) == 1)
        newsBits = sbits.updated(modifyIndex, 0)
    }
    val newSymbol = FloatingPointTheory.fp(sign, neweBits, newsBits)(sort)
    newSymbol
  }

  def modifyBits(symbol: ConcreteFunctionSymbol, shift: Int): ConcreteFunctionSymbol = {
    symbol match {
      case fpLit: FloatingPointLiteral =>
        fpLit.getFactory match {
          case fpConstant :FPConstantFactory =>
            val newSymbol = modByLastOne(fpConstant, shift, fpLit.sort)
            newSymbol
          case _ => symbol
        }
      case _ => symbol
    }
  }

  def generateModels(candidateModel: Model, variable: AST, iteration: Int): ListBuffer[Model] = {
    var modelList = ListBuffer() : ListBuffer[Model]
    var noModels = 3

//    if (iteration < 3)
//      noModels = iteration + 1

    for (i <- -1 to noModels) {
      val reconstructedModel = copyModel(candidateModel)

      val newSymbol = modifyBits(candidateModel(variable).symbol, i)
      val newAST = AST(newSymbol, List(), List())

      reconstructedModel.overwrite(variable, newAST)
      modelList += reconstructedModel
    }

    modelList
  }

  def generateNeighborhood(ast: AST, candidateModel: Model, failedAtoms: List[AST], iteration: Int): ListBuffer[Model] = {
    var modelList = ListBuffer() : ListBuffer[Model]

    val variables = failedAtoms.flatMap(_.iterator).toList.filter(x => x.isVariable)

    for (v <- variables) {
      v.symbol match {
        case _: FPVar =>
          modelList = modelList ++ generateModels(candidateModel, v, iteration)
        case _ =>
      }
    }

    modelList
  }

  def calculateScore(failedAtoms: List[AST], model: Model): Double = {
    var score : Double = 0
    for (a <- failedAtoms) {
      val (left, right) = (model(a.children(0)).symbol, model(a.children(1)).symbol)

      (left, right) match {
        case (lfp : FloatingPointLiteral, rfp: FloatingPointLiteral) =>
          val lDouble = FloatingPointTheory.bitsToDouble(lfp)
          val rDouble = FloatingPointTheory.bitsToDouble(rfp)

          a.symbol.name match {
            case FloatingPointTheory.FPFPEqualityFactory.symbolName
            |    FloatingPointTheory.FPEqualityFactory.symbolName =>
              score += Math.abs(lDouble - rDouble)
            case FloatingPointTheory.FPLessThanFactory.symbolName
            |    FloatingPointTheory.FPLessThanOrEqualFactory.symbolName =>
              score += lDouble - rDouble
            case FloatingPointTheory.FPGreaterThanFactory.symbolName
            |    FloatingPointTheory.FPGreaterThanOrEqualFactory.symbolName =>
              score += rDouble - lDouble
            case _ =>
              throw new Exception("Not a valid Predicate " + a.symbol.name)
          }
        case _ =>
      }
    }
    score
  }

  def orderByScore(models: ListBuffer[Model], filteredModels: ListBuffer[(Model, Double)], critical: List[AST], decodedModel: Model, formula: AST): ListBuffer[(Model, Double)] = {
    val newModels = filteredModels
    for (m <- models) {
      val evalM = postReconstruct(formula, m)
      val failedAtoms = critical.filter((x: AST) => decodedModel(x).symbol != evalM(x).symbol)
      val score = calculateScore(failedAtoms, evalM)
      val mTuple = (evalM, score)
      if (!hasModel(newModels, evalM))
        newModels += mTuple
    }
    val sortedModels = newModels.sortBy(_._2)
    sortedModels
  }

  def checkTimeout() : Boolean = {
    false
  }

  def reconstruct(formula: AST, decodedModel: Model) : Model = {
    println("LocalSearchReconstruction")
    var done : Boolean = false
    var steps = 0
    var orderedModels = ListBuffer() : ListBuffer[(Model, Double)]

    var referenceModel = decodedModel
    val critical = Toolbox.retrieveCriticalAtoms(decodedModel)(formula).toList

    val t0 = System.nanoTime()
    while (!done && steps < 20) {
      if (checkTimeout())
        referenceModel
      val reconstructedModel: Model = postReconstruct(formula, referenceModel)
      val failedAtoms = critical.filter( (x : AST) => decodedModel(x).symbol != reconstructedModel(x).symbol)

      if (failedAtoms.nonEmpty){
        // println("Searching for candidates...")
        val neighborHood = generateNeighborhood(formula, reconstructedModel, failedAtoms, steps)
        orderedModels = orderByScore(neighborHood, orderedModels.dropRight(orderedModels.length - 5), critical, decodedModel, formula)

        // Pick model
        println(orderedModels.head._2)
        referenceModel = orderedModels.head._1
        orderedModels.remove(0)
      } else {
        done = true
        println("Model found " + "in iteration " + steps + ": \n" + reconstructedModel)
        referenceModel = reconstructedModel
      }
      steps += 1
    }

    val t1 = System.nanoTime()

    println("LS time elapsed: " + ((t1-t0)/1000000) + "ms")
    referenceModel
  }

  /**
    * Tries to apply the equality-as-assignment heuristic, returning true if successful (else otherwise)
    *
    * Checks whether the root node of the AST is an equality. If so, if one of the sides is an undefined variable,
    * that variables will be assigned the expression of the other side in candidateModel.
    *
    * Note: If the root node of ast is an equality it has to be defined in the decodedModel.
    *
    * @param ast The node to which equality-as-assignment should be applied (node of the full-precision formula)
    * @param decodedModel The model of the approximate formula
    * @param candidateModel The potential model which is under construction (of the full-precision formula),
    *                       will be updated if equality-as-assignment is applied.
    *
    * @return True if equalityAsAssignment could be applied, otherwise false

    */
  def equalityAsAssignment(ast : AST, decodedModel : Model,  candidateModel : Model) : Boolean = {
    ast match {
      case AST(RoundingModeEquality, _ , _)|
           AST(BoolEquality, _, _) |
           AST(IntEquality, _, _)|
           AST(_: FPPredicateSymbol, _, _)
        if (decodedModel(ast).symbol == BoolTrue &&
          (! ast.symbol.isInstanceOf[IndexedFunctionSymbol]
            || ast.symbol.asInstanceOf[FPPredicateSymbol].getFactory == FPEqualityFactory
            || ast.symbol.asInstanceOf[FPPredicateSymbol].getFactory == FPFPEqualityFactory)) => {
        val (lhs, rhs) = (ast.children(0), ast.children(1))
        val (lhsDefined, rhsDefined) = (candidateModel.contains(lhs), candidateModel.contains(rhs))

        ((lhs.isVariable, lhsDefined), (rhs.isVariable, rhsDefined)) match {
          case ((true, false), (true, true)) => {
            candidateModel.set(lhs, candidateModel(rhs))
            candidateModel.set(ast, BoolTrue)
            true
          }
          case ((true, true), (true, false)) => {
            candidateModel.set(rhs, candidateModel(lhs))
            candidateModel.set(ast, BoolTrue)
            true
          }
          case ((true, false), (false, _)) => {
            candidateModel.set(lhs, candidateModel(rhs))
            candidateModel.set(ast, BoolTrue)
            true
          }
          case ((false, _), (true, false)) => {
            candidateModel.set(rhs, candidateModel(lhs))
            candidateModel.set(ast, BoolTrue)
            true
          }
          case (_, _) => {
            false
          }
        }
      }
      case _ => false
    }
  }

  def reconstructNode( decodedModel  : Model, candidateModel : Model, ast : AST) : Model = {
    val AST(symbol, label, children) = ast
    if (children.length > 0) { // && !equalityAsAssignment(ast, decodedModel, candidateModel)) {
      val newChildren = for ( c <- children) yield {
        Toolbox.getCurrentValue(c, decodedModel, candidateModel)
      }

      val newAST = AST(symbol, label, newChildren.toList)
      val newValue = ModelEvaluator.evalAST(newAST, inputTheory)
      verbose(ast.symbol + " " + ast.label + " " + " <- " + newValue.symbol)

      candidateModel.set(ast, newValue)
      candidateModel
    } else {
      /*if(globalOptions.VERBOSE) {
        ast.ppWithModels("", decodedModel, candidateModel, false)
      }*/
      candidateModel
    }
  }

  def reconstructSubtree(ast : AST, decodedModel : Model, candidateModel : Model) : Model = {
    AST.postVisit[Model, Model](ast, candidateModel, decodedModel, reconstructNode)
    candidateModel
  }

  def basicReconstruct(ast : AST, decodedModel : Model) : Model = {
    val candidateModel = new Model()


    val todo = new Stack[AST]()
    todo.push(ast)

    val toEvaluateEquality = ListBuffer() : ListBuffer[AST]
    val toEvaluateBoolean = new Stack[AST]()
    val toReconstructPredicate = new Queue[AST]()

    // Traverse the tree and add all nodes to respective list
    while (!todo.isEmpty) {
      val nextItem = todo.pop()
      (nextItem.symbol) match {
        case (RoundingModeEquality)|
             FPEqualityFactory(_) |
             FPFPEqualityFactory(_) => {
          toEvaluateEquality += nextItem
        }

        case intPred : IntegerPredicateSymbol => {
          toReconstructPredicate += nextItem
        }

        case fpPred : FloatingPointPredicateSymbol => {
          toReconstructPredicate += nextItem
        }

        case _ if nextItem.symbol.sort == BooleanSort => {
          toEvaluateBoolean.push(nextItem)
          for (c <- nextItem.children)
            todo.push(c)
        }
      }
    }

    val equalitySort = Toolbox.topologicalSortEqualities(toEvaluateEquality.toList)

    equalitySort.map(reconstructSubtree(_, decodedModel, candidateModel))
    toReconstructPredicate.map(reconstructSubtree(_, decodedModel, candidateModel))
    toEvaluateBoolean.map(reconstructNode(decodedModel, candidateModel, _))
    candidateModel
  }

  def postReconstruct(ast : AST, decodedModel : Model) : Model = {
    val reconstructedModel = new Model()
    AST.postVisit[Model, Model](ast, reconstructedModel, decodedModel, reconstructNode)
    reconstructedModel
  }
}