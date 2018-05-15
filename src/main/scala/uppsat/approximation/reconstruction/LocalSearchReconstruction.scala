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

  def modifyBits(symbol: ConcreteFunctionSymbol, shift: Int): ConcreteFunctionSymbol = {
    symbol match {
      case fpLit: FloatingPointLiteral =>
        fpLit.getFactory match {
          case fpConstant :FPConstantFactory =>
            val (sign, ebits, sbits) = (fpConstant.sign, fpConstant.eBits, fpConstant.sBits)
            val lastOneIndex = getLastOneIndex(sbits)

            var modifyIndex = lastOneIndex + shift
            if (!(modifyIndex < sbits.size))
              modifyIndex = sbits.size - 1
            val newsBits = sbits.updated(modifyIndex, 1)
            val newSymbol = FloatingPointTheory.fp(sign, ebits, newsBits)(fpLit.sort)
            newSymbol
          case _ => symbol
        }
      case _ => symbol
    }
  }

  def copyModel(model: Model): Model = {
    val newModel = new Model()
    newModel.variableValuation = model.variableValuation
    newModel.subexprValuation = model.subexprValuation
    newModel
  }

  def generateModels(candidateModel: Model, variable: AST): ListBuffer[Model] = {
    var modelList = ListBuffer() : ListBuffer[Model]

    for (i <- 1 to 5) {
      val reconstructedModel = copyModel(candidateModel)

      val newSymbol = modifyBits(candidateModel(variable).symbol, i)
      val newAST = AST(newSymbol, List(), List())

      reconstructedModel.overwrite(variable, newAST)
      modelList += reconstructedModel
    }

    modelList
  }

  def generateNeighborhood(ast: AST, candidateModel: Model, referenceModel: Model, failedAtoms: List[AST]): ListBuffer[Model] = {
    var modelList = ListBuffer() : ListBuffer[Model]

    val fitness = failedAtoms.size
    val atoms = failedAtoms.flatMap(_.iterator).toList
    val variables = atoms.filter(x => x.isVariable)

    for (v <- variables) {
      v.symbol match {
        case _: FPVar =>
          modelList ++= generateModels(candidateModel, v)
        case _ =>
      }
    }

    modelList
  }

  def hasModel(models: ListBuffer[(Model, Double)], model : Model): Boolean = {
    var hasModel = false
    models.foreach(x => if(x._1.variableValuation == model.variableValuation
      && x._1.subexprValuation == model.subexprValuation) hasModel = true)
    hasModel
  }

  def calculateFitness(failedAtoms: List[AST], model: Model): Double = {
    var fitness : Double = 0
    for (a <- failedAtoms) {
      val (left, right) =
        (model(a.children(0)).symbol, model(a.children(1)).symbol)
      (left, right) match {
        case (lfp : FloatingPointLiteral, rfp: FloatingPointLiteral) =>
          val lDouble = FloatingPointTheory.bitsToDouble(lfp)
          val rDouble = FloatingPointTheory.bitsToDouble(rfp)

          a.symbol.name match {
            case FloatingPointTheory.FPFPEqualityFactory.symbolName
            |    FloatingPointTheory.FPEqualityFactory.symbolName =>
              fitness += Math.abs(lDouble - rDouble)
            case FloatingPointTheory.FPLessThanFactory.symbolName
            |    FloatingPointTheory.FPLessThanOrEqualFactory.symbolName =>
              fitness += lDouble - rDouble
            case FloatingPointTheory.FPGreaterThanFactory.symbolName
            |    FloatingPointTheory.FPGreaterThanOrEqualFactory.symbolName =>
              fitness += rDouble - lDouble
            case _ =>
              throw new Exception("Not a valid Predicate " + a.symbol.name)
          }
        case _ =>
      }
    }
    fitness
  }

  def filterByFitness(models: ListBuffer[Model], filteredModels: ListBuffer[(Model, Double)], decodedModel: Model, formula: AST): ListBuffer[(Model, Double)] = {
    for (m <- models) {
      val evalM = postReconstruct(formula, m)
      val critical = Toolbox.retrieveCriticalAtoms(decodedModel)(formula).toList
      val failedAtoms = critical.filter((x: AST) => decodedModel(x).symbol != evalM(x).symbol)
      val fitness = calculateFitness(failedAtoms, evalM)
      val mTuple = (evalM, fitness)
      if (!hasModel(filteredModels, evalM))
        filteredModels += mTuple
    }
    val sortedModels = filteredModels.sortBy(_._2)
    sortedModels
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

  def reconstruct(formula: AST, decodedModel: Model) : Model = {
    println("LocalSearchReconstruction")
    var done : Boolean = false
    var steps = 0
    var filteredModels = ListBuffer() : ListBuffer[(Model, Double)]

    var referenceM = decodedModel
    val critical = Toolbox.retrieveCriticalAtoms(decodedModel)(formula).toList

    println("Searching for candidates...")
    while (!done && steps < 10) {
      val reconstructedModel: Model = postReconstruct(formula, referenceM)
      val failedAtoms = critical.filter( (x : AST) => decodedModel(x).symbol != reconstructedModel(x).symbol)

      if (failedAtoms.nonEmpty){
        val neighborHood = generateNeighborhood(formula, reconstructedModel, referenceM, failedAtoms)
        filteredModels = filterByFitness(neighborHood, filteredModels, decodedModel, formula)

        referenceM = filteredModels.head._1
        println("Candidate model: ")
        println("Fitness: " + filteredModels.head._2)
        println(referenceM)
        filteredModels.remove(0)
      } else {
        done = true
        println("Model found: " + reconstructedModel)
        referenceM = reconstructedModel
      }
      steps += 1
    }

    referenceM
  }
}