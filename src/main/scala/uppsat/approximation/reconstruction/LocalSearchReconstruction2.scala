package uppsat.approximation.reconstruction

import uppsat.ModelEvaluator
import uppsat.ModelEvaluator.Model
import uppsat.approximation.ModelReconstruction
import uppsat.approximation.toolbox.Toolbox
import uppsat.ast.{AST, ConcreteFunctionSymbol, IndexedFunctionSymbol}
import uppsat.globalOptions._
import uppsat.theory.BooleanTheory.{BoolEquality, _}
import uppsat.theory.FloatingPointTheory
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.theory.FloatingPointTheory.{FPConstantFactory, FPEqualityFactory, FPFPEqualityFactory, FPPredicateSymbol, FPVar, FloatingPointLiteral, FloatingPointPredicateSymbol, RoundingModeEquality}
import uppsat.theory.IntegerTheory.{IntEquality, IntegerPredicateSymbol}

import scala.collection.mutable.{ListBuffer, Queue, Stack}


trait LocalSearchReconstruction2 extends ModelReconstruction {
  val LAST_ONE = 0
  val MOVE_ONE = 1

  def getLastOneIndex(ints: List[Int], from: Int): Int = {
    for (i <- from to 0 by -1) {
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

  def flipBits(fp: List[Int], from: Int, end: Int): List[Int] = {
    var flippedFp = fp
    for (i <- from to end) {
      if (fp(i) == 0) {
        flippedFp = flippedFp.updated(i, 1)
      } else {
        flippedFp = flippedFp.updated(i, 0)
      }
    }
    flippedFp
  }

  def modByLastOne(fpConstant: FPConstantFactory, shift: Int, sort:FPSort): ConcreteFunctionSymbol = {
    val (sign, ebits, sbits) = (fpConstant.sign, fpConstant.eBits, fpConstant.sBits)
    var lastOneIndex = getLastOneIndex(sbits, sbits.length - 1)
    var neweBits = ebits
    var newsBits = sbits

    if (shift < 0) {
      val newBits = makeSmaller(fpConstant, shift)
      neweBits = newBits._1
      newsBits = newBits._2
    } else {
      if (lastOneIndex < 0)
        lastOneIndex = 0
      var modifyIndex = lastOneIndex + shift
      if (!(modifyIndex < sbits.size))
        modifyIndex = sbits.size - 1


      if (sbits(modifyIndex) == 1)
        newsBits = sbits.updated(modifyIndex, 0)
      else
        newsBits = sbits.updated(modifyIndex, 1)
    }
    val newSymbol = FloatingPointTheory.fp(sign, neweBits, newsBits)(sort)
    newSymbol
  }

  def moveLastOne(fpConstant: FPConstantFactory, shift: Int, sort:FPSort): ConcreteFunctionSymbol = {
    val (sign, ebits, sbits) = (fpConstant.sign, fpConstant.eBits, fpConstant.sBits)

    val lastOneIndex = getLastOneIndex(sbits, sbits.length-1)

    var neweBits = ebits
    var newsBits = sbits
    if (shift < 0) {
      val newBits = makeSmaller(fpConstant, shift)
      neweBits = newBits._1
      newsBits = newBits._2
    } else if (lastOneIndex >= 0 && lastOneIndex + shift < sbits.length - 1) {
      newsBits = sbits.updated(lastOneIndex, 0)
      newsBits = sbits.updated(lastOneIndex + shift, 1)
    } else {
      newsBits = sbits.updated(lastOneIndex + shift + 1, 1)
    }
    val newSymbol = FloatingPointTheory.fp(sign, neweBits, newsBits)(sort)
    newSymbol
  }

  def makeSmaller(fpConstant: FPConstantFactory, shift: Int): (List[Int], List[Int]) = {
    val (sign, ebits, sbits) = (fpConstant.sign, fpConstant.eBits, fpConstant.sBits)
    val exp = FloatingPointTheory.unbiasExp(ebits, ebits.length)
    val lastOneIndex = getLastOneIndex(sbits, sbits.size - 2)

    var newsBits = sbits
    var neweBits = ebits

    if (lastOneIndex < 0) {
      val newExp = exp - 1
      neweBits = FloatingPointTheory.intToBits(FloatingPointTheory.biasExp(newExp, ebits.length), ebits.length)
      newsBits = flipBits(newsBits, 0, exp - shift)
    } else if (lastOneIndex < exp) {
      newsBits = flipBits(newsBits, lastOneIndex, exp - shift)
    } else {
      newsBits = flipBits(newsBits, lastOneIndex, lastOneIndex - shift)
    }

    val newBits = (neweBits, newsBits)
    newBits
  }



  def modifyBits(symbol: ConcreteFunctionSymbol, shift: Int, method: Int): ConcreteFunctionSymbol = {
    symbol match {
      case fpLit: FloatingPointLiteral =>
        fpLit.getFactory match {
          case fpConstant :FPConstantFactory =>
          method match {
            case LAST_ONE =>
              val newSymbol = modByLastOne(fpConstant, shift, fpLit.sort)
              newSymbol
            case _ =>
              val newSymbol = moveLastOne(fpConstant, shift, fpLit.sort)
              newSymbol
          }
          case _ => symbol
        }
      case _ => symbol
    }
  }

  def generateModels(candidateModel: Model, variable: AST, iteration: Int): ListBuffer[ConcreteFunctionSymbol] = {
    var modelList = ListBuffer() : ListBuffer[ConcreteFunctionSymbol]
    var noModels = 3
    var method = LAST_ONE

    if (iteration < 3)
      noModels = iteration + 1

    for (i <- -noModels to noModels) {
      val newSymbol = modifyBits(candidateModel(variable).symbol, i, method)
      modelList += newSymbol
    }

    modelList
  }

  def generateNeighborhood(ast: AST, candidateModel: Model, failedAtoms: List[AST], iteration: Int): ListBuffer[(AST, ListBuffer[ConcreteFunctionSymbol])] = {
    var modelList = ListBuffer() : ListBuffer[(AST, ListBuffer[ConcreteFunctionSymbol])]

    val variables = failedAtoms.flatMap(_.iterator).toList.filter(x => x.isVariable)
    var vList = ListBuffer() : ListBuffer[ConcreteFunctionSymbol]

    for (v <- variables) {
      if (!(vList contains v.symbol)) {
        vList += v.symbol
        v.symbol match {
          case _: FPVar =>
            val tuple = (v, generateModels(candidateModel, v, iteration))
            modelList += tuple
          case _ =>
        }
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
          (lfp.getFactory, rfp.getFactory) match {
            case (_: FPConstantFactory, _: FPConstantFactory) =>
              a.symbol.name match {
                case FloatingPointTheory.FPFPEqualityFactory.symbolName
                     | FloatingPointTheory.FPEqualityFactory.symbolName =>
                  score += Math.abs(lDouble - rDouble)
                case FloatingPointTheory.FPLessThanFactory.symbolName
                     | FloatingPointTheory.FPLessThanOrEqualFactory.symbolName =>
                  score += lDouble - rDouble
                case FloatingPointTheory.FPGreaterThanFactory.symbolName
                     | FloatingPointTheory.FPGreaterThanOrEqualFactory.symbolName =>
                  score += rDouble - lDouble
                case _ =>
                  throw new Exception("Not a valid Predicate " + a.symbol.name)
              }
            case _ =>
          }
        case _ =>
      }
    }
    score
  }

  def orderByScore(models: ListBuffer[(AST, ListBuffer[ConcreteFunctionSymbol])], critical: List[AST], decodedModel: Model, referenceModel: Model, formula: AST): ListBuffer[(Model, Double)] = {
    var newModels = ListBuffer() : ListBuffer[(Model, Double)]
    for (m <- models) {
      var modelCopy = copyModel(referenceModel)
      var bestScore = 10000.0
      var bestVal = AST(m._2.head, List(), List())
      for (a <- m._2) {
        val newAST = AST(a, List(), List())
        modelCopy.overwrite(m._1, newAST)
        val evalM = postReconstruct(formula, modelCopy)
        val failedAtoms = critical.filter((x: AST) => decodedModel(x).symbol != evalM(x).symbol)
        val score = calculateScore(failedAtoms, evalM)
        if (score < bestScore) {
          bestScore = score
          bestVal = newAST
        }
      }
      modelCopy.overwrite(m._1, bestVal)
      val newTuple = (modelCopy, bestScore)
      newModels += newTuple
    }
    val sortedModels = newModels.sortBy(_._2)
    sortedModels
  }


  def checkTimeout() : Boolean = {
    false
  }

  def reconstruct(formula: AST, decodedModel: Model) : Model = {
    println("LocalSearchReconstruction2")
    var done : Boolean = false
    var steps = 0
    var referenceModel = decodedModel
    val critical = Toolbox.retrieveCriticalAtoms(decodedModel)(formula).toList

    val t0 = System.nanoTime()
    while (!done && steps < 10) {
      if (checkTimeout())
        referenceModel
      val reconstructedModel: Model = postReconstruct(formula, referenceModel)
      val failedAtoms = critical.filter( (x : AST) => decodedModel(x).symbol != reconstructedModel(x).symbol)

      if (failedAtoms.nonEmpty){
        // println("Searching for candidates...")
        val neighborHood = generateNeighborhood(formula, reconstructedModel, failedAtoms, steps)
        val orderedModels = orderByScore(neighborHood, critical, decodedModel, referenceModel, formula)

        // Order Models
        println(orderedModels.head._2)
        referenceModel = orderedModels.head._1
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