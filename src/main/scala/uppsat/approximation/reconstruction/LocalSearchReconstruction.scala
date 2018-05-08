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
import uppsat.theory.FloatingPointTheory.{FPEqualityFactory, FPFPEqualityFactory, FPPredicateSymbol, FPSpecialValuesFactory, FPVar, FloatingPointLiteral, FloatingPointPredicateSymbol, RMVar, RoundingModeEquality}
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.approximation.toolbox.Toolbox

import scala.collection.mutable.Queue
import scala.collection.mutable.Stack
import uppsat.globalOptions


trait LocalSearchReconstruction extends ModelReconstruction {

  def getLastOneIndex(ints: List[Int]): Int = {
    for (i <- (ints.size - 1) to 0 by -1) {
      if (ints(i) == 1)
        return i
    }
    -1
  }

  def modifyBits(symbol: ConcreteFunctionSymbol): ConcreteFunctionSymbol = {
    symbol match {
      case _: FPSpecialValuesFactory => symbol
      case fpLit: FloatingPointLiteral =>
        val (sign, ebits, sbits) = (fpLit.sign, fpLit.eBits, fpLit.sBits)
        val lastOneIndex = getLastOneIndex(sbits)
        val newsBits = sbits.updated(lastOneIndex + 1, 1)
        val newSymbol = FloatingPointTheory.fp(sign, ebits, newsBits)(fpLit.sort)
        println(lastOneIndex)
        println(symbol + " <- " + newSymbol)
        newSymbol

      case _ => symbol
    }
  }

  def copyModel(model: Model): Model = {
    val newModel = new Model()
    newModel.variableValuation = model.variableValuation
    newModel.subexprValuation = model.subexprValuation
    newModel
  }

  def generateModels(formula: AST, candidateModel: Model, failedAtoms: List[AST]): ListBuffer[Model] = {
    var modelList = ListBuffer() : ListBuffer[Model]

    val atoms = failedAtoms.flatMap(_.iterator).toList
    val variables = atoms.filter(x => x.isVariable)

    println("Variables: ")
    variables.foreach(x => println(x))

    for (v <- variables) {
      v.symbol match {
        case _: FPVar =>
          val reconstructedModel = copyModel(candidateModel)
          println("Assigning new value to " + v)

          val newSymbol = modifyBits(candidateModel(v).symbol)
          val newAST = AST(newSymbol, List(), List())

          reconstructedModel.overwrite(v, newAST)
          modelList += reconstructedModel
        case _ =>
          println("Not FPVar, doing nothing...")
      }
    }

//    AST.postVisit[Model, Model](ast, reconstructedModel, candidateModel, reconstructNode)

//    reconstructedModel
    modelList
  }

  def generateNeighborhood(ast: AST, candidateModel: Model, referenceModel: Model, criticalAtoms: List[AST]): ListBuffer[Model] = {
    val reconstructedModels = generateModels(ast, candidateModel, criticalAtoms)
    reconstructedModels
  }

  def filterByFitness(models: ListBuffer[Model], decodedModel: Model, formula: AST): ListBuffer[Model] = {
    for (m <- models) {
      val critical = Toolbox.retrieveCriticalAtoms(decodedModel)(formula).map(_.iterator).flatten.toList
      val failedAtoms = critical.filter( (x : AST) => decodedModel(x) != m(x))
    }
    models
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
    if (children.length > 0 && !equalityAsAssignment(ast, decodedModel, candidateModel)) {
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

  def reconstruct(formula: AST, decodedModel: Model) : Model = {
    println("LocalSearchReconstruction")
    var done : Boolean = false
    var steps = 0
    var referenceM = decodedModel
    while (!done && steps < 10) {
      val reconstructedModel: Model = basicReconstruct(formula, referenceM)
      val critical = Toolbox.retrieveCriticalAtoms(decodedModel)(formula).flatMap(_.iterator).toList
      val failedAtoms = critical.filter( (x : AST) => decodedModel(x).symbol != reconstructedModel(x).symbol)

      if (failedAtoms.nonEmpty){
        println("Searching for candidates...")
        val neighborHood = generateNeighborhood(formula, reconstructedModel, referenceM, failedAtoms)
        val filteredModels = filterByFitness(neighborHood, decodedModel, formula)

        referenceM = filteredModels.head
      } else {
        done = true
        referenceM = reconstructedModel
      }
      steps += 1
    }

    referenceM
  }
}