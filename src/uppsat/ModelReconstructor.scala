package uppsat

import uppsat.precision.PrecisionMap.Path
import uppsat.Encoder.PathMap
import uppsat.ModelReconstructor.Model
import uppsat.theory.Theory
import uppsat.approximation.Approximation
import ast.AST
import uppsat.solver.SMTSolver
import uppsat.solver.SMTTranslator

object ModelReconstructor {
  type Model = Map[Path, AST]
  
  def valAST(ast: AST, assignments: List[(String, String)], theory : Theory, solver : SMTSolver): Boolean = {
    val translator = new SMTTranslator(theory)
    val smtVal = translator.translate(ast, assignments)
    solver.solve(smtVal)    
  }
}

class ModelReconstructor[T](approximation : Approximation[T]) {
  // Given an original formula (ast), and a model over an approximate formula (model).
  // created using a PathMap (sourceToEncoding), translate it to a model over the original formula
  def reconstruct(ast : AST, model : Model) : Model = {
    approximation.reconstruct(ast, model)
  }
}