package uppsat.approximation.reconstruction

import uppsat.approximation.ModelReconstruction
import uppsat.ModelEvaluator.Model
import uppsat.ast.AST

trait PostOrderReconstruction extends ModelReconstruction {
  def reconstructNode( decodedM : Model,  candidateM : Model, ast :  AST) : Model //satisfy

  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    val reconstructedModel = new Model()
    AST.postVisit[Model, Model](ast, reconstructedModel, decodedModel, reconstructNode)
    reconstructedModel
  }

  // Utility function
  def getCurrentValue(ast : AST, decodedModel : Model, candidateModel : Model) : AST = {
    if (! candidateModel.contains(ast)) {
      candidateModel.set(ast, decodedModel(ast))
    }
    candidateModel(ast)
  }
}