package uppsat.solver;

trait SMTSolver {
  def solve(formula : String) : Boolean
  def evaluate(formula : String) : String
  def getModel(formula : String, extractSymbols : List[String]) : Map[String, String]
  def getAnswer(formula : String) : String 
}
