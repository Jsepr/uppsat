package uppsat

import BooleanTheory._
import IntegerTheory._
// TODO: How do we handle quantifiers. Should we have different types of AST?
// TODO: What do we do with let-expressions.
// TODO: Sharing, how do we accommodate? Enforced sharing (seems like a bad idea?)
// TODO: We can use implicit conversion

// ASKPC: Is this a good way? (syntactic sugar)
// DD: 1) "Cannot" inherit case classes
//     2) Typing the AST messed up matching with Node (e.g., in translator)
abstract class Node(val symbol : ConcreteFunctionSymbol) {
  
  def symbols : Set[ConcreteFunctionSymbol]= {
      this match {
        case InternalNode(symbol, desc) => desc.foldLeft (Set(symbol)) ((s1,s2) => s1 ++ s2.symbols)
        case LeafNode(symbol) => Set(symbol)
      }
  }
  
  def nodes : Set[Node]= {
      this match {
        case InternalNode(symbol, desc) => desc.foldLeft (Set(this)) ((s1,s2) => s1 ++ s2.nodes)
        case LeafNode(symbol) => Set(this)
      }
  }
  
  //Syntactic sugar
  def &(that : Node) = {
     (this.symbol.sort, that.symbol.sort) match {
       case (BooleanSort, BooleanSort) => boolAnd(this, that)
     }
  }
  
  def unary_! = {
     this.symbol.sort match {
       case BooleanSort => boolNot(this)
     }
  }
  
  def +(that : Node) = {
     (this.symbol.sort, that.symbol.sort) match {
       case (IntegerSort, IntegerSort) => intAddition(this, that)
     }
  }
  
  def -(that : Node) = {
     (this.symbol.sort, that.symbol.sort) match {
       case (IntegerSort, IntegerSort) => intSubstraction(this, that)
     }
  }
  
  //TODO: Check which one to use
  def ===(that : Node) = {
    (this.symbol.sort, that.symbol.sort) match {
       case (IntegerSort, IntegerSort) => intEquality(this, that)
     }
  }
  
  def <=(that : Node) = {
    (this.symbol.sort, that.symbol.sort) match {
       case (IntegerSort, IntegerSort) => intLessThanOrEqual(this, that)
     }
  }
}
case class InternalNode(override val symbol : ConcreteFunctionSymbol, desc : Seq[Node]) extends Node(symbol) {
  override def toString = symbol.toString + "(" + desc.map(_.toString).mkString(", ") + ")"
}

case class LeafNode(override val symbol : ConcreteFunctionSymbol) extends Node(symbol) {
  override def toString = symbol.toString
}