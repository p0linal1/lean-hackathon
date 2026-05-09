import Std.Data.HashMap
import Std.Data.HashSet

structure Node where
  id : Nat
deriving Repr, DecidableEq, Hashable

structure Domino where
  left : Nat
  right : Nat
deriving Repr, DecidableEq

structure Pip where
  board: Std.HashMap Node (Std.HashSet Node)
deriving Repr


def Pip.empty : Pip :=
  { board := Std.HashMap.emptyWithCapacity 64 }

inductive SumConstraintType where
  | eq
  | lt
  | gt
deriving Repr

inductive Constraint where
  | sum   (ns : Std.HashSet Node) (c : Nat) (t : SumConstraintType)
  | equiv (ns : Std.HashSet Node) (c : Nat)
deriving Repr
