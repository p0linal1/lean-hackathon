import Std.Data.HashMap
import Std.Data.HashSet

structure Node where
  id : Nat
deriving Repr, DecidableEq, Hashable, BEq

structure Domino where
  left : Nat
  right : Nat
deriving Repr, DecidableEq, BEq

structure Pip where
  board: Std.HashMap Node (Std.HashSet Node)
deriving Repr, BEq

def adjacent (pip: Pip) (n₁ n₂ : Node) : Bool :=
  match pip.board.get? n₁ with
  | some neighbors => neighbors.contains n₂
  | none => false

def Assignment := Std.HashMap Node (Node × Node)

def Pip.empty : Pip :=
  { board := Std.HashMap.emptyWithCapacity 64 }

inductive SumConstraintType where
  | eq
  | lt
  | gt
deriving Repr, DecidableEq, BEq, Hashable

inductive Constraint where
  | sum   (ns : List Node) (c : Nat) (t : SumConstraintType)
  | equiv (ns : List Node) (c : Nat)
deriving Repr, BEq, Hashable

def Constraints := Std.HashSet Constraint

-- def assignment_is_valid (pip : Pip) (assignment : Assignment) : Bool :=
--   assignment.all (fun (node, (left, right)) =>
--     match pip.board.find? node with
--     | some neighbors => neighbors.contains left && neighbors.contains right
--     | none => false
--   )
