import AeneasPlayground.Gen.BstSet

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AeneasPlayground
namespace bst_set_spec

open bst_set

/-- Pure membership predicate on an extracted BST node pointer. -/
def memAux : Option bst_set.Node → Std.I32 → Prop
  | none, _ => False
  | some (bst_set.Node.mk k l r), x =>
      x = k ∨ memAux l x ∨ memAux r x

/-- Pure membership predicate on an extracted `BstSet`. -/
def mem (s : bst_set.BstSet) (x : Std.I32) : Prop :=
  memAux s.root x

@[simp] theorem memAux_none (x : Std.I32) : memAux (none : Option bst_set.Node) x = False := by
  simp [memAux]

@[simp] theorem memAux_some (k : Std.I32) (l r : Option bst_set.Node) (x : Std.I32) :
    memAux (some (bst_set.Node.mk k l r)) x = (x = k ∨ memAux l x ∨ memAux r x) := by
  simp [memAux]

end bst_set_spec
end AeneasPlayground
