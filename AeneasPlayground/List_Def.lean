import AeneasPlayground.Gen.List

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AeneasPlayground
namespace list_spec

open list

/--
Pure interpretation of the extracted linked-list spine.

`toListAux` maps an optional extracted node pointer to a Lean list of elements.
This is the primary abstraction used in functional-correctness statements.
-/
def toListAux : Option list.Node → _root_.List Std.I32
  | none => []
  | some (list.Node.mk x nxt) => x :: toListAux nxt

/--
Pure interpretation of the extracted `list.List` wrapper.

This simply forwards to `toListAux` on the `head` field.
-/
def toList (xs : list.List) : _root_.List Std.I32 :=
  toListAux xs.head

/-!
## Definitional rewriting lemmas

These lemmas are intended for `simp` and normalize goals into the expected
canonical forms for `toList` / `toListAux`.
-/

@[simp] theorem toListAux_none :
    toListAux (none : Option list.Node) = ([] : _root_.List Std.I32) := by
  simp [toListAux]

@[simp] theorem toListAux_some (x : Std.I32) (nxt : Option list.Node) :
    toListAux (some (list.Node.mk x nxt)) = x :: toListAux nxt := by
  simp [toListAux]

@[simp] theorem toList_mk (h : Option list.Node) :
    toList { head := h } = toListAux h := by
  rfl

/-- Any allocated node denotes a nonempty abstract list. -/
theorem toListAux_some_ne_nil (n : list.Node) : toListAux (some n) ≠ [] := by
  cases n with
  | mk x nxt =>
      simp

/-- Characterization of emptiness for the pointer representation. -/
theorem toListAux_eq_nil_iff :
    ∀ o : Option list.Node, toListAux o = [] ↔ o = none
  | none => by simp
  | some n => by
      simp [toListAux_some_ne_nil]

end list_spec
end AeneasPlayground
