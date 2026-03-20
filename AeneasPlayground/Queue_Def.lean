import AeneasPlayground.Gen.Queue

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AeneasPlayground
namespace queue_spec

open queue

/--
Pure interpretation of the extracted optional node pointer as a Lean list.

This is the shared abstraction used both for the internal list representation
(`queue.List`) and for the queue specification.
-/
def toListAux : Option queue.Node → _root_.List Std.I32
  | none => []
  | some (queue.Node.mk x nxt) => x :: toListAux nxt

/--
Pure interpretation of the extracted `queue.List` wrapper.
-/
def toList (xs : queue.List) : _root_.List Std.I32 :=
  toListAux xs.head

/--
Pure interpretation of the extracted queue.

The queue is represented by two lists:
- `front` in dequeue order
- `back` in reverse enqueue order (since `enqueue` pushes to the front of `back`)

The abstract queue contents are therefore:
`toList front ++ reverse (toList back)`.
-/
def toQ (q : queue.Queue) : _root_.List Std.I32 :=
  toList q.front ++ (toList q.back).reverse

/-!
## Definitional rewriting lemmas

These lemmas are intended for `simp` and normalize goals involving `toListAux`,
`toList`, and `toQ`.
-/

@[simp] theorem toListAux_none :
    toListAux (none : Option queue.Node) = ([] : _root_.List Std.I32) := by
  simp [toListAux]

@[simp] theorem toListAux_some (x : Std.I32) (nxt : Option queue.Node) :
    toListAux (some (queue.Node.mk x nxt)) = x :: toListAux nxt := by
  simp [toListAux]

@[simp] theorem toList_mk (h : Option queue.Node) :
    toList { head := h } = toListAux h := by
  rfl

@[simp] theorem toQ_mk (f b : queue.List) :
    toQ { front := f, back := b } = toList f ++ (toList b).reverse := by
  rfl

/-- Any allocated node denotes a nonempty abstract list. -/
theorem toListAux_some_ne_nil (n : queue.Node) : toListAux (some n) ≠ [] := by
  cases n with
  | mk x nxt => simp

end queue_spec
end AeneasPlayground
