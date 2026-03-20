import AeneasPlayground.BinaryHeap_Def
import AeneasPlayground.Gen.BinaryHeap

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AeneasPlayground.binary_heap_spec

open binary_heap

/--
`MinHeap.new` builds an empty heap, relative to a chosen `Vec → List` interpretation.
-/
theorem new_correct_relative
  (toListVec : alloc.vec.Vec Std.I32 → _root_.List Std.I32)
  (H_new : toListVec (alloc.vec.Vec.new Std.I32) = []) :
    ∃ h, binary_heap.MinHeap.new = ok h ∧
      AeneasPlayground.binary_heap_spec.toList toListVec h = [] := by
  refine ⟨{ a := alloc.vec.Vec.new Std.I32 }, ?_, ?_⟩
  · simp [binary_heap.MinHeap.new]
  · simp [AeneasPlayground.binary_heap_spec.toList, H_new]

/-
Main correctness statements (kept for later).
-/

/-- A lightweight “push increases length by 1” statement (relative). -/
theorem push_length_correct_relative
  (toListVec : alloc.vec.Vec Std.I32 → _root_.List Std.I32)
  (H_push :
    ∀ v x, ∃ v', alloc.vec.Vec.push v x = ok v' ∧ toListVec v' = toListVec v ++ [x])
  (h : binary_heap.MinHeap) (x : Std.I32) :
    ∃ h', binary_heap.MinHeap.push h x = ok h' ∧
      _root_.List.length (AeneasPlayground.binary_heap_spec.toList toListVec h') =
        _root_.List.length (AeneasPlayground.binary_heap_spec.toList toListVec h) + 1 := by
  sorry

/-- `pop_min` returns `none` iff the heap is abstractly empty (relative). -/
theorem pop_min_none_iff_relative
  (toListVec : alloc.vec.Vec Std.I32 → _root_.List Std.I32)
  (H_is_empty :
    ∀ v, alloc.vec.Vec.is_empty Global v = ok (decide (toListVec v = [])))
  (h : binary_heap.MinHeap) :
    (∃ h', binary_heap.MinHeap.pop_min h = ok (none, h')) ↔
      AeneasPlayground.binary_heap_spec.toList toListVec h = [] := by
  sorry

/-- If `pop_min` returns `some m`, then `m` is a lower bound of remaining elements (relative). -/
theorem pop_min_lower_bound_relative
  (toListVec : alloc.vec.Vec Std.I32 → _root_.List Std.I32)
  (h : binary_heap.MinHeap) :
    ∀ m h', binary_heap.MinHeap.pop_min h = ok (some m, h') →
      AeneasPlayground.binary_heap_spec.IsLowerBound m
        (AeneasPlayground.binary_heap_spec.toList toListVec h') := by
  sorry

end AeneasPlayground.binary_heap_spec
