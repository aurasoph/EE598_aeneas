import AeneasPlayground.Gen.BinaryHeap

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AeneasPlayground.binary_heap_spec

open binary_heap

/-- Abstract content of a heap, relative to a chosen `Vec → List` interpretation. -/
def toList
  (toListVec : alloc.vec.Vec Std.I32 → _root_.List Std.I32)
  (h : binary_heap.MinHeap) : _root_.List Std.I32 :=
  toListVec h.a

/-- `m` is a lower bound of all elements in `xs`. -/
def IsLowerBound (m : Std.I32) (xs : _root_.List Std.I32) : Prop :=
  ∀ y, y ∈ xs → m ≤ y

end AeneasPlayground.binary_heap_spec
