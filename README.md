# README

## Goal

Verify small **safe Rust** data structures by translating them to Lean 4 with **Aeneas** and proving functional correctness against simple pure specifications. A secondary goal is to reduce recurring Aeneas proof boilerplate (unfolding `Result`/`do`, branch elimination, loop stepping, goal normalization) with small Lean automation.

## Main definitions

Aeneas-generated code lives in `AeneasPlayground/Gen/*.lean`. For each verified structure we add a `*_Def.lean` spec layer and a `*_Proofs.lean` file.

### List
- `List_Def.lean`
  - `toListAux : Option list.Node → List Std.I32` — interprets the extracted pointer spine as a pure list
  - `toList : list.List → List Std.I32` — abstraction for the extracted list
- `List_Proofs.lean` — correctness proofs for list operations w.r.t. `toList`

### Queue
- `Queue_Def.lean`
  - `toListAux : Option queue.Node → List Std.I32`
  - `toList : queue.List → List Std.I32`
  - `toQ : queue.Queue → List Std.I32` — abstraction: `toList front ++ reverse (toList back)`
- `Queue_Proofs.lean` — correctness lemmas for list helpers + queue operations

### BST Set
- `BstSet_Def.lean`
  - `memAux : Option bst_set.Node → Std.I32 → Prop` — pure membership predicate over the tree shape
  - `mem : bst_set.BstSet → Std.I32 → Prop`
- `BstSet_Proofs.lean`
  - `insert_loop_total` — `insert_loop` always returns `ok`
  - `insert_loop_mem` — inserting `k` adds `k` to membership
  - `insert_mem_self`, `insert_preserves_mem`

### Binary Heap
- `BinaryHeap_Def.lean`
  - `toList : (Vec → List) → MinHeap → List Std.I32` — heap contents relative to a chosen `Vec` interpretation
  - `IsLowerBound : Std.I32 → List Std.I32 → Prop`
- `BinaryHeap_Proofs.lean`
  - `new_correct_relative` proved
  - `push_length_correct_relative`, `pop_min_none_iff_relative`, `pop_min_lower_bound_relative` stated relative to hypotheses about `Vec` ops (since Aeneas models several `Vec` operations as axioms)

## Main theorems (high level)

- List: `push_front_correct`, `push_back_correct`, `append_correct`, `reverse_iter_correct`, `pop_front_correct`, `len_correct_relative` (relative to Aeneas’ `Option.as_ref`)
- Queue: `enqueue_correct`, `queue_is_empty_correct` (and planned `dequeue_correct`)
- BST Set: `insert_mem_self`, `insert_preserves_mem` (proved via `insert_loop_mem`)
- Binary Heap: `new_correct_relative` (proved), plus the three relative correctness statements listed above

## References

- [Aeneas (Lean backend) repository/documentation](https://github.com/AeneasVerif/aeneas)
- [Lean 4](https://github.com/leanprover/lean4)

## Future work

- Finish any remaining `sorry` proofs (notably deeper queue/heap properties).
- Extend specs/proofs to more generated structures
- Add small Lean helpers/tactics for common Aeneas proof steps and refactor at least one proof to use them.