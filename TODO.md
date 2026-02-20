# TODO

1. Keep the Rust extraction minimal (no `Debug`/fmt in extracted surface; keep helpers like `to_vec` test-only).
2. Re-run Aeneas and confirm the generated Lean code builds with `lake build`.
3. Create a abstraction `toList : rust_list.List → List I32` (or `List Int`) and basic helper lemmas for `Option Node`.
4. Prove `push_front` correctness w.r.t. `toList`.
5. Prove `push_back` correctness (likely via a lemma about `push_back_loop` rebuilding the spine).
6. Prove `append` correctness (with a lemma for `append_loop` and the empty/non-empty split).
7. Prove `reverse_iter` correctness (with an accumulator lemma for `reverse_iter_loop`).
8. Identify repetitive “monadic plumbing” steps in these proofs
9. Implement a small Lean 4 meta-tool (tactic or simp extensions) to automate: bounded symbolic execution steps, Result-branch elimination, and goal normalization.
10. Refactor at least one proof (e.g., `push_back`) to use the meta-tool and document the before/after reduction in boilerplate.