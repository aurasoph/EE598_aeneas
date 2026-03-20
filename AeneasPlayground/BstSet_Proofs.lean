import AeneasPlayground.BstSet_Def
import AeneasPlayground.Gen.BstSet

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AeneasPlayground
namespace bst_set_spec

open bst_set

/-- `insert_loop` is total: it always returns `ok out` for some `out`. -/
theorem insert_loop_total (k : Std.I32) :
    ∀ cur : Option bst_set.Node, ∃ out, bst_set.BstSet.insert_loop k cur = ok out := by
  intro cur
  cases cur with
  | none =>
      refine ⟨some (bst_set.Node.mk k none none), ?_⟩
      simp [bst_set.BstSet.insert_loop]
  | some n =>
      cases n with
      | mk nk l r =>
          by_cases hk : k = nk
          · refine ⟨some (bst_set.Node.mk nk l r), ?_⟩
            simp [bst_set.BstSet.insert_loop, hk]
          · by_cases hlt : k < nk
            · rcases insert_loop_total (k := k) l with ⟨outL, houtL⟩
              refine ⟨some (bst_set.Node.mk nk outL r), ?_⟩
              simp [bst_set.BstSet.insert_loop, hk, hlt, houtL]
            · rcases insert_loop_total (k := k) r with ⟨outR, houtR⟩
              refine ⟨some (bst_set.Node.mk nk l outR), ?_⟩
              simp [bst_set.BstSet.insert_loop, hk, hlt, houtR]

/--
Key lemma (monadic form):

If `insert_loop k cur = ok out`, then membership in `out` is exactly membership
in `cur` plus the new key `k`.
-/
theorem insert_loop_mem (k x : Std.I32) :
    ∀ cur : Option bst_set.Node,
      ∀ out, bst_set.BstSet.insert_loop k cur = ok out →
        (memAux out x ↔ (x = k ∨ memAux cur x)) := by
  intro cur
  cases cur with
  | none =>
      intro out hout
      have : ok out = ok (some (bst_set.Node.mk k none none)) := by
        simpa [bst_set.BstSet.insert_loop] using Eq.symm hout
      cases this
      simp
  | some n =>
      cases n with
      | mk nk l r =>
          intro out hout
          by_cases hk : k = nk
          ·
            have : ok out = ok (some (bst_set.Node.mk nk l r)) := by
              simpa [bst_set.BstSet.insert_loop, hk] using Eq.symm hout
            cases this
            subst hk
            simp
          ·
            by_cases hlt : (↑k : Int) < (↑nk : Int)
            ·
              cases hback : bst_set.BstSet.insert_loop k l with
              | ok back =>
                  have hout' : ok out = ok (some (bst_set.Node.mk nk back r)) := by
                    simpa [bst_set.BstSet.insert_loop, hk, hlt, hback] using Eq.symm hout
                  cases hout'
                  have IH :
                      memAux back x ↔ (x = k ∨ memAux l x) := by
                    exact insert_loop_mem (k := k) (x := x) l back (by simp [hback])
                  simp [IH, or_assoc, or_left_comm]
              | fail e =>
                  have : (fail e : Result (Option bst_set.Node)) = ok out := by
                    simp [bst_set.BstSet.insert_loop, hk, hlt, hback] at hout
                  cases this
              | div =>
                  have : (div : Result (Option bst_set.Node)) = ok out := by
                    simp [bst_set.BstSet.insert_loop, hk, hlt, hback] at hout
                  cases this
            ·
              cases hback : bst_set.BstSet.insert_loop k r with
              | ok back =>
                  have hout' : ok out = ok (some (bst_set.Node.mk nk l back)) := by
                    simpa [bst_set.BstSet.insert_loop, hk, hlt, hback] using Eq.symm hout
                  cases hout'
                  have IH :
                      memAux back x ↔ (x = k ∨ memAux r x) := by
                    exact insert_loop_mem (k := k) (x := x) r back (by simp [hback])
                  simp [IH, or_left_comm]
              | fail e =>
                  have : (fail e : Result (Option bst_set.Node)) = ok out := by
                    simp [bst_set.BstSet.insert_loop, hk, hlt, hback] at hout
                  cases this
              | div =>
                  have : (div : Result (Option bst_set.Node)) = ok out := by
                    simp [bst_set.BstSet.insert_loop, hk, hlt, hback] at hout
                  cases this

/-- After `insert`, the inserted key is a member. -/
theorem insert_mem_self (s : bst_set.BstSet) (k : Std.I32) :
    ∃ s', bst_set.BstSet.insert s k = ok s' ∧ mem s' k := by
  -- Use totality to get the ok-witness.
  rcases insert_loop_total (k := k) s.root with ⟨out, hout⟩
  refine ⟨{ root := out }, ?_, ?_⟩
  · simp [bst_set.BstSet.insert, hout]
  · have H := insert_loop_mem (k := k) (x := k) s.root out hout
    have : k = k ∨ memAux s.root k := Or.inl rfl
    exact (H.mpr this)

/-- `insert` preserves membership of any existing element. -/
theorem insert_preserves_mem (s : bst_set.BstSet) (k x : Std.I32) :
    mem s x → ∃ s', bst_set.BstSet.insert s k = ok s' ∧ mem s' x := by
  intro hx
  rcases insert_loop_total (k := k) s.root with ⟨out, hout⟩
  refine ⟨{ root := out }, ?_, ?_⟩
  · simp [bst_set.BstSet.insert, hout]
  · have H := insert_loop_mem (k := k) (x := x) s.root out hout
    have : x = k ∨ memAux s.root x := Or.inr hx
    exact (H.mpr this)

end bst_set_spec
end AeneasPlayground
