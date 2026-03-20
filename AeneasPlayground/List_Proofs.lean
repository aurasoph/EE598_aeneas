import AeneasPlayground.List_Def
import AeneasPlayground.Gen.List

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000

namespace AeneasPlayground
namespace list_spec

open list

-- push_front and is_empty

/--
`push_front` agrees with the pure abstraction: it conses onto the front.
-/
theorem push_front_correct (xs : list.List) (x : Std.I32) :
    ∃ ys, list.List.push_front xs x = ok ys ∧
      toList ys = x :: toList xs := by
  refine ⟨{ head := some (list.Node.mk x xs.head) }, ?_, ?_⟩
  · grind [list.List.push_front, core.option.Option.take]
  · grind [toList, toListAux]

/--
`is_empty` agrees with the pure abstraction: it returns `true` exactly when the
abstract list is empty.
-/
theorem is_empty_correct (xs : list.List) :
    ∃ b, list.List.is_empty xs = ok b ∧ (b = true ↔ toList xs = []) := by
  refine ⟨core.option.Option.is_none xs.head, ?_, ?_⟩
  · grind [list.List.is_empty]
  · cases h : xs.head with
    | none =>
        simp [toList, h]
    | some n =>
        have hn : toListAux (some n) ≠ [] := toListAux_some_ne_nil n
        simp [toList, h, hn]

-- push_back

/--
Semantic specification for `push_back_loop`.

The loop returns a “rebuilding function” `f` such that `f suf` reconstructs the
original spine `cur` followed by the suffix `suf`, at the level of `toListAux`.
-/
theorem push_back_loop_spec :
    ∀ cur : Option list.Node,
      ∃ f, list.List.push_back_loop cur = ok f ∧
        (∀ suf : Option list.Node,
          toListAux (f suf) = toListAux cur ++ toListAux suf)
  | none => by
      refine ⟨(fun o => o), ?_, ?_⟩
      · grind [list.List.push_back_loop]
      · intro suf
        grind [toListAux]
  | some n => by
      cases n with
      | mk x nxt =>
          rcases push_back_loop_spec nxt with ⟨back, hback, hsem⟩
          refine ⟨(fun suf => some (list.Node.mk x (back suf))), ?_, ?_⟩
          · simp [list.List.push_back_loop, hback]
          · intro suf
            simp [hsem, _root_.List.cons_append]

/--
`push_back` agrees with the pure abstraction: it appends a singleton at the end.
-/
theorem push_back_correct (xs : list.List) (x : Std.I32) :
    ∃ ys, list.List.push_back xs x = ok ys ∧
      toList ys = toList xs ++ [x] := by
  rcases push_back_loop_spec xs.head with ⟨back, hback, hsem⟩
  let suf : Option list.Node := some (list.Node.mk x none)
  let ys : list.List := { head := back suf }
  refine ⟨ys, ?_, ?_⟩
  · simp [list.List.push_back, ys, suf, hback]
  · have hsuf : toListAux suf = [x] := by
      simp [suf]
    simp [toList, ys, hsem, hsuf]

-- append

/--
Semantic specification for `append_loop`.

The loop returns the reconstructed spine corresponding to `cur` with `other`
appended at the end, at the level of `toListAux`.
-/
theorem append_loop_spec :
    ∀ (other : list.List) (cur : Option list.Node),
      ∃ out, list.List.append_loop other cur = ok out ∧
        toListAux out = toListAux cur ++ toList other
  | other, none => by
      refine ⟨other.head, ?_, ?_⟩
      · grind [list.List.append_loop, core.option.Option.take]
      · grind [toList, toListAux]
  | other, some n => by
      cases n with
      | mk x nxt =>
          cases hnxt : nxt with
          | none =>
              refine ⟨some (list.Node.mk x other.head), ?_, ?_⟩
              · simp [list.List.append_loop, core.option.Option.take]
              · simp [toList, _root_.List.cons_append]
          | some nxtNode =>
              rcases append_loop_spec other (some nxtNode) with ⟨out, hout, hsem⟩
              refine ⟨some (list.Node.mk x out), ?_, ?_⟩
              · simp [list.List.append_loop, hout]
              · simp [hsem, _root_.List.cons_append]

/--
`append` agrees with the pure abstraction: it concatenates abstract lists.
-/
theorem append_correct (xs ys : list.List) :
    ∃ zs, list.List.append xs ys = ok zs ∧
      toList zs = toList xs ++ toList ys := by
  cases hx : xs.head with
  | none =>
      refine ⟨{ head := ys.head }, ?_, ?_⟩
      · simp [list.List.append, hx, core.option.Option.take]
      · simp [toList, hx]
  | some n =>
      rcases append_loop_spec ys (some n) with ⟨out, hout, hsem⟩
      refine ⟨{ head := out }, ?_, ?_⟩
      · simp [list.List.append, hx, hout]
      · simp [toList, hx, hsem]

-- reverse_iter (via reverse_iter_loop)

/--
Accumulator specification for `reverse_iter_loop`.

If `reverse_iter_loop prev cur` returns `out`, then `out` represents the abstract
list `reverse (toListAux cur) ++ toListAux prev`.
-/
theorem reverse_iter_loop_spec :
    ∀ (prev cur : Option list.Node),
      ∃ out, list.List.reverse_iter_loop prev cur = ok out ∧
        toListAux out = (toListAux cur).reverse ++ toListAux prev := by
  intro prev cur
  let body :
      (Option list.Node × Option list.Node) →
        Result (Aeneas.Std.ControlFlow
          (Option list.Node × Option list.Node)
          (Option list.Node)) :=
    fun s =>
      match s.2 with
      | none => ok (done s.1)
      | some node =>
        let (next, _) := core.option.Option.take node.next
        ok (cont (some (list.Node.mk node.elem s.1), next))

  cases cur with
  | none =>
      refine ⟨prev, ?_, ?_⟩
      · simp only [list.List.reverse_iter_loop]
        unfold Aeneas.Std.loop
        simp
      · simp
  | some n =>
      cases n with
      | mk x nxt =>
          have ih :=
            reverse_iter_loop_spec
              (prev := some (list.Node.mk x prev))
              (cur := nxt)
          rcases ih with ⟨out, hout, hsem⟩
          refine ⟨out, ?_, ?_⟩
          ·
            have hout_loop :
                loop body (some (list.Node.mk x prev), nxt) = ok out := by
              simpa [list.List.reverse_iter_loop, body] using hout
            simp only [list.List.reverse_iter_loop]
            unfold Aeneas.Std.loop
            simp only
              [core.option.Option.take,
               list.Node.elem._simpLemma_,
               list.Node.next._simpLemma_]
            exact hout_loop
          ·
            simpa
              [toListAux,
               _root_.List.reverse_cons,
               _root_.List.append_assoc,
               _root_.List.cons_append]
              using hsem
termination_by
  prev cur => sizeOf cur

/--
`reverse_iter` agrees with the pure abstraction: it reverses the abstract list.
-/
theorem reverse_iter_correct (xs : list.List) :
    ∃ ys, list.List.reverse_iter xs = ok ys ∧
      toList ys = (toList xs).reverse := by
  rcases reverse_iter_loop_spec (prev := none) (cur := xs.head) with ⟨out, hout, hsem⟩
  refine ⟨{ head := out }, ?_, ?_⟩
  · simp [list.List.reverse_iter, hout]
  · simpa [toList, toListAux] using hsem

-- pop_front

/--
`pop_front` agrees with the pure abstraction.

It returns `none` exactly on an empty list (and leaves the list empty), and
returns `some v` together with the tail otherwise.
-/
theorem pop_front_correct (xs : list.List) :
    ∃ (o : Option Std.I32) (ys : list.List),
      list.List.pop_front xs = ok (o, ys) ∧
        match o with
        | none =>
            toList xs = [] ∧ toList ys = []
        | some v =>
            toList xs = v :: toList ys := by
  cases h : xs.head with
  | none =>
      refine ⟨none, { head := none }, ?_, ?_⟩
      · grind [list.List.pop_front, core.option.Option.take]
      · grind [toList, toListAux]
  | some n =>
      cases n with
      | mk x nxt =>
          refine ⟨some x, { head := nxt }, ?_, ?_⟩
          · simp [list.List.pop_front, h, core.option.Option.take]
          · simp [toList, h]

-- len (relative to Option.as_ref)

/-- Result-valued “add 1#usize, k times, starting from n”. -/
def usizeAddNatR (n : Std.Usize) : Nat → Result Std.Usize
  | 0 => ok n
  | Nat.succ k => do
      let n2 ← n + 1#usize
      usizeAddNatR n2 k

/-- Result-valued conversion `Nat → Usize` (starting from 0). -/
def usizeOfNatR (k : Nat) : Result Std.Usize :=
  usizeAddNatR 0#usize k

/--
`len_loop` correctness, relative to the behavior of `Option.as_ref`.

The hypothesis `H` expresses the intended semantics of the extracted axiom:
`as_ref` returns its input unchanged.
-/
theorem len_loop_correct_relative
  (H : ∀ o : Option list.Node, list.core.option.Option.as_ref o = ok o) :
  ∀ (n : Std.Usize) (cur : Option list.Node),
    list.List.len_loop n cur = usizeAddNatR n (toListAux cur).length := by
  intro n cur
  let body :
      (Std.Usize × Option list.Node) →
        Result (ControlFlow (Std.Usize × Option list.Node) Std.Usize) :=
    fun s =>
      match s.2 with
      | none => ok (done s.1)
      | some node => do
          let n2 ← s.1 + 1#usize
          let cur2 ← list.core.option.Option.as_ref node.next
          ok (cont (n2, cur2))
  cases cur with
  | none =>
      simp only [toListAux_none, List.length_nil, usizeAddNatR]
      simp only [list.List.len_loop]
      unfold Aeneas.Std.loop
      simp
  | some node =>
      cases node with
      | mk x nxt =>
          have href : list.core.option.Option.as_ref nxt = ok nxt := H nxt
          simp only [list.List.len_loop]
          unfold Aeneas.Std.loop
          simp [href]
          cases hplus : (n + 1#usize) with
          | ok n2 =>
              simp [usizeAddNatR, hplus]
              simpa [list.List.len_loop, body] using (len_loop_correct_relative (H := H) n2 nxt)
          | fail e =>
              simp [usizeAddNatR, hplus]
          | div =>
              simp [usizeAddNatR, hplus]
/--
`len` correctness, relative to the behavior of `Option.as_ref`.

Under the same hypothesis as `len_loop_correct_relative`, the extracted `len`
computes the length of the abstract list (returned as a `Result Usize`).
-/
theorem len_correct_relative
  (H : ∀ o : Option list.Node, list.core.option.Option.as_ref o = ok o)
  (xs : list.List) :
  list.List.len xs = usizeOfNatR (toList xs).length := by
  have href : list.core.option.Option.as_ref xs.head = ok xs.head := H xs.head
  simp [list.List.len, href, usizeOfNatR, toList]
  simpa using (len_loop_correct_relative H 0#usize xs.head)

end list_spec
end AeneasPlayground
