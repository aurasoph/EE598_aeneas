import AeneasPlayground.Queue_Def
import AeneasPlayground.Gen.Queue

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000

namespace AeneasPlayground
namespace queue_spec

open queue

-- Correctness lemmas for list helpers.

/--
Correctness of the extracted list `push_front` with respect to the abstraction `toList`.
-/
theorem list_push_front_correct (xs : queue.List) (x : Std.I32) :
    ∃ ys, queue.List.push_front xs x = ok ys ∧
      toList ys = x :: toList xs := by
  refine ⟨{ head := some (queue.Node.mk x xs.head) }, ?_, ?_⟩
  · simp [queue.List.push_front]
  · simp [toList]

/--
Correctness of the extracted list `pop_front` with respect to `toList`.

If the list is empty, it returns `none` and leaves the list empty.
Otherwise it returns the head element together with the tail list.
-/
theorem list_pop_front_correct (xs : queue.List) :
    ∃ (o : Option Std.I32) (ys : queue.List),
      queue.List.pop_front xs = ok (o, ys) ∧
        match o with
        | none =>
            toList xs = [] ∧ toList ys = []
        | some v =>
            toList xs = v :: toList ys := by
  cases h : xs.head with
  | none =>
      refine ⟨none, { head := none }, ?_, ?_⟩
      · simp [queue.List.pop_front, h]
      · simp [toList, h]
  | some n =>
      cases n with
      | mk x nxt =>
          refine ⟨some x, { head := nxt }, ?_, ?_⟩
          · simp [queue.List.pop_front, h]
          · simp [toList, h]

-- Correctness of `reverse_into`.

/--
Specification for `reverse_into`.

`reverse_into self other` transfers all elements from `self` into `other` by
repeatedly popping from the front of `self` and pushing to the front of `other`.

At the level of `toList`:
- the returned `self'` is empty
- the returned `other'` equals `(toList self).reverse ++ toList other`
-/
theorem reverse_into_correct (self other : queue.List) :
    ∃ self' other',
      queue.List.reverse_into self other = ok (self', other') ∧
        toList self' = [] ∧
        toList other' = (toList self).reverse ++ toList other := by
  sorry

-- Queue-level correctness lemmas.

/--
Correctness of `enqueue` with respect to the abstraction `toQ`.
-/
theorem enqueue_correct (q : queue.Queue) (x : Std.I32) :
    ∃ q', queue.Queue.enqueue q x = ok q' ∧
      toQ q' = toQ q ++ [x] := by
  rcases list_push_front_correct q.back x with ⟨b', hb, hbabs⟩
  refine ⟨{ q with back := b' }, ?_, ?_⟩
  · simp [queue.Queue.enqueue, hb]
  · simp [toQ, hbabs, _root_.List.reverse_cons, _root_.List.append_assoc]

/--
Correctness of `Queue.is_empty` with respect to `toQ`.

The extracted implementation checks `front` first; if `front` is empty it checks
`back`, otherwise it returns `false`. The statement relates the returned boolean
to emptiness of the abstract queue contents.
-/
theorem queue_is_empty_correct (q : queue.Queue) :
    ∃ b, queue.Queue.is_empty q = ok b ∧ (b = true ↔ toQ q = []) := by
  refine ⟨(if q.front.head = none then q.back.head.isNone else false), ?_, ?_⟩
  ·
    cases hf : q.front.head with
    | none =>
        simp [queue.Queue.is_empty, queue.List.is_empty, hf]
    | some n =>
        simp [queue.Queue.is_empty, queue.List.is_empty, hf]
  ·
    case refine_2 =>
      cases hf : q.front.head with
      | none =>
          cases hb : q.back.head with
          | none =>
              simp [toQ, toList, hf, hb]
          | some n =>
              have hn : toListAux (some n) ≠ [] := toListAux_some_ne_nil n
              have htoq : toQ q ≠ [] := by
                intro hqnil
                have hrev : (toList q.back).reverse = [] := by
                  simpa [toQ, toList, hf] using hqnil
                have hrev2 := congrArg _root_.List.reverse hrev
                have hbackNil : toList q.back = [] := by
                  simpa using hrev2
                have : toListAux (some n) = [] := by
                  simpa [toList, hb] using hbackNil
                exact hn this
              simp_all only [ne_eq, ↓reduceIte, Option.isNone_some, Bool.false_eq_true]
      | some n =>
          have hn : toListAux (some n) ≠ [] := toListAux_some_ne_nil n
          have htoq : toQ q ≠ [] := by
            intro hqnil
            have happ : toList q.front ++ (toList q.back).reverse = [] := by
              simpa [toQ] using hqnil
            have hfrontNil : toList q.front = [] := by simp_all only [ne_eq, List.append_eq_nil_iff,
              List.reverse_eq_nil_iff]
            have : toListAux (some n) = [] := by
              simpa [toList, hf] using hfrontNil
            exact hn this
          simp_all only [ne_eq, reduceCtorEq, ↓reduceIte, Bool.false_eq_true]

end queue_spec
end AeneasPlayground
