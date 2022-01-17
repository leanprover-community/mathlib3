/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import order.succ_pred.basic
/-!
# Relations on types with a `succ_order`

This file contains properties about relations on types with a `succ_order`
and their closure operations (like the transitive closure).
-/

open set relation succ_order function

variables {α : Type*} [linear_order α] [succ_order α] [is_succ_archimedean α] [no_max_order α]
/-- `(n, m)` is in the reflexive-transitive closure of `~` if `i ~ i+1` and `i+1 ~ i`
  for all `i` between `n` and `m`. -/
lemma refl_trans_gen_of_succ (r : α → α → Prop) {n m : α}
  (h1 : ∀ i ∈ Ico n m, r i (succ i)) (h2 : ∀ i ∈ Ico m n, r (succ i) i) : refl_trans_gen r n m :=
begin
  cases le_total n m with hnm hmn,
  { revert h1 h2,
    refine le_succ_rec _ _ hnm,
    { intros h1 h2, exact refl_trans_gen.refl },
    { intros m hnm ih h1 h2,
      refine refl_trans_gen.tail (ih _ _) (h1 m _),
      { intros i hi, exact h1 i ⟨hi.1, hi.2.trans $ lt_succ m⟩ },
      { simp [Ico_eq_empty_of_le (show n ≤ m, from hnm)] },
      { refine ⟨hnm, lt_succ m⟩ } }, },
  { revert h1 h2,
    refine le_succ_rec _ _ hmn,
    { intros h1 h2, exact refl_trans_gen.refl },
    { intros n hmn ih h1 h2,
      refine refl_trans_gen.head (h2 n _) (ih _ _),
      { refine ⟨hmn, lt_succ n⟩ },
      { simp [Ico_eq_empty_of_le (show m ≤ n, from hmn)] },
      { intros i hi, exact h2 i ⟨hi.1, hi.2.trans $ lt_succ n⟩ } } }
end

/-- `(n, m)` is in the transitive closure of a relation `~` for `n ≠ m` if `i ~ i+1` and `i+1 ~ i`
  for all `i` between `n` and `m`. -/
lemma trans_gen_of_succ_of_ne (r : α → α → Prop) {n m : α}
  (h1 : ∀ i ∈ Ico n m, r i (succ i)) (h2 : ∀ i ∈ Ico m n, r (succ i) i)
  (hnm : n ≠ m) : trans_gen r n m :=
(refl_trans_gen_iff_eq_or_trans_gen.mp (refl_trans_gen_of_succ r h1 h2)).resolve_left hnm.symm

/-- `(n, m)` is in the transitive closure of a reflexive relation `~` if `i ~ i+1` and `i+1 ~ i`
  for all `i` between `n` and `m`. -/
lemma trans_gen_of_succ_of_reflexive (r : α → α → Prop) {n m : α} (hr : reflexive r)
  (h1 : ∀ i ∈ Ico n m, r i (succ i)) (h2 : ∀ i ∈ Ico m n, r (succ i) i) : trans_gen r n m :=
begin
  rcases eq_or_ne m n with rfl|hmn, { exact trans_gen.single (hr m) },
  exact trans_gen_of_succ_of_ne r h1 h2 hmn.symm
end
