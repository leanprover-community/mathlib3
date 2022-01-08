/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import data.nat.basic
import logic.relation
/-!
# Relations on `ℕ`

This file contains properties about relations on `ℕ` and their closure operations
(like the transitive closure).
-/

open set nat

namespace relation

/-- `(n, m)` is in the reflexive-transitive closure of `~` if `i ~ i+1` and `i+1 ~ i`
  for all `i` between `n` and `m`. -/
lemma refl_trans_gen_nat (r : ℕ → ℕ → Prop) {n m : ℕ}
  (h1 : ∀ i ∈ Ico n m, r i i.succ) (h2 : ∀ i ∈ Ico m n, r (i : ℕ).succ i) : refl_trans_gen r n m :=
begin
  cases le_total n m with hnm hmn,
  { induction hnm with m hnm ih,
    { exact refl_trans_gen.refl },
    { refine refl_trans_gen.tail (ih _ _) (h1 m _),
      { intros i hi, exact h1 i ⟨hi.1, hi.2.step⟩ },
      { simp [Ico_eq_empty_of_le (show n ≤ m, from hnm)] },
      { refine ⟨hnm, lt_add_one m⟩ } } },
  { induction hmn with n hmn ih,
    { exact refl_trans_gen.refl },
    { refine refl_trans_gen.head (h2 n _) (ih _ _),
      { refine ⟨hmn, lt_add_one n⟩ },
      { simp [Ico_eq_empty_of_le (show m ≤ n, from hmn)] },
      { intros i hi, exact h2 i ⟨hi.1, hi.2.step⟩ } } }
end

/-- `(n, m)` is in the transitive closure of a relation `~` for `n ≠ m` if `i ~ i+1` and `i+1 ~ i`
  for all `i` between `n` and `m`. -/
lemma trans_gen_nat_of_ne (r : ℕ → ℕ → Prop) {n m : ℕ}
  (h1 : ∀ i ∈ Ico n m, r i i.succ) (h2 : ∀ i ∈ Ico m n, r (i : ℕ).succ i)
  (hnm : n ≠ m) : trans_gen r n m :=
(refl_trans_gen_iff_eq_or_trans_gen.mp (refl_trans_gen_nat r h1 h2)).resolve_left hnm.symm

/-- `(n, m)` is in the transitive closure of a reflexive relation `~` if `i ~ i+1` and `i+1 ~ i`
  for all `i` between `n` and `m`. -/
lemma trans_gen_nat_of_reflexive (r : ℕ → ℕ → Prop) {n m : ℕ} (hr : reflexive r)
  (h1 : ∀ i ∈ Ico n m, r i i.succ) (h2 : ∀ i ∈ Ico m n, r (i : ℕ).succ i) : trans_gen r n m :=
begin
  rcases eq_or_ne m n with rfl|hmn, { exact trans_gen.single (hr m) },
  exact trans_gen_nat_of_ne r h1 h2 hmn.symm
end

end relation
