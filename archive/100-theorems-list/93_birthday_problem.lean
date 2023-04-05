/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import data.fintype.card_embedding
import probability.cond_count
import probability.notation

/-!
# Birthday Problem

This file proves Theorem 93 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

As opposed to the standard probabilistic statement, we instead state the birthday problem
in terms of injective functions. The general result about `fintype.card (α ↪ β)` which this proof
uses is `fintype.card_embedding_eq`.
-/

local notation (name := finset.card)  `|` x `|` := finset.card x
local notation (name := fintype.card) `‖` x `‖` := fintype.card x

/-- **Birthday Problem**: set cardinality interpretation. -/
theorem birthday :
  2 * ‖fin 23 ↪ fin 365‖ < ‖fin 23 → fin 365‖ ∧ 2 * ‖fin 22 ↪ fin 365‖ > ‖fin 22 → fin 365‖ :=
begin
  simp only [nat.desc_factorial, fintype.card_fin, fintype.card_embedding_eq, fintype.card_fun],
  norm_num
end

section measure_theory

open measure_theory probability_theory
open_locale probability_theory ennreal

variables {n m : ℕ}

/- In order for Lean to understand that we can take probabilities in `fin 23 → fin 365`, we must
tell Lean that there is a `measurable_space` structure on the space. Note that this instance
is only for `fin m` - Lean automatically figures out that the function space `fin n → fin m`
is _also_ measurable, by using `measurable_space.pi`, and furthermore that all sets are measurable,
from `measurable_singleton_class.pi`. -/
instance : measurable_space (fin m) := ⊤
instance : measurable_singleton_class (fin m) := ⟨λ _, trivial⟩

/- We then endow the space with a canonical measure, which is called ℙ.
We define this to be the conditional counting measure. -/
noncomputable instance : measure_space (fin n → fin m) := ⟨cond_count set.univ⟩

/- The canonical measure on `fin n → fin m` is a probability measure (except on an empty space). -/
instance : is_probability_measure (ℙ : measure (fin n → fin (m + 1))) :=
cond_count_is_probability_measure set.finite_univ set.univ_nonempty

lemma fin_fin.measure_apply {s : set $ fin n → fin m} :
  ℙ s = (|s.to_finite.to_finset|) / ‖fin n → fin m‖ :=
by erw [cond_count_univ, measure.count_apply_finite]

/-- **Birthday Problem**: first probabilistic interpretation. -/
theorem birthday_measure : ℙ {f : fin 23 → fin 365 | function.injective f} < 1 / 2 :=
begin
  -- most of this proof is essentially converting it to the same form as `birthday`.
  rw [fin_fin.measure_apply],
  generalize_proofs hfin,
  have : |hfin.to_finset| = 42200819302092359872395663074908957253749760700776448000000,
  { transitivity ‖fin 23 ↪ fin 365‖,
    { simp_rw [←fintype.card_coe, set.finite.coe_sort_to_finset, set.coe_set_of],
      exact fintype.card_congr (equiv.subtype_injective_equiv_embedding _ _) },
    { simp only [fintype.card_embedding_eq, fintype.card_fin, nat.desc_factorial],
      norm_num } },
  rw [this, ennreal.lt_div_iff_mul_lt, mul_comm, mul_div, ennreal.div_lt_iff],
  rotate, iterate 2 { right, norm_num }, iterate 2 { left, norm_num },
  norm_cast,
  simp only [fintype.card_pi, fintype.card_fin],
  norm_num
end

end measure_theory
