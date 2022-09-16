/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import data.fintype.card_embedding
import probability.notation
import tactic.norm_num

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

open measure_theory
open_locale probability_theory ennreal

variables {n m : ℕ}

/- In order for Lean to understand that we can take probabilities in `fin 23 → fin 365`, we must
tell Lean that there is a `measurable_space` structure on the space. Note that this instance
is only for `fin m` - Lean automatically figures out that the function space `fin n → fin m`
is _also_ measurable, by using `measurable_space.pi` -/

instance : measurable_space (fin m) :=
{ measurable_set' := λ _, true,
  measurable_set_empty := trivial,
  measurable_set_compl := λ _ _, trivial,
  measurable_set_Union := λ _ _, trivial }

/- We then endow the space with a canonical measure, which is called ℙ. We define this to be
the counting measure, scaled by the size of the whole set. -/
noncomputable instance : measure_space (fin n → fin m) :=
  ⟨(measure.count (set.univ : set $ fin n → fin m))⁻¹ • measure.count⟩

-- Singletons are measurable; therefore, as `fin n → fin m` is finite, all sets are measurable.
instance : measurable_singleton_class (fin n → fin m) :=
⟨λ f, begin
  convert measurable_set.pi set.finite_univ.countable
    (show ∀ i, i ∈ set.univ → measurable_set ({f i} : set (fin m)), from λ _ _, trivial),
  ext g,
  simp only [function.funext_iff, set.mem_singleton_iff, set.mem_univ_pi],
end⟩

/- The canonical measure on `fin n → fin m` is a probability measure (except on an empty space). -/
example : is_probability_measure (ℙ : measure (fin n → fin (m + 1))) :=
is_probability_measure_smul
begin
  rw [ne.def, ←measure.measure_univ_eq_zero, measure.count_apply_finite, set.finite_univ_to_finset,
      finset.card_univ, ←ne.def],
  norm_cast,
  exact fintype.card_ne_zero,
  exact set.finite_univ
end

lemma fin_fin.measure_apply {s : set $ fin n → fin m} :
  ℙ s = (|s.to_finite.to_finset|) / ‖fin n → fin m‖ :=
begin
  change _ • measure.count _ = _,
  rw [measure.count_apply_finite, measure.count_apply_finite, smul_eq_mul,
      ←ennreal.div_eq_inv_mul, set.finite_univ_to_finset, finset.card_univ],
  exact set.finite_univ
end

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
