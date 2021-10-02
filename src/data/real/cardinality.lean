/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import set_theory.continuum
import analysis.specific_limits
import data.rat.denumerable
import data.set.intervals.image_preimage
import data.real.binary_fraction

/-!
# The cardinality of the reals

This file shows that the real numbers have cardinality continuum, i.e. `#ℝ = 𝔠`.

We show that `#ℝ ≤ 𝔠` by noting that every real number is determined by a Cauchy-sequence of the
form `ℕ → ℚ`, which has cardinality `𝔠`. To show that `#ℝ ≥ 𝔠` we define an injection from
`{0, 1} ^ ℕ` to `ℝ` with `f ↦ Σ n, f n * (1 / 3) ^ n`.

We conclude that all intervals with distinct endpoints have cardinality continuum.

## Main definitions

* `cardinal.cantor_function` is the function that sends `f` in `{0, 1} ^ ℕ` to `ℝ` by
  `f ↦ Σ' n, f n * (1 / 3) ^ n`

## Main statements

* `cardinal.mk_real : #ℝ = 𝔠`: the reals have cardinality continuum.
* `cardinal.not_countable_real`: the universal set of real numbers is not countable.
  We can use this same proof to show that all the other sets in this file are not countable.
* 8 lemmas of the form `mk_Ixy_real` for `x,y ∈ {i,o,c}` state that intervals on the reals
  have cardinality continuum.

## Notation

* `𝔠` : notation for `cardinal.continuum` in locale `cardinal`, defined in `set_theory.continuum`.

## Tags
continuum, cardinality, reals, cardinality of the reals
-/

open nat set
open_locale cardinal
noncomputable theory

namespace cardinal

/-- The cardinality of the reals, as a type. -/
@[simp] lemma mk_real : #ℝ = 𝔠 :=
begin
  apply le_antisymm _ (le_mk_of_conditionally_complete_lattice ℝ),
  rw real.equiv_Cauchy.cardinal_eq,
  apply mk_quotient_le.trans, apply (mk_subtype_le _).trans,
  rw [←power_def, mk_nat, mk_rat, power_self_eq (le_refl _)]
end

/-- The cardinality of the reals, as a set. -/
lemma mk_univ_real : #(set.univ : set ℝ) = 𝔠 :=
by rw [mk_univ, mk_real]

/-- **Non-Denumerability of the Continuum**: The reals are not countable. -/
lemma not_countable_real : ¬ countable (set.univ : set ℝ) :=
not_countable_of_mk_eq_two_pow_omega _ mk_univ_real

/-- The cardinality of the interval (a, b). -/
@[simp] lemma mk_Ioo_real {a b : ℝ} (h : a < b) : #(Ioo a b) = 2 ^ omega.{0} :=
le_antisymm (mk_real ▸ mk_set_le _) $ le_mk_Ioo h

/-- The cardinality of the interval (a, ∞). -/
lemma mk_Ioi_real (a : ℝ) : #(Ioi a) = 2 ^ omega.{0} :=
le_antisymm (mk_real ▸ mk_set_le _) $
  mk_Ioo_real (lt_add_one a) ▸ mk_le_mk_of_subset Ioo_subset_Ioi_self

/-- The cardinality of the interval [a, ∞). -/
lemma mk_Ici_real (a : ℝ) : #(Ici a) = 𝔠 :=
le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioi_real a ▸ mk_le_mk_of_subset Ioi_subset_Ici_self)

/-- The cardinality of the interval (-∞, a). -/
lemma mk_Iio_real (a : ℝ) : #(Iio a) = 𝔠 :=
begin
  refine le_antisymm (mk_real ▸ mk_set_le _) _,
  have h2 : (λ x, a + a - x) '' Iio a = Ioi a,
  { convert image_const_sub_Iio _ _, simp },
  exact mk_Ioi_real a ▸ h2 ▸ mk_image_le
end

/-- The cardinality of the interval (-∞, a]. -/
lemma mk_Iic_real (a : ℝ) : #(Iic a) = 𝔠 :=
le_antisymm (mk_real ▸ mk_set_le _) (mk_Iio_real a ▸ mk_le_mk_of_subset Iio_subset_Iic_self)

/-- The cardinality of the interval [a, b). -/
lemma mk_Ico_real {a b : ℝ} (h : a < b) : #(Ico a b) = 𝔠 :=
le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ico_self)

/-- The cardinality of the interval [a, b]. -/
lemma mk_Icc_real {a b : ℝ} (h : a < b) : #(Icc a b) = 𝔠 :=
le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Icc_self)

/-- The cardinality of the interval (a, b]. -/
lemma mk_Ioc_real {a b : ℝ} (h : a < b) : #(Ioc a b) = 𝔠 :=
le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ioc_self)

end cardinal
