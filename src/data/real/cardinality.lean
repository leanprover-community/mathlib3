/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import analysis.specific_limits.basic
import data.rat.denumerable
import data.set.intervals.image_preimage
import data.real.binary_fraction
import set_theory.cardinal.continuum


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
open_locale cardinal interval
noncomputable theory

namespace cardinal

instance : has_card_continuum ℝ :=
begin
  refine ⟨le_antisymm _ (continuum_le_mk ℝ)⟩,
  rw mk_congr real.equiv_Cauchy,
  apply mk_quotient_le.trans, apply (mk_subtype_le _).trans,
  simp
end

/-- The cardinality of the reals, as a type. -/
@[simp] lemma mk_real : #ℝ = 𝔠 := mk_eq_continuum ℝ

/-- The cardinality of the reals, as a set. -/
lemma mk_univ_real : #(set.univ : set ℝ) = 𝔠 :=
by rw [mk_univ, mk_real]

/-- **Non-Denumerability of the Continuum**: The reals are not countable. -/
lemma not_countable_real : ¬ countable (set.univ : set ℝ) :=
not_countable_of_continuum_le_mk _ mk_univ_real.ge

/-- The cardinality of the interval (a, b). -/
@[simp] lemma mk_Ioo_real {a b : ℝ} (h : a < b) : #(Ioo a b) = 𝔠 :=
mk_Ioo_eq_continuum h

/-- The cardinality of the interval (a, ∞). -/
lemma mk_Ioi_real (a : ℝ) : #(Ioi a) = 𝔠 :=
mk_Ioi_eq_continuum a

/-- The cardinality of the interval [a, ∞). -/
lemma mk_Ici_real (a : ℝ) : #(Ici a) = 𝔠 :=
mk_Ici_eq_continuum a

/-- The cardinality of the interval (-∞, a). -/
lemma mk_Iio_real (a : ℝ) : #(Iio a) = 𝔠 :=
mk_Iio_eq_continuum a

/-- The cardinality of the interval (-∞, a]. -/
lemma mk_Iic_real (a : ℝ) : #(Iic a) = 𝔠 :=
mk_Iic_eq_continuum a

/-- The cardinality of the interval [a, b). -/
lemma mk_Ico_real {a b : ℝ} (h : a < b) : #(Ico a b) = 𝔠 :=
mk_Ico_eq_continuum h

/-- The cardinality of the interval [a, b]. -/
lemma mk_Icc_real {a b : ℝ} (h : a < b) : #(Icc a b) = 𝔠 :=
mk_Icc_eq_continuum h

/-- The cardinality of the interval (a, b]. -/
lemma mk_Ioc_real {a b : ℝ} (h : a < b) : #(Ioc a b) = 𝔠 :=
mk_Ioc_eq_continuum h

lemma mk_interval_real {a b : ℝ} (h : a ≠ b) : #([a, b]) = 𝔠 :=
mk_Icc_real $ min_lt_max.2 h

lemma mk_interval_oc_real {a b : ℝ} (h : a ≠ b) : #(Ι a b) = 𝔠 :=
mk_Ioc_real $ min_lt_max.2 h

end cardinal
