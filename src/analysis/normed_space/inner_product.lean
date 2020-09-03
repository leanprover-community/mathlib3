/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import algebra.quadratic_discriminant
import analysis.special_functions.pow
import topology.metric_space.pi_Lp
import data.complex.is_R_or_C

/-!
# Inner Product Space

This file defines inner product spaces and proves its basic properties.

An inner product space is a vector space endowed with an inner product `⟪·, ·⟫` which
satisfies `⟪x, y⟫ = conj ⟪y, x⟫`.

## Main results

- We define the class `inner_product_space` with a number of basic properties, most
  notably the Cauchy-Schwarz inequality.
- We show that if `f i` is an inner product space for each `i`, then so is `Π i, f i`
- We define `euclidean_space K n` to be `n → K` for any `fintype n`, and show that
  this an inner product space.

## Notation

We locally denote the inner product by `⟪·, ·⟫`.

## Implementation notes

We define both the real and complex cases at the same time using the `is_R_of_C` typeclass.

## Tags

inner product space, norm
-/

noncomputable theory

namespace is_R_or_C

open is_R_or_C real set -- vector_space finite_dimensional submodule module
open_locale big_operators
open_locale topological_space

variables {α : Type*} {F : Type*} {G : Type*}
variables {K : Type*} [nondiscrete_normed_field K] [algebra ℝ K] [is_R_or_C K]
local notation `𝓚` := @is_R_or_C.of_real K _ _ _


class has_inner (K α : Type*) := (inner : α → α → K)

export has_inner (inner)

section prio

set_option default_priority 100 -- see Note [default priority]
-- see Note[vector space definition] for why we extend `semimodule`.
/--
An inner product space is a vector space with an additional operation called inner product.
The norm could be derived from the inner product, instead we require the existence of a norm and
the fact that `∥x∥^2 = re ⟪x, x⟫` to be able to put instances on `K` or product
spaces.

To construct a norm from an inner product, see `inner_product_space.of_core`.
-/
class inner_product_space (K : Type*) (α : Type*)
  [nondiscrete_normed_field K] [algebra ℝ K] [is_R_or_C K]
  extends normed_group α, normed_space K α, has_inner K α :=
(norm_sq_eq_inner : ∀ (x : α), ∥x∥^2 = re (inner x x))
(conj_sym  : ∀ x y, conj (inner y x) = inner x y)
(nonneg_im : ∀ x, im (inner x x) = 0)
(add_left  : ∀ x y z, inner (x + y) z = inner x z + inner y z)
(smul_left : ∀ x y r, inner (r • x) y = (conj r) * inner x y)

end prio

/-!
### Constructing a normed space structure from a scalar product

In the definition of an inner product space, we require the existence of a norm, which is equal
(but maybe not defeq) to the square root of the scalar product. This makes it possible to put
an inner product space structure on spaces with a preexisting norm (for instance `ℝ`), with good
properties. However, sometimes, one would like to define the norm starting only from a well-behaved
scalar product. This is what we implement in this paragraph, starting from a structure
`inner_product_space.core` stating that we have a nice scalar product.

Our goal here is not to develop a whole theory with all the supporting API, as this will be done
below for `inner_product_space`. Instead, we implement the bare minimum to go as directly as
possible to the construction of the norm and the proof of the triangular inequality.
-/

/-- A structure requiring that a scalar product is positive definite and symmetric, from which one
can construct an `inner_product_space` instance in `inner_product_space.of_core`. -/
@[nolint has_inhabited_instance]
structure inner_product_space.core
  (K : Type*) (F : Type*)
  [nondiscrete_normed_field K] [algebra ℝ K] [is_R_or_C K]
  [add_comm_group F] [semimodule K F] :=
(inner     : F → F → K)
(conj_sym  : ∀ x y, conj (inner y x) = inner x y)
(nonneg_im : ∀ x, im (inner x x) = 0)
(nonneg_re : ∀ x, re (inner x x) ≥ 0)
(definite  : ∀ x, inner x x = 0 → x = 0)
(add_left  : ∀ x y z, inner (x + y) z = inner x z + inner y z)
(smul_left : ∀ x y r, inner (r • x) y = (conj r) * inner x y)

/- We set `inner_product_space.core` to be a class as we will use it as such in the construction
of the normed space structure that it produces. However, all the instances we will use will be
local to this proof. -/
attribute [class] inner_product_space.core

namespace inner_product_space.of_core

variables [add_comm_group F] [semimodule K F] [c : inner_product_space.core K F]
include c

local notation `⟪`x`, `y`⟫` := @inner K F _ x y
local notation `𝓚` := @is_R_or_C.of_real K _ _ _
local notation `norm_sqK` := @is_R_or_C.norm_sq K _ _ _
local notation `reK` := @is_R_or_C.re K _ _ _
local notation `ext_iff` := @is_R_or_C.ext_iff K _ _ _
local postfix `†`:90 := @is_R_or_C.conj K _ _ _

/-- Inner product defined by the `inner_product_space.core` structure. -/
def to_has_inner : has_inner K F := { inner := c.inner }
local attribute [instance] to_has_inner

/-- The norm squared function for inner product spaces. -/
def norm_sq (x : F) := reK ⟪x, x⟫

local notation `norm_sqF` := @norm_sq F K _ _ _ _ _ _

@[simp] lemma inner_conj_sym (x y : F) : ⟪y, x⟫† = ⟪x, y⟫ := c.conj_sym x y

lemma inner_self_nonneg {x : F} : 0 ≤ re ⟪x, x⟫ := c.nonneg_re _

lemma inner_self_nonneg_im {x : F} : im ⟪x, x⟫ = 0 := c.nonneg_im _

lemma inner_self_im_zero {x : F} : im ⟪x, x⟫ = 0 := c.nonneg_im _

lemma inner_add_left {x y z : F} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
c.add_left _ _ _

lemma inner_add_right {x y z : F} : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ :=
by rw [←inner_conj_sym, inner_add_left, ring_hom.map_add]; simp only [inner_conj_sym]

lemma inner_norm_sq_eq_inner_self_re (x : F) : norm_sqF x = re ⟪x, x⟫ := rfl

lemma inner_norm_sq_eq_inner_self (x : F) : 𝓚 (norm_sqF x) = ⟪x, x⟫ :=
begin
  rw ext_iff,
  exact ⟨by simp only [of_real_re]; refl, by simp only [inner_self_nonneg_im, of_real_im]⟩
end

lemma inner_re_symm {x y : F} : re ⟪x, y⟫ = re ⟪y, x⟫ :=
by rw [←inner_conj_sym, conj_re]

lemma inner_im_symm {x y : F} : im ⟪x, y⟫ = -im ⟪y, x⟫ :=
by rw [←inner_conj_sym, conj_im]

lemma inner_smul_left {x y : F} {r : K} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
c.smul_left _ _ _

lemma inner_smul_right {x y : F} {r : K} : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_smul_left]; simp only [conj_conj, inner_conj_sym, ring_hom.map_mul]

@[simp] lemma inner_zero_left {x : F} : ⟪0, x⟫ = 0 :=
by rw [←zero_smul K (0 : F), inner_smul_left]; simp only [zero_mul, ring_hom.map_zero]

lemma inner_re_zero_left {x : F} : re ⟪0, x⟫ = 0 := by simp

@[simp] lemma inner_zero_right {x : F} : ⟪x, 0⟫ = 0 :=
by rw [←inner_conj_sym, inner_zero_left]; simp only [ring_hom.map_zero]

lemma inner_re_zero_right {x : F} : re ⟪x, 0⟫ = 0 :=
by simp only [inner_zero_right, add_monoid_hom.map_zero]

@[simp] lemma inner_self_eq_zero {x : F} : ⟪x, x⟫ = 0 ↔ x = 0 :=
iff.intro (c.definite _) (by { rintro rfl, exact inner_zero_left })

@[simp] lemma inner_self_nonpos {x : F} : re ⟪x, x⟫ ≤ 0 ↔ x = 0 :=
begin
  split,
  { intro h,
    apply (@inner_self_eq_zero F K _ _ _ _ _ _ x).mp,
    have H₁ : re ⟪x, x⟫ ≥ 0, exact inner_self_nonneg,
    have H₂ : re ⟪x, x⟫ = 0, exact le_antisymm h H₁,
    rw [ext_iff],
    split,
    { simp only [H₂, add_monoid_hom.map_zero] },
    { simp [inner_self_im_zero] } },
  { intro h,
    simp only [h, inner_zero_left, add_monoid_hom.map_zero] }
end

lemma inner_symm_re {x y : F} : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [←inner_conj_sym, conj_re]

@[simp] lemma inner_self_re_to_K {x : F} : 𝓚 (re ⟪x, x⟫) = ⟪x, x⟫ :=
by norm_num [ext_iff, inner_self_nonneg_im]

lemma inner_self_re_abs {x : F} : re ⟪x, x⟫ = abs ⟪x, x⟫ :=
begin
  have H : ⟪x, x⟫ = 𝓚 (re ⟪x, x⟫) + 𝓚 (im ⟪x, x⟫) * I,
  { rw re_add_im, },
  rw [H, is_add_hom.map_add re (𝓚 (re ⟪x, x⟫)) ((𝓚 (im ⟪x, x⟫)) * I)],
  rw [mul_re, I_re, mul_zero, I_im, zero_sub, tactic.ring.add_neg_eq_sub],
  rw [of_real_re, of_real_im, sub_zero, inner_self_nonneg_im],
  simp only [abs_of_real, add_zero, of_real_zero, zero_mul],
  exact (_root_.abs_of_nonneg inner_self_nonneg).symm,
end

lemma inner_self_abs_to_K {x : F} : 𝓚 (abs ⟪x, x⟫) = ⟪x, x⟫ :=
  by { rw[←inner_self_re_abs], exact inner_self_re_to_K }

lemma inner_abs_conj_sym {x y : F} : abs ⟪x, y⟫ = abs ⟪y, x⟫ :=
  by rw [←inner_conj_sym, abs_conj]

@[simp] lemma inner_neg_left {x y : F} : ⟪-x, y⟫ = -⟪x, y⟫ :=
by { rw [← neg_one_smul K x, inner_smul_left], simp }

@[simp] lemma inner_neg_right {x y : F} : ⟪x, -y⟫ = -⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_neg_left]; simp only [ring_hom.map_neg, inner_conj_sym]

lemma inner_neg_neg {x y : F} : ⟪-x, -y⟫ = ⟪x, y⟫ := by simp

@[simp] lemma inner_self_conj {x : F} : ⟪x, x⟫† = ⟪x, x⟫ :=
by rw [ext_iff]; exact ⟨by rw [conj_re], by rw [conj_im, inner_self_im_zero, neg_zero]⟩

lemma inner_sub_left {x y z : F} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_left] }

lemma inner_sub_right {x y z : F} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_right] }

lemma inner_mul_conj_re_abs {x y : F} : re (⟪x, y⟫ * ⟪y, x⟫) = abs (⟪x, y⟫ * ⟪y, x⟫) :=
by { rw[←inner_conj_sym, mul_comm], exact re_eq_abs_of_mul_conj (inner y x), }

/-- Expand `inner (x + y) (x + y)` -/
lemma inner_add_add_self {x y : F} : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_add_left, inner_add_right]; ring

/- Expand `inner (x - y) (x - y)` -/
lemma inner_sub_sub_self {x y : F} : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_sub_left, inner_sub_right]; ring

/- Parallelogram law -/
lemma parallelogram_law {x y : F} :
  ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫) :=
by simp [inner_add_add_self, inner_sub_sub_self, two_mul, sub_eq_add_neg, add_comm, add_left_comm]

/--
Cauchy–Schwarz inequality. This proof follows "Proof 2" on Wikipedia.
We need this for the `core` structure to prove the triangle inequality below when
showing the core is a normed group.
-/
lemma inner_mul_inner_self_le (x y : F) : abs ⟪x, y⟫ * abs ⟪y, x⟫ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
begin
  by_cases hy : y = 0,
  { rw [hy], simp only [abs_zero, inner_zero_left, mul_zero, add_monoid_hom.map_zero] },
  { change y ≠ 0 at hy,
    have hy' : ⟪y, y⟫ ≠ 0 := λ h, by rw [inner_self_eq_zero] at h; exact hy h,
    set T := ⟪y, x⟫ / ⟪y, y⟫ with hT,
    have h₁ : re ⟪y, x⟫ = re ⟪x, y⟫ := inner_re_symm,
    have h₂ : im ⟪y, x⟫ = -im ⟪x, y⟫ := inner_im_symm,
    have h₃ : ⟪y, x⟫ * ⟪x, y⟫ * ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = ⟪y, x⟫ * ⟪x, y⟫ / ⟪y, y⟫,
    { rw [mul_div_assoc],
      have : ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = 1 / ⟪y, y⟫ :=
        by rw [div_mul_eq_div_mul_one_div, div_self hy', one_mul],
      rw [this, div_eq_mul_inv, one_mul, ←div_eq_mul_inv] },
    have h₄ : ⟪y, y⟫ = 𝓚 (re ⟪y, y⟫) := by simp only [inner_self_re_to_K],
    have h₅ : re ⟪y, y⟫ > 0,
    { refine lt_of_le_of_ne inner_self_nonneg _,
      intro H,
      apply hy',
      rw ext_iff,
      exact ⟨by simp [H],by simp [inner_self_nonneg_im]⟩ },
    have h₆ : re ⟪y, y⟫ ≠ 0 := ne_of_gt h₅,
    have hmain := calc
      0   ≤ re ⟪x - T • y, x - T • y⟫
                  : inner_self_nonneg
      ... = re ⟪x, x⟫ - re ⟪T • y, x⟫ - re ⟪x, T • y⟫ + re ⟪T • y, T • y⟫
                  : by simp [inner_sub_sub_self, inner_smul_left, inner_smul_right, h₁, h₂]
      ... = re ⟪x, x⟫ - re (T† * ⟪y, x⟫) - re (T * ⟪x, y⟫) + re (T * T† * ⟪y, y⟫)
                  : by simp [inner_smul_left, inner_smul_right, mul_assoc]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ / ⟪y, y⟫ * ⟪y, x⟫)
                  : by field_simp [-mul_re, hT, conj_div, h₁, h₃]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / ⟪y, y⟫)
                  : by rw [div_mul_eq_mul_div_comm, ←mul_div_assoc]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / 𝓚 (re ⟪y, y⟫))
                  : by conv_lhs { rw [h₄] }
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫
                  : by rw [div_re_of_real]
      ... = re ⟪x, x⟫ - abs (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫
                  : by rw [inner_mul_conj_re_abs]
      ... = re ⟪x, x⟫ - abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫
                  : by rw abs_mul,
    have hmain' : abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫ ≤ re ⟪x, x⟫ := by linarith,
    have := (mul_le_mul_right h₅).mpr hmain',
    rwa [div_mul_cancel (abs ⟪x, y⟫ * abs ⟪y, x⟫) h₆] at this }
end

/-- Norm constructed from a `inner_product_space.core` structure, defined to be the square root
of the scalar product. -/
def to_has_norm : has_norm F :=
{ norm := λ x, sqrt (re ⟪x, x⟫) }

local attribute [instance] to_has_norm


lemma norm_eq_sqrt_inner (x : F) : ∥x∥ = sqrt (re ⟪x, x⟫) := rfl

lemma inner_self_eq_norm_square (x : F) : re ⟪x, x⟫ = ∥x∥ * ∥x∥ :=
  by rw[norm_eq_sqrt_inner, ←sqrt_mul inner_self_nonneg (re ⟪x, x⟫),
        sqrt_mul_self inner_self_nonneg]

lemma sqrt_norm_sq_eq_norm {x : F} : sqrt (norm_sqF x) = ∥x∥ := rfl

/-- Expand the square -/
lemma norm_add_pow_two {x y : F} : ∥x + y∥^2 = ∥x∥^2 + 2 * (re ⟪x, y⟫) + ∥y∥^2 :=
begin
  repeat {rw [pow_two, ←inner_self_eq_norm_square]},
  rw[inner_add_add_self, two_mul],
  simp only [add_assoc, add_left_inj, add_right_inj, add_monoid_hom.map_add],
  rw [←inner_conj_sym, conj_re],
end

/-- Same lemma as above but in a different form -/
lemma norm_add_mul_self {x y : F} : ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + 2 * (re ⟪x, y⟫) + ∥y∥ * ∥y∥ :=
    by { repeat {rw [← pow_two]}, exact norm_add_pow_two }

/-- Expand the square -/
lemma norm_sub_pow_two {x y : F} : ∥x - y∥^2 = ∥x∥^2 - 2 * (re ⟪x, y⟫) + ∥y∥^2 :=
begin
repeat {rw [pow_two, ←inner_self_eq_norm_square]},
rw[inner_sub_sub_self],
calc
  re (⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫)
      = re ⟪x, x⟫ - re ⟪x, y⟫ - re ⟪y, x⟫ + re ⟪y, y⟫  : by simp
  ... = -re ⟪y, x⟫ - re ⟪x, y⟫ + re ⟪x, x⟫ + re ⟪y, y⟫  : by ring
  ... = -re (⟪x, y⟫†) - re ⟪x, y⟫ + re ⟪x, x⟫ + re ⟪y, y⟫ : by rw[inner_conj_sym]
  ... = -re ⟪x, y⟫ - re ⟪x, y⟫ + re ⟪x, x⟫ + re ⟪y, y⟫ : by rw[conj_re]
  ... = re ⟪x, x⟫ - 2*re ⟪x, y⟫ + re ⟪y, y⟫ : by ring
end

/-- Cauchy–Schwarz inequality with norm -/
lemma abs_inner_le_norm (x y : F) : abs ⟪x, y⟫ ≤ ∥x∥ * ∥y∥ :=
nonneg_le_nonneg_of_squares_le (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
begin
  have H : ∥x∥ * ∥y∥ * (∥x∥ * ∥y∥) = re ⟪y, y⟫ * re ⟪x, x⟫,
  { simp only [inner_self_eq_norm_square], ring, },
  rw H,
  conv
  begin
    to_lhs, congr, rw[inner_abs_conj_sym],
  end,
  exact inner_mul_inner_self_le y x,
end

lemma parallelogram_law_with_norm {x y : F} :
  ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥) :=
begin
  simp only [(inner_self_eq_norm_square _).symm],
  rw[←add_monoid_hom.map_add, parallelogram_law, two_mul, two_mul],
  simp only [add_monoid_hom.map_add],
end

/-- Normed group structure constructed from an `inner_product_space.core` structure -/
def to_normed_group : normed_group F :=
normed_group.of_core F
{ norm_eq_zero_iff := assume x,
  begin
    split,
    { intro H,
      change sqrt (re ⟪x, x⟫) = 0 at H,
      rw [sqrt_eq_zero inner_self_nonneg] at H,
      apply (inner_self_eq_zero : ⟪x, x⟫ = 0 ↔ x = 0).mp,
      rw ext_iff,
      exact ⟨by simp [H], by simp [inner_self_im_zero]⟩ },
    { rintro rfl,
      change sqrt (re ⟪0, 0⟫) = 0,
      simp only [sqrt_zero, inner_zero_right, add_monoid_hom.map_zero] }
  end,
  triangle := assume x y,
  begin
    have h₁ : abs ⟪x, y⟫ ≤ ∥x∥ * ∥y∥ := abs_inner_le_norm _ _,
    have h₂ : re ⟪x, y⟫ ≤ abs ⟪x, y⟫ := re_le_abs _,
    have h₃ : re ⟪x, y⟫ ≤ ∥x∥ * ∥y∥ := by linarith,
    have h₄ : re ⟪y, x⟫ ≤ ∥x∥ * ∥y∥ := by rwa [←inner_conj_sym, conj_re],
    have : ∥x + y∥ * ∥x + y∥ ≤ (∥x∥ + ∥y∥) * (∥x∥ + ∥y∥),
    { simp [←inner_self_eq_norm_square, inner_add_add_self, add_mul, mul_add, mul_comm],
      linarith },
    exact nonneg_le_nonneg_of_squares_le (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this
  end,
  norm_neg := λ x, by simp only [norm, inner_neg_left, neg_neg, inner_neg_right]
}

local attribute [instance] to_normed_group

/-- Normed space structure constructed from a `inner_product_space.core` structure -/
def to_normed_space : normed_space K F :=
{ norm_smul_le := assume r x,
  begin
    rw [norm_eq_sqrt_inner, inner_smul_left, inner_smul_right, ←mul_assoc],
    rw [conj_mul_eq_norm_sq_left, of_real_mul_re, sqrt_mul, ←inner_norm_sq_eq_inner_self, of_real_re],
    { simp [sqrt_norm_sq_eq_norm, is_R_or_C.sqrt_norm_sq_eq_norm] },
    { exact norm_sq_nonneg r }
  end }

end inner_product_space.of_core

/-- Given a `inner_product_space.core` structure on a space, one can use it to turn
the space into an inner product space, constructing the norm out of the inner product -/
def inner_product_space.of_core [add_comm_group F] [semimodule K F]
  (c : inner_product_space.core K F) : inner_product_space K F :=
begin
  letI : normed_group F := @inner_product_space.of_core.to_normed_group F K _ _ _ _ _ c,
  letI : normed_space K F := @inner_product_space.of_core.to_normed_space F K _ _ _ _ _ c,
  exact { norm_sq_eq_inner := λ x,
    begin
      have h₁ : ∥x∥^2 = (sqrt (re (c.inner x x))) ^ 2 := rfl,
      have h₂ : 0 ≤ re (c.inner x x) := inner_product_space.of_core.inner_self_nonneg,
      simp [h₁, sqr_sqrt, h₂],
    end,
    ..c }
end

/-! ### Properties of complex inner product spaces -/

variables [inner_product_space K α]
local notation `⟪`x`, `y`⟫` := @inner K α _ x y
local postfix `†`:90 := @is_R_or_C.conj K _ _ _

export inner_product_space (norm_sq_eq_inner)

section basic_properties

lemma inner_conj_sym (x y : α) : ⟪y, x⟫† = ⟪x, y⟫ := inner_product_space.conj_sym _ _

lemma inner_self_nonneg_im {x : α} : im ⟪x, x⟫ = 0 := inner_product_space.nonneg_im _

lemma inner_self_im_zero {x : α} : im ⟪x, x⟫ = 0 := inner_product_space.nonneg_im _

lemma inner_add_left {x y z : α} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
inner_product_space.add_left _ _ _

lemma inner_add_right {x y z : α} : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ :=
begin
  rw [←inner_conj_sym, inner_add_left, ring_hom.map_add],
  conv_rhs { rw ←inner_conj_sym, conv { congr, skip, rw ←inner_conj_sym } }
end

lemma inner_re_symm {x y : α} : re ⟪x, y⟫ = re ⟪y, x⟫ :=
by rw [←inner_conj_sym, conj_re]

lemma inner_im_symm {x y : α} : im ⟪x, y⟫ = -im ⟪y, x⟫ :=
by rw [←inner_conj_sym, conj_im]

lemma inner_smul_left {x y : α} {r : K} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
inner_product_space.smul_left _ _ _

lemma inner_smul_right {x y : α} {r : K} : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_smul_left, ring_hom.map_mul, conj_conj, inner_conj_sym]

@[simp] lemma inner_zero_left {x : α} : ⟪0, x⟫ = 0 :=
by rw [← zero_smul K (0:α), inner_smul_left, ring_hom.map_zero, zero_mul]

lemma inner_re_zero_left {x : α} : re ⟪0, x⟫ = 0 :=
by simp only [inner_zero_left, add_monoid_hom.map_zero]

@[simp] lemma inner_zero_right {x : α} : ⟪x, 0⟫ = 0 :=
by rw [←inner_conj_sym, inner_zero_left, ring_hom.map_zero]

lemma inner_re_zero_right {x : α} : re ⟪x, 0⟫ = 0 :=
by simp only [inner_zero_right, add_monoid_hom.map_zero]

lemma inner_self_nonneg {x : α} : 0 ≤ re ⟪x, x⟫ :=
by rw [←norm_sq_eq_inner]; exact pow_nonneg (norm_nonneg x) 2

@[simp] lemma inner_self_eq_zero {x : α} : ⟪x, x⟫ = 0 ↔ x = 0 :=
begin
  split,
  { intro h,
    have h₁ : re ⟪x, x⟫ = 0 := by rw ext_iff at h; simp [h.1],
    rw [←norm_sq_eq_inner x] at h₁,
    rw [←norm_eq_zero],
    exact pow_eq_zero h₁ },
  { rintro rfl,
    exact inner_zero_left }
end

@[simp] lemma inner_self_nonpos {x : α} : re ⟪x, x⟫ ≤ 0 ↔ x = 0 :=
begin
  split,
  { intro h,
    rw ←inner_self_eq_zero,
    have H₁ : re ⟪x, x⟫ ≥ 0, exact inner_self_nonneg,
    have H₂ : re ⟪x, x⟫ = 0, exact le_antisymm h H₁,
    rw ext_iff,
    exact ⟨by simp [H₂], by simp [inner_self_nonneg_im]⟩ },
  { rintro rfl,
    simp only [inner_zero_left, add_monoid_hom.map_zero] }
end

@[simp] lemma inner_self_re_to_K {x : α} : 𝓚 (re ⟪x, x⟫) = ⟪x, x⟫ :=
by rw ext_iff; exact ⟨by simp, by simp [inner_self_nonneg_im]⟩

lemma inner_self_re_abs {x : α} : re ⟪x, x⟫ = abs ⟪x, x⟫ :=
begin
  have H : ⟪x, x⟫ = 𝓚 (re ⟪x, x⟫) + 𝓚 (im ⟪x, x⟫) * I,
  { rw re_add_im, },
  rw [H, is_add_hom.map_add re (𝓚 (re ⟪x, x⟫)) ((𝓚 (im ⟪x, x⟫)) * I)],
  rw [mul_re, I_re, mul_zero, I_im, zero_sub, tactic.ring.add_neg_eq_sub],
  rw [of_real_re, of_real_im, sub_zero, inner_self_nonneg_im],
  simp only [abs_of_real, add_zero, of_real_zero, zero_mul],
  exact (_root_.abs_of_nonneg inner_self_nonneg).symm,
end

lemma inner_self_abs_to_K {x : α} : 𝓚 (abs ⟪x, x⟫) = ⟪x, x⟫ :=
by { rw[←inner_self_re_abs], exact inner_self_re_to_K }

lemma inner_abs_conj_sym {x y : α} : abs ⟪x, y⟫ = abs ⟪y, x⟫ :=
by rw [←inner_conj_sym, abs_conj]

@[simp] lemma inner_neg_left {x y : α} : ⟪-x, y⟫ = -⟪x, y⟫ :=
by { rw [← neg_one_smul K x, inner_smul_left], simp }

@[simp] lemma inner_neg_right {x y : α} : ⟪x, -y⟫ = -⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_neg_left]; simp only [ring_hom.map_neg, inner_conj_sym]

lemma inner_neg_neg {x y : α} : ⟪-x, -y⟫ = ⟪x, y⟫ := by simp

@[simp] lemma inner_self_conj {x : α} : ⟪x, x⟫† = ⟪x, x⟫ :=
by rw [ext_iff]; exact ⟨by rw [conj_re], by rw [conj_im, inner_self_im_zero, neg_zero]⟩

lemma inner_sub_left {x y z : α} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_left] }

lemma inner_sub_right {x y z : α} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_right] }

lemma inner_mul_conj_re_abs {x y : α} : re (⟪x, y⟫ * ⟪y, x⟫) = abs (⟪x, y⟫ * ⟪y, x⟫) :=
by { rw[←inner_conj_sym, mul_comm], exact re_eq_abs_of_mul_conj (inner y x), }

/-- Expand `inner (x + y) (x + y)` -/
lemma inner_add_add_self {x y : α} : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_add_left, inner_add_right]; ring

/- Expand `inner (x - y) (x - y)` -/
lemma inner_sub_sub_self {x y : α} : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_sub_left, inner_sub_right]; ring

/-- Parallelogram law -/
lemma parallelogram_law {x y : α} :
  ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫) :=
by simp [inner_add_add_self, inner_sub_sub_self, two_mul, sub_eq_add_neg, add_comm, add_left_comm]

/-- Cauchy–Schwarz inequality. This proof follows "Proof 2" on Wikipedia. -/
lemma inner_mul_inner_self_le (x y : α) : abs ⟪x, y⟫ * abs ⟪y, x⟫ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
begin
  by_cases hy : y = 0,
  { rw [hy], simp only [abs_zero, inner_zero_left, mul_zero, add_monoid_hom.map_zero] },
  { change y ≠ 0 at hy,
    have hy' : ⟪y, y⟫ ≠ 0 := λ h, by rw [inner_self_eq_zero] at h; exact hy h,
    set T := ⟪y, x⟫ / ⟪y, y⟫ with hT,
    have h₁ : re ⟪y, x⟫ = re ⟪x, y⟫ := inner_re_symm,
    have h₂ : im ⟪y, x⟫ = -im ⟪x, y⟫ := inner_im_symm,
    have h₃ : ⟪y, x⟫ * ⟪x, y⟫ * ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = ⟪y, x⟫ * ⟪x, y⟫ / ⟪y, y⟫,
    { rw [mul_div_assoc],
      have : ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = 1 / ⟪y, y⟫ :=
        by rw [div_mul_eq_div_mul_one_div, div_self hy', one_mul],
      rw [this, div_eq_mul_inv, one_mul, ←div_eq_mul_inv] },
    have h₄ : ⟪y, y⟫ = 𝓚 (re ⟪y, y⟫) := by simp,
    have h₅ : re ⟪y, y⟫ > 0,
    { refine lt_of_le_of_ne inner_self_nonneg _,
      intro H,
      apply hy',
      rw ext_iff,
      exact ⟨by simp [H],by simp [inner_self_nonneg_im]⟩ },
    have h₆ : re ⟪y, y⟫ ≠ 0 := ne_of_gt h₅,
    have hmain := calc
      0   ≤ re ⟪x - T • y, x - T • y⟫
                  : inner_self_nonneg
      ... = re ⟪x, x⟫ - re ⟪T • y, x⟫ - re ⟪x, T • y⟫ + re ⟪T • y, T • y⟫
                  : by simp [inner_sub_sub_self, inner_smul_left, inner_smul_right, h₁, h₂]
      ... = re ⟪x, x⟫ - re (T† * ⟪y, x⟫) - re (T * ⟪x, y⟫) + re (T * T† * ⟪y, y⟫)
                  : by simp [inner_smul_left, inner_smul_right, mul_assoc]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ / ⟪y, y⟫ * ⟪y, x⟫)
                  : by field_simp [-mul_re, hT, conj_div, h₁, h₃, inner_conj_sym]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / ⟪y, y⟫)
                  : by rw [div_mul_eq_mul_div_comm, ←mul_div_assoc]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / 𝓚 (re ⟪y, y⟫))
                  : by conv_lhs { rw [h₄] }
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫
                  : by rw [div_re_of_real]
      ... = re ⟪x, x⟫ - abs (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫
                  : by rw [inner_mul_conj_re_abs]
      ... = re ⟪x, x⟫ - abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫
                  : by rw abs_mul,
    have hmain' : abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫ ≤ re ⟪x, x⟫ := by linarith,
    have := (mul_le_mul_right h₅).mpr hmain',
    rwa [div_mul_cancel (abs ⟪x, y⟫ * abs ⟪y, x⟫) h₆] at this }
end

end basic_properties


/-! ### Inner product space structure on product spaces -/

/-
 If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space,
then `Π i, f i` is an inner product space as well. This is not an instance to avoid conflict
with the default instance for the norm on `Π i, f i`.
-/
instance pi_Lp.inner_product_space {ι : Type*} [fintype ι] (f : ι → Type*)
  [Π i, inner_product_space K (f i)] : inner_product_space K (pi_Lp 2 one_le_two f) :=
{ inner := λ x y, ∑ i, inner (x i) (y i),
  norm_sq_eq_inner :=
  begin
    intro x,
    have h₁ : ∑ (i : ι), ∥x i∥ ^ (2 : ℕ) = ∑ (i : ι), ∥x i∥ ^ (2 : ℝ),
    { apply finset.sum_congr rfl,
      intros j hj,
      simp [←rpow_nat_cast] },
    have h₂ : 0 ≤ ∑ (i : ι), ∥x i∥ ^ (2 : ℝ),
    { rw [←h₁],
      exact finset.sum_nonneg (λ (j : ι) (hj : j ∈ finset.univ), pow_nonneg (norm_nonneg (x j)) 2) },
    simp [norm, add_monoid_hom.map_sum, ←norm_sq_eq_inner],
    rw [←rpow_nat_cast ((∑ (i : ι), ∥x i∥ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹) 2],
    rw [←rpow_mul h₂],
    norm_num [h₁],
  end,
  conj_sym :=
  begin
    intros x y,
    unfold inner,
    rw [←finset.sum_hom finset.univ conj],
    apply finset.sum_congr rfl,
    rintros z -,
    apply inner_conj_sym,
    apply_instance
  end,
  nonneg_im :=
  begin
    intro x,
    unfold inner,
    rw[←finset.sum_hom finset.univ im],
    apply finset.sum_eq_zero,
    rintros z -,
    exact inner_self_nonneg_im,
    apply_instance
  end,
  add_left := λ x y z,
    show ∑ i, inner (x i + y i) (z i) = ∑ i, inner (x i) (z i) + ∑ i, inner (y i) (z i),
    by simp only [inner_add_left, finset.sum_add_distrib],
  smul_left := λ x y r,
    show ∑ (i : ι), inner (r • x i) (y i) = (conj r) * ∑ i, inner (x i) (y i),
    by simp only [finset.mul_sum, inner_smul_left]
}

/-- A field `K` satisfying `is_R_or_C` is itself a `K`-inner product space. -/
instance is_R_or_C.inner_product_space : inner_product_space K K :=
{ inner := (λ x y, (conj x) * y),
  norm_sq_eq_inner := λ x, by unfold inner; rw [mul_comm, mul_conj, of_real_re, norm_sq, norm_sq_eq_def],
  conj_sym := λ x y, by simp [mul_comm],
  nonneg_im := λ x, by rw[mul_im, conj_re, conj_im]; ring,
  add_left := λ x y z, by simp [inner, add_mul],
  smul_left := λ x y z, by simp [inner, mul_assoc] }


/-- The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional space
use `euclidean_space K (fin n)`.  -/
@[reducible, nolint unused_arguments]
def euclidean_space (K : Type*) [nondiscrete_normed_field K] [algebra ℝ K] [is_R_or_C K]
  (n : Type*) [fintype n] : Type* := pi_Lp 2 one_le_two (λ (i : n), K)

section pi_Lp
local attribute [reducible] pi_Lp
variables {ι : Type*} [fintype ι]

instance : finite_dimensional K (euclidean_space K ι) := by apply_instance

@[simp] lemma findim_euclidean_space :
  finite_dimensional.findim K (euclidean_space K ι) = fintype.card ι := by simp

lemma findim_euclidean_space_fin {n : ℕ} :
  finite_dimensional.findim K (euclidean_space K (fin n)) = n := by simp

end pi_Lp

end is_R_or_C
