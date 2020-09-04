/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import linear_algebra.bilinear_form
import linear_algebra.sesquilinear_form
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
We choose the convention that inner products are conjugate linear in the first argument and linear
in the second.

## Tags

inner product space, norm
-/

noncomputable theory

--namespace is_R_or_C

open is_R_or_C real set
open_locale big_operators

variables {F : Type*} {G : Type*}
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

/-- The norm squared function for `inner_product_space.core` structure. -/
def norm_sq (x : F) := reK ⟪x, x⟫

local notation `norm_sqF` := @norm_sq F K _ _ _ _ _ _

lemma inner_conj_sym (x y : F) : ⟪y, x⟫† = ⟪x, y⟫ := c.conj_sym x y

lemma inner_self_nonneg {x : F} : 0 ≤ re ⟪x, x⟫ := c.nonneg_re _

lemma inner_self_nonneg_im {x : F} : im ⟪x, x⟫ = 0 := c.nonneg_im _

lemma inner_self_im_zero {x : F} : im ⟪x, x⟫ = 0 := c.nonneg_im _

lemma inner_add_left {x y z : F} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
c.add_left _ _ _

lemma inner_add_right {x y z : F} : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ :=
by rw [←inner_conj_sym, inner_add_left, ring_hom.map_add]; simp only [inner_conj_sym]

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

lemma inner_zero_left {x : F} : ⟪0, x⟫ = 0 :=
by rw [←zero_smul K (0 : F), inner_smul_left]; simp only [zero_mul, ring_hom.map_zero]

lemma inner_zero_right {x : F} : ⟪x, 0⟫ = 0 :=
by rw [←inner_conj_sym, inner_zero_left]; simp only [ring_hom.map_zero]

lemma inner_self_eq_zero {x : F} : ⟪x, x⟫ = 0 ↔ x = 0 :=
iff.intro (c.definite _) (by { rintro rfl, exact inner_zero_left })

lemma inner_self_re_to_K {x : F} : 𝓚 (re ⟪x, x⟫) = ⟪x, x⟫ :=
by norm_num [ext_iff, inner_self_nonneg_im]

lemma inner_abs_conj_sym {x y : F} : abs ⟪x, y⟫ = abs ⟪y, x⟫ :=
  by rw [←inner_conj_sym, abs_conj]

lemma inner_neg_left {x y : F} : ⟪-x, y⟫ = -⟪x, y⟫ :=
by { rw [← neg_one_smul K x, inner_smul_left], simp }

lemma inner_neg_right {x y : F} : ⟪x, -y⟫ = -⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_neg_left]; simp only [ring_hom.map_neg, inner_conj_sym]

lemma inner_sub_left {x y z : F} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_left, inner_neg_left] }

lemma inner_sub_right {x y z : F} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_right, inner_neg_right] }

lemma inner_mul_conj_re_abs {x y : F} : re (⟪x, y⟫ * ⟪y, x⟫) = abs (⟪x, y⟫ * ⟪y, x⟫) :=
by { rw[←inner_conj_sym, mul_comm], exact re_eq_abs_of_mul_conj (inner y x), }

/-- Expand `inner (x + y) (x + y)` -/
lemma inner_add_add_self {x y : F} : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_add_left, inner_add_right]; ring

/- Expand `inner (x - y) (x - y)` -/
lemma inner_sub_sub_self {x y : F} : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_sub_left, inner_sub_right]; ring

/--
Cauchy–Schwarz inequality. This proof follows "Proof 2" on Wikipedia.
We need this for the `core` structure to prove the triangle inequality below when
showing the core is a normed group.
-/
lemma inner_mul_inner_self_le (x y : F) : abs ⟪x, y⟫ * abs ⟪y, x⟫ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
begin
  by_cases hy : y = 0,
  { rw [hy], simp only [is_R_or_C.abs_zero, inner_zero_left, mul_zero, add_monoid_hom.map_zero] },
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
                  : by field_simp [-mul_re, inner_conj_sym, hT, conj_div, h₁, h₃]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / ⟪y, y⟫)
                  : by rw [div_mul_eq_mul_div_comm, ←mul_div_assoc]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / 𝓚 (re ⟪y, y⟫))
                  : by conv_lhs { rw [h₄] }
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫
                  : by rw [div_re_of_real]
      ... = re ⟪x, x⟫ - abs (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫
                  : by rw [inner_mul_conj_re_abs]
      ... = re ⟪x, x⟫ - abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫
                  : by rw is_R_or_C.abs_mul,
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
  norm_neg := λ x, by simp only [norm, inner_neg_left, neg_neg, inner_neg_right] }

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

/-! ### Properties of inner product spaces -/

variables {α β γ : Type*}
  [inner_product_space K α] [inner_product_space ℝ β] [inner_product_space ℂ γ]
local notation `⟪`x`, `y`⟫` := @inner K α _ x y
local notation `⟪`x`, `y`⟫_ℝ` := @inner ℝ β _ x y
local notation `⟪`x`, `y`⟫_ℂ` := @inner ℂ γ _ x y
local notation `IK` := @is_R_or_C.I K _ _ _
local postfix `†`:90 := @is_R_or_C.conj K _ _ _
local postfix `⋆`:90 := complex.conj

export inner_product_space (norm_sq_eq_inner)

section basic_properties

lemma inner_conj_sym (x y : α) : ⟪y, x⟫† = ⟪x, y⟫ := inner_product_space.conj_sym _ _
lemma real.inner_comm (x y : β) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := inner_conj_sym x y

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
lemma real.inner_smul_left {x y : β} {r : ℝ} : ⟪r • x, y⟫_ℝ = r * ⟪x, y⟫_ℝ := inner_smul_left

lemma inner_smul_right {x y : α} {r : K} : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_smul_left, ring_hom.map_mul, conj_conj, inner_conj_sym]
lemma real.inner_smul_right {x y : β} {r : ℝ} : ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ := inner_smul_right

/-- The inner product as a sesquilinear form. -/
def sesq_form_of_inner : sesq_form K α conj_to_ring_equiv :=
{ sesq := λ x y, ⟪y, x⟫,    -- Note that sesquilinear forms are linear in the first argument
  sesq_add_left := λ x y z, inner_add_right,
  sesq_add_right := λ x y z, inner_add_left,
  sesq_smul_left := λ r x y, inner_smul_right,
  sesq_smul_right := λ r x y, inner_smul_left }

/-- The real inner product as a bilinear form. -/
def real.bilin_form_of_inner : bilin_form ℝ β :=
{ bilin := inner,
  bilin_add_left := λ x y z, inner_add_left,
  bilin_smul_left := λ a x y, inner_smul_left,
  bilin_add_right := λ x y z, inner_add_right,
  bilin_smul_right := λ a x y, inner_smul_right }

/-- An inner product with a sum on the left. -/
lemma sum_inner {ι : Type*} (s : finset ι) (f : ι → α) (x : α) :
  ⟪∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫ :=
sesq_form.map_sum_right (sesq_form_of_inner) _ _ _

/-- An inner product with a sum on the right. -/
lemma inner_sum {ι : Type*} (s : finset ι) (f : ι → α) (x : α) :
  ⟪x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫ :=
sesq_form.map_sum_left (sesq_form_of_inner) _ _ _

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
lemma real.inner_self_nonneg {x : β} : 0 ≤ ⟪x, x⟫_ℝ := @inner_self_nonneg ℝ _ _ _ β _ x

@[simp] lemma inner_self_eq_zero {x : α} : ⟪x, x⟫ = 0 ↔ x = 0 :=
begin
  split,
  { intro h,
    have h₁ : re ⟪x, x⟫ = 0 := by rw is_R_or_C.ext_iff at h; simp [h.1],
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
    rw is_R_or_C.ext_iff,
    exact ⟨by simp [H₂], by simp [inner_self_nonneg_im]⟩ },
  { rintro rfl,
    simp only [inner_zero_left, add_monoid_hom.map_zero] }
end

@[simp] lemma inner_self_re_to_K {x : α} : 𝓚 (re ⟪x, x⟫) = ⟪x, x⟫ :=
by rw is_R_or_C.ext_iff; exact ⟨by simp, by simp [inner_self_nonneg_im]⟩

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
by rw [is_R_or_C.ext_iff]; exact ⟨by rw [conj_re], by rw [conj_im, inner_self_im_zero, neg_zero]⟩

lemma inner_sub_left {x y z : α} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_left] }

lemma inner_sub_right {x y z : α} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_right] }

lemma inner_mul_conj_re_abs {x y : α} : re (⟪x, y⟫ * ⟪y, x⟫) = abs (⟪x, y⟫ * ⟪y, x⟫) :=
by { rw[←inner_conj_sym, mul_comm], exact re_eq_abs_of_mul_conj (inner y x), }

/-- Expand `inner (x + y) (x + y)` -/
lemma inner_add_add_self {x y : α} : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_add_left, inner_add_right]; ring

/-- Expand `inner (x + y) (x + y)` -/
lemma real.inner_add_add_self {x y : β} : ⟪x + y, x + y⟫_ℝ = ⟪x, x⟫_ℝ + 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ :=
begin
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [←inner_conj_sym]; refl,
  simp [inner_add_add_self, this],
  ring,
end

/- Expand `inner (x - y) (x - y)` -/
lemma inner_sub_sub_self {x y : α} : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_sub_left, inner_sub_right]; ring

/-- Expand `inner (x - y) (x - y)` -/
lemma real.inner_sub_sub_self {x y : β} : ⟪x - y, x - y⟫_ℝ = ⟪x, x⟫_ℝ - 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ :=
begin
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [←inner_conj_sym]; refl,
  simp [inner_sub_sub_self, this],
  ring,
end

/-- Parallelogram law -/
lemma parallelogram_law {x y : α} :
  ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫) :=
by simp [inner_add_add_self, inner_sub_sub_self, two_mul, sub_eq_add_neg, add_comm, add_left_comm]

/-- Cauchy–Schwarz inequality. This proof follows "Proof 2" on Wikipedia. -/
lemma inner_mul_inner_self_le (x y : α) : abs ⟪x, y⟫ * abs ⟪y, x⟫ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
begin
  by_cases hy : y = 0,
  { rw [hy], simp only [is_R_or_C.abs_zero, inner_zero_left, mul_zero, add_monoid_hom.map_zero] },
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
      rw is_R_or_C.ext_iff,
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
                  : by rw is_R_or_C.abs_mul,
    have hmain' : abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫ ≤ re ⟪x, x⟫ := by linarith,
    have := (mul_le_mul_right h₅).mpr hmain',
    rwa [div_mul_cancel (abs ⟪x, y⟫ * abs ⟪y, x⟫) h₆] at this }
end

/-- Cauchy–Schwarz inequality -/
lemma real.inner_mul_inner_self_le (x y : β) : ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ :=
begin
  have h₁ : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [←inner_conj_sym]; refl,
  have h₂ := @inner_mul_inner_self_le ℝ _ _ _ β _ x y,
  dsimp at h₂,
  have h₃ := abs_mul_abs_self ⟪x, y⟫_ℝ,
  rw [h₁] at h₂,
  simpa [h₃] using h₂,
end

end basic_properties

section norm

lemma norm_eq_sqrt_inner (x : α) : ∥x∥ = sqrt (re ⟪x, x⟫) :=
begin
  have h₁ : ∥x∥^2 = re ⟪x, x⟫ := norm_sq_eq_inner x,
  have h₂ := congr_arg sqrt h₁,
  simpa using h₂,
end

lemma inner_self_eq_norm_square (x : α) : re ⟪x, x⟫ = ∥x∥ * ∥x∥ :=
  by rw[norm_eq_sqrt_inner, ←sqrt_mul inner_self_nonneg (re ⟪x, x⟫),
        sqrt_mul_self inner_self_nonneg]

lemma real.inner_self_eq_norm_square (x : β) : ⟪x, x⟫_ℝ = ∥x∥ * ∥x∥ :=
begin
  have h := @inner_self_eq_norm_square ℝ _ _ _ β _ x,
  simpa using h,
end


/-- Expand the square -/
lemma norm_add_pow_two {x y : α} : ∥x + y∥^2 = ∥x∥^2 + 2 * (re ⟪x, y⟫) + ∥y∥^2 :=
begin
  repeat {rw [pow_two, ←inner_self_eq_norm_square]},
  rw[inner_add_add_self, two_mul],
  simp only [add_assoc, add_left_inj, add_right_inj, add_monoid_hom.map_add],
  rw [←inner_conj_sym, conj_re],
end

/-- Expand the square -/
lemma real.norm_add_pow_two {x y : β} : ∥x + y∥^2 = ∥x∥^2 + 2 * inner x y + ∥y∥^2 :=
begin
  have h₁ := @norm_add_pow_two ℝ _ _ _ β _,
  simpa using h₁,
end

/-- Same lemma as above but in a different form -/
lemma norm_add_mul_self {x y : α} : ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + 2 * (re ⟪x, y⟫) + ∥y∥ * ∥y∥ :=
    by { repeat {rw [← pow_two]}, exact norm_add_pow_two }

/-- Same lemma as above but in a different form -/
lemma real.norm_add_mul_self {x y : β} : ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + 2 * inner x y + ∥y∥ * ∥y∥ :=
begin
  have h₁ := @norm_add_mul_self ℝ _ _ _ β _,
  simpa using h₁,
end

/-- Expand the square -/
lemma norm_sub_pow_two {x y : α} : ∥x - y∥^2 = ∥x∥^2 - 2 * (re ⟪x, y⟫) + ∥y∥^2 :=
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

/-- Expand the square -/
lemma real.norm_sub_pow_two {x y : β} : ∥x - y∥^2 = ∥x∥^2 - 2 * inner x y + ∥y∥^2 :=
begin
  have h₁ := @norm_sub_pow_two ℝ _ _ _ β _,
  simpa using h₁,
end

/-- Same lemma as above but in a different form -/
lemma norm_sub_mul_self {x y : α} : ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ - 2 * re ⟪x, y⟫ + ∥y∥ * ∥y∥ :=
by { repeat {rw [← pow_two]}, exact norm_sub_pow_two }

/-- Same lemma as above but in a different form -/
lemma real.norm_sub_mul_self {x y : β} : ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ - 2 * ⟪x, y⟫_ℝ + ∥y∥ * ∥y∥ :=
begin
  have h₁ := @norm_sub_mul_self ℝ _ _ _ β _,
  simpa using h₁,
end

/-- Cauchy–Schwarz inequality with norm -/
lemma abs_inner_le_norm (x y : α) : abs ⟪x, y⟫ ≤ ∥x∥ * ∥y∥ :=
nonneg_le_nonneg_of_squares_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
begin
  have : ∥x∥ * ∥y∥ * (∥x∥ * ∥y∥) = (re ⟪x, x⟫) * (re ⟪y, y⟫),
    simp only [inner_self_eq_norm_square], ring,
  rw this,
  conv_lhs { congr, skip, rw [inner_abs_conj_sym] },
  exact inner_mul_inner_self_le _ _
end

/-- Cauchy–Schwarz inequality with norm -/
lemma real.abs_inner_le_norm (x y : β) : _root_.abs ⟪x, y⟫_ℝ ≤ ∥x∥ * ∥y∥ :=
begin
  have h₁ := @abs_inner_le_norm ℝ _ _ _ β _ x y,
  simpa using h₁,
end

include K
lemma parallelogram_law_with_norm {x y : α} :
  ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥) :=
begin
  simp only [(inner_self_eq_norm_square _).symm],
  rw[←add_monoid_hom.map_add, parallelogram_law, two_mul, two_mul],
  simp only [add_monoid_hom.map_add],
end
omit K

lemma real.parallelogram_law_with_norm {x y : β} :
  ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥) :=
begin
  have h₁ := @parallelogram_law_with_norm ℝ _ _ _ β _ x y,
  simpa using h₁,
end

/-- Polarization identity: The real inner product, in terms of the norm. -/
lemma real.inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : β) :
  ⟪x, y⟫_ℝ = (∥x + y∥ * ∥x + y∥ - ∥x∥ * ∥x∥ - ∥y∥ * ∥y∥) / 2 :=
by rw norm_add_mul_self; ring

/-- Polarization identity: The real inner product, in terms of the norm. -/
lemma real.inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : β) :
  ⟪x, y⟫_ℝ = (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ - ∥x - y∥ * ∥x - y∥) / 2 :=
by rw norm_sub_mul_self; ring

/-- Pythagorean theorem, if-and-only-if vector inner product form. -/
lemma real.norm_add_square_eq_norm_square_add_norm_square_iff_inner_eq_zero (x y : β) :
  ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ ⟪x, y⟫_ℝ = 0 :=
begin
  rw [norm_add_mul_self, add_right_cancel_iff, add_right_eq_self, mul_eq_zero],
  norm_num
end

/-- Pythagorean theorem, vector inner product form. -/
lemma norm_add_square_eq_norm_square_add_norm_square {x y : β} (h : ⟪x, y⟫_ℝ = 0) :
  ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ :=
(real.norm_add_square_eq_norm_square_add_norm_square_iff_inner_eq_zero x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector
inner product form. -/
lemma real.norm_sub_square_eq_norm_square_add_norm_square_iff_inner_eq_zero (x y : β) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ ⟪x, y⟫_ℝ = 0 :=
begin
  rw [norm_sub_mul_self, add_right_cancel_iff, sub_eq_add_neg, add_right_eq_self, neg_eq_zero,
      mul_eq_zero],
  norm_num
end

/-- Pythagorean theorem, subtracting vectors, vector inner product
form. -/
lemma real.norm_sub_square_eq_norm_square_add_norm_square {x y : β} (h : ⟪x, y⟫_ℝ = 0) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ :=
(real.norm_sub_square_eq_norm_square_add_norm_square_iff_inner_eq_zero x y).2 h

/-- The sum and difference of two vectors are orthogonal if and only
if they have the same norm. -/
lemma real.inner_add_sub_eq_zero_iff (x y : β) : ⟪x + y, x - y⟫_ℝ = 0 ↔ ∥x∥ = ∥y∥ :=
begin
  conv_rhs { rw ←mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _) },
  simp only [←inner_self_eq_norm_square, inner_add_left, inner_sub_right,
            real.inner_comm y x, sub_eq_zero, re_to_real],
  split,
  { intro h,
    rw [add_comm] at h,
    linarith },
  { intro h,
    linarith }
end

/-- The real inner product of two vectors, divided by the product of their
norms, has absolute value at most 1. -/
lemma real.abs_inner_div_norm_mul_norm_le_one (x y : β) : _root_.abs (⟪x, y⟫_ℝ / (∥x∥ * ∥y∥)) ≤ 1 :=
begin
  rw _root_.abs_div,
  by_cases h : 0 = _root_.abs (∥x∥ * ∥y∥),
  { rw [←h, div_zero],
    norm_num },
  { change 0 ≠ _root_.abs (∥x∥ * ∥y∥) at h,
    rw div_le_iff' (lt_of_le_of_ne (ge_iff_le.mp (_root_.abs_nonneg (∥x∥ * ∥y∥))) h),
    convert real.abs_inner_le_norm x y using 1,
    rw [_root_.abs_mul, _root_.abs_of_nonneg (norm_nonneg x), _root_.abs_of_nonneg (norm_nonneg y), mul_one] }
end

/-- The inner product of a vector with a multiple of itself. -/
lemma real.inner_smul_self_left (x : β) (r : ℝ) : ⟪r • x, x⟫_ℝ = r * (∥x∥ * ∥x∥) :=
by rw [real.inner_smul_left, ←real.inner_self_eq_norm_square]

/-- The inner product of a vector with a multiple of itself. -/
lemma real.inner_smul_self_right (x : β) (r : ℝ) : ⟪x, r • x⟫_ℝ = r * (∥x∥ * ∥x∥) :=
by rw [inner_smul_right, ←real.inner_self_eq_norm_square]

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
lemma real.abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
  {x : β} {r : ℝ} (hx : x ≠ 0) (hr : r ≠ 0) : _root_.abs ⟪x, r • x⟫_ℝ / (∥x∥ * ∥r • x∥) = 1 :=
sorry

/-- The inner product of a nonzero vector with a positive multiple of
itself, divided by the product of their norms, has value 1. -/
lemma real.inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul
  {x : β} {r : ℝ} (hx : x ≠ 0) (hr : 0 < r) : ⟪x, r • x⟫_ℝ / (∥x∥ * ∥r • x∥) = 1 :=
sorry

/-- The inner product of a nonzero vector with a negative multiple of
itself, divided by the product of their norms, has value -1. -/
lemma real.inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul
  {x : β} {r : ℝ} (hx : x ≠ 0) (hr : r < 0) : ⟪x, r • x⟫_ℝ / (∥x∥ * ∥r • x∥) = -1 :=
sorry

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
lemma real.abs_inner_div_norm_mul_norm_eq_one_iff (x y : β) :
  _root_.abs (⟪x, y⟫_ℝ / (∥x∥ * ∥y∥)) = 1 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), r ≠ 0 ∧ y = r • x) :=
sorry

/-- The inner product of two vectors, divided by the product of their
norms, has value 1 if and only if they are nonzero and one is
a positive multiple of the other. -/
lemma real.inner_div_norm_mul_norm_eq_one_iff (x y : β) :
  ⟪x, y⟫_ℝ / (∥x∥ * ∥y∥) = 1 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), 0 < r ∧ y = r • x) :=
sorry

/-- The inner product of two vectors, divided by the product of their
norms, has value -1 if and only if they are nonzero and one is
a negative multiple of the other. -/
lemma real.inner_div_norm_mul_norm_eq_neg_one_iff (x y : β) :
  ⟪x, y⟫_ℝ / (∥x∥ * ∥y∥) = -1 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), r < 0 ∧ y = r • x) :=
sorry

-- The inner product of two weighted sums, where the weights in each
--sum add to 0, in terms of the norms of pairwise differences. -/
--lemma inner_sum_smul_sum_smul_of_sum_eq_zero {ι₁ : Type*} {s₁ : finset ι₁} {w₁ : ι₁ → ℝ}
--    (v₁ : ι₁ → α) (h₁ : ∑ i in s₁, w₁ i = 0) {ι₂ : Type*} {s₂ : finset ι₂} {w₂ : ι₂ → ℝ}
--    (v₂ : ι₂ → α) (h₂ : ∑ i in s₂, w₂ i = 0) :
--  inner (∑ i₁ in s₁, w₁ i₁ • v₁ i₁) (∑ i₂ in s₂, w₂ i₂ • v₂ i₂) =
--    (-∑ i₁ in s₁, ∑ i₂ in s₂, w₁ i₁ * w₂ i₂ * (∥v₁ i₁ - v₂ i₂∥ * ∥v₁ i₁ - v₂ i₂∥)) / 2 :=
--by simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
--            inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
--            ←div_sub_div_same, ←div_add_div_same, mul_sub_left_distrib, left_distrib,
--            finset.sum_sub_distrib, finset.sum_add_distrib, ←finset.mul_sum, ←finset.sum_mul,
--            h₁, h₂, zero_mul, mul_zero, finset.sum_const_zero, zero_add, zero_sub, finset.mul_sum,
--            neg_div, finset.sum_div, mul_div_assoc, mul_assoc]

end norm

/-! ### Inner product space structure on product spaces -/

/-
 If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space,
then `Π i, f i` is an inner product space as well. Since `Π i, f i` is endowed with the sup norm,
we use instead `pi_Lp 2 one_le_two f` for the product space, which is endowed with the `L^2` norm.
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


/-! ### Orthogonal projection in inner product spaces -/
section orthogonal

open filter

/--
Existence of minimizers
Let `u` be a point in an inner product space, and let `K` be a nonempty complete convex subset.
Then there exists a unique `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
 -/
-- FIXME this monolithic proof causes a deterministic timeout with `-T50000`
-- It should be broken in a sequence of more manageable pieces,
-- perhaps with individual statements for the three steps below.
theorem real.exists_norm_eq_infi_of_complete_convex {K : set β} (ne : K.nonempty) (h₁ : is_complete K)
  (h₂ : convex K) : ∀ u : β, ∃ v ∈ K, ∥u - v∥ = ⨅ w : K, ∥u - w∥ := assume u,
begin
  let δ := ⨅ w : K, ∥u - w∥,
  letI : nonempty K := ne.to_subtype,
  have zero_le_δ : 0 ≤ δ := le_cinfi (λ _, norm_nonneg _),
  have δ_le : ∀ w : K, δ ≤ ∥u - w∥,
    from cinfi_le ⟨0, forall_range_iff.2 $ λ _, norm_nonneg _⟩,
  have δ_le' : ∀ w ∈ K, δ ≤ ∥u - w∥ := assume w hw, δ_le ⟨w, hw⟩,
  -- Step 1: since `δ` is the infimum, can find a sequence `w : ℕ → K` in `K`
  -- such that `∥u - w n∥ < δ + 1 / (n + 1)` (which implies `∥u - w n∥ --> δ`);
  -- maybe this should be a separate lemma
  have exists_seq : ∃ w : ℕ → K, ∀ n, ∥u - w n∥ < δ + 1 / (n + 1),
  { have hδ : ∀n:ℕ, δ < δ + 1 / (n + 1), from
      λ n, lt_add_of_le_of_pos (le_refl _) nat.one_div_pos_of_nat,
    have h := λ n, exists_lt_of_cinfi_lt (hδ n),
    let w : ℕ → K := λ n, classical.some (h n),
    exact ⟨w, λ n, classical.some_spec (h n)⟩ },
  rcases exists_seq with ⟨w, hw⟩,
  have norm_tendsto : tendsto (λ n, ∥u - w n∥) at_top (nhds δ),
  { have h : tendsto (λ n:ℕ, δ) at_top (nhds δ) := tendsto_const_nhds,
    have h' : tendsto (λ n:ℕ, δ + 1 / (n + 1)) at_top (nhds δ),
    { convert h.add tendsto_one_div_add_at_top_nhds_0_nat, simp only [add_zero] },
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h h'
      (λ x, δ_le _) (λ x, le_of_lt (hw _)) },
  -- Step 2: Prove that the sequence `w : ℕ → K` is a Cauchy sequence
  have seq_is_cauchy : cauchy_seq (λ n, ((w n):β)),
  { rw cauchy_seq_iff_le_tendsto_0, -- splits into three goals
    let b := λ n:ℕ, (8 * δ * (1/(n+1)) + 4 * (1/(n+1)) * (1/(n+1))),
    use (λn, sqrt (b n)),
    split,
    -- first goal :  `∀ (n : ℕ), 0 ≤ sqrt (b n)`
    assume n, exact sqrt_nonneg _,
    split,
    -- second goal : `∀ (n m N : ℕ), N ≤ n → N ≤ m → dist ↑(w n) ↑(w m) ≤ sqrt (b N)`
    assume p q N hp hq,
    let wp := ((w p):β), let wq := ((w q):β),
    let a := u - wq, let b := u - wp,
    let half := 1 / (2:ℝ), let div := 1 / ((N:ℝ) + 1),
    have : 4 * ∥u - half • (wq + wp)∥ * ∥u - half • (wq + wp)∥ + ∥wp - wq∥ * ∥wp - wq∥ =
      2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) :=
    calc
      4 * ∥u - half•(wq + wp)∥ * ∥u - half•(wq + wp)∥ + ∥wp - wq∥ * ∥wp - wq∥
          = (2*∥u - half•(wq + wp)∥) * (2 * ∥u - half•(wq + wp)∥) + ∥wp-wq∥*∥wp-wq∥ : by ring
      ... = (_root_.abs((2:ℝ)) * ∥u - half•(wq + wp)∥) * (_root_.abs((2:ℝ)) * ∥u - half•(wq+wp)∥) + ∥wp-wq∥*∥wp-wq∥ :
      by { rw _root_.abs_of_nonneg, exact add_nonneg zero_le_one zero_le_one }
      ... = ∥(2:ℝ) • (u - half • (wq + wp))∥ * ∥(2:ℝ) • (u - half • (wq + wp))∥ + ∥wp-wq∥ * ∥wp-wq∥ :
        by { rw [norm_smul], refl }
      ... = ∥a + b∥ * ∥a + b∥ + ∥a - b∥ * ∥a - b∥ :
      begin
        rw [smul_sub, smul_smul, mul_one_div_cancel (_root_.two_ne_zero : (2 : ℝ) ≠ 0),
            ← one_add_one_eq_two, add_smul],
        simp only [one_smul],
        have eq₁ : wp - wq = a - b, show wp - wq = (u - wq) - (u - wp), abel,
        have eq₂ : u + u - (wq + wp) = a + b, show u + u - (wq + wp) = (u - wq) + (u - wp), abel,
        rw [eq₁, eq₂],
      end
      ... = 2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) : parallelogram_law_with_norm,
    have eq : δ ≤ ∥u - half • (wq + wp)∥,
    { rw smul_add,
      apply δ_le', apply h₂,
        repeat {exact subtype.mem _},
        repeat {exact le_of_lt one_half_pos},
        exact add_halves 1 },
    have eq₁ : 4 * δ * δ ≤ 4 * ∥u - half • (wq + wp)∥ * ∥u - half • (wq + wp)∥,
    {  mono, mono, norm_num, apply mul_nonneg, norm_num, exact norm_nonneg _ },
    have eq₂ : ∥a∥ * ∥a∥ ≤ (δ + div) * (δ + div) :=
      mul_self_le_mul_self (norm_nonneg _)
        (le_trans (le_of_lt $ hw q) (add_le_add_left (nat.one_div_le_one_div hq) _)),
    have eq₂' : ∥b∥ * ∥b∥ ≤ (δ + div) * (δ + div) :=
      mul_self_le_mul_self (norm_nonneg _)
        (le_trans (le_of_lt $ hw p) (add_le_add_left (nat.one_div_le_one_div hp) _)),
    rw dist_eq_norm,
    apply nonneg_le_nonneg_of_squares_le, { exact sqrt_nonneg _ },
    rw mul_self_sqrt,
    exact calc
      ∥wp - wq∥ * ∥wp - wq∥ = 2 * (∥a∥*∥a∥ + ∥b∥*∥b∥) - 4 * ∥u - half • (wq+wp)∥ * ∥u - half • (wq+wp)∥ :
        by { rw ← this, simp }
      ... ≤ 2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) - 4 * δ * δ : sub_le_sub_left eq₁ _
      ... ≤ 2 * ((δ + div) * (δ + div) + (δ + div) * (δ + div)) - 4 * δ * δ :
        sub_le_sub_right (mul_le_mul_of_nonneg_left (add_le_add eq₂ eq₂') (by norm_num)) _
      ... = 8 * δ * div + 4 * div * div : by ring,
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) zero_le_δ) (le_of_lt nat.one_div_pos_of_nat))
      (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt nat.one_div_pos_of_nat)) (le_of_lt nat.one_div_pos_of_nat)),
    -- third goal : `tendsto (λ (n : ℕ), sqrt (b n)) at_top (𝓝 0)`
    apply tendsto.comp,
    { convert continuous_sqrt.continuous_at, exact sqrt_zero.symm },
    have eq₁ : tendsto (λ (n : ℕ), 8 * δ * (1 / (n + 1))) at_top (nhds (0:ℝ)),
    { convert (@tendsto_const_nhds _ _ _ (8 * δ) _).mul tendsto_one_div_add_at_top_nhds_0_nat,
      simp only [mul_zero] },
    have : tendsto (λ (n : ℕ), (4:ℝ) * (1 / (n + 1))) at_top (nhds (0:ℝ)),
    { convert (@tendsto_const_nhds _ _ _ (4:ℝ) _).mul tendsto_one_div_add_at_top_nhds_0_nat,
      simp only [mul_zero] },
    have eq₂ : tendsto (λ (n : ℕ), (4:ℝ) * (1 / (n + 1)) * (1 / (n + 1))) at_top (nhds (0:ℝ)),
    { convert this.mul tendsto_one_div_add_at_top_nhds_0_nat,
      simp only [mul_zero] },
    convert eq₁.add eq₂, simp only [add_zero] },
  -- Step 3: By completeness of `K`, let `w : ℕ → K` converge to some `v : K`.
  -- Prove that it satisfies all requirements.
  rcases cauchy_seq_tendsto_of_is_complete h₁ (λ n, _) seq_is_cauchy with ⟨v, hv, w_tendsto⟩,
  use v, use hv,
  have h_cont : continuous (λ v, ∥u - v∥) :=
    continuous.comp continuous_norm (continuous.sub continuous_const continuous_id),
  have : tendsto (λ n, ∥u - w n∥) at_top (nhds ∥u - v∥),
    convert (tendsto.comp h_cont.continuous_at w_tendsto),
  exact tendsto_nhds_unique this norm_tendsto,
  exact subtype.mem _
end

/-- Characterization of minimizers in the above theorem -/
theorem real.norm_eq_infi_iff_inner_le_zero {K : set β} (h : convex K) {u : β} {v : β}
  (hv : v ∈ K) : ∥u - v∥ = (⨅ w : K, ∥u - w∥) ↔ ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0 :=
iff.intro
begin
  assume eq w hw,
  let δ := ⨅ w : K, ∥u - w∥, let p := inner (u - v) (w - v), let q := ∥w - v∥^2,
  letI : nonempty K := ⟨⟨v, hv⟩⟩,
  have zero_le_δ : 0 ≤ δ,
    apply le_cinfi, intro, exact norm_nonneg _,
  have δ_le : ∀ w : K, δ ≤ ∥u - w∥,
    assume w, apply cinfi_le, use (0:ℝ), rintros _ ⟨_, rfl⟩, exact norm_nonneg _,
  have δ_le' : ∀ w ∈ K, δ ≤ ∥u - w∥ := assume w hw, δ_le ⟨w, hw⟩,
  have : ∀θ:ℝ, 0 < θ → θ ≤ 1 → 2 * p ≤ θ * q,
    assume θ hθ₁ hθ₂,
    have : ∥u - v∥^2 ≤ ∥u - v∥^2 - 2 * θ * inner (u - v) (w - v) + θ*θ*∥w - v∥^2 :=
    calc
      ∥u - v∥^2 ≤ ∥u - (θ•w + (1-θ)•v)∥^2 :
      begin
        simp only [pow_two], apply mul_self_le_mul_self (norm_nonneg _),
        rw [eq], apply δ_le',
        apply h hw hv,
        exacts [le_of_lt hθ₁, sub_nonneg.2 hθ₂, add_sub_cancel'_right _ _],
      end
      ... = ∥(u - v) - θ • (w - v)∥^2 :
      begin
        have : u - (θ•w + (1-θ)•v) = (u - v) - θ • (w - v),
        { rw [smul_sub, sub_smul, one_smul],
          simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add_rev] },
        rw this
      end
      ... = ∥u - v∥^2 - 2 * θ * inner (u - v) (w - v) + θ*θ*∥w - v∥^2 :
      begin
        rw [norm_sub_pow_two, inner_smul_right, norm_smul],
        simp only [pow_two],
        show ∥u-v∥*∥u-v∥-2*(θ*inner(u-v)(w-v))+abs(θ)*∥w-v∥*(abs(θ)*∥w-v∥)=
                ∥u-v∥*∥u-v∥-2*θ*inner(u-v)(w-v)+θ*θ*(∥w-v∥*∥w-v∥),
        rw abs_of_pos hθ₁, ring
      end,
    have eq₁ : ∥u-v∥^2-2*θ*inner(u-v)(w-v)+θ*θ*∥w-v∥^2=∥u-v∥^2+(θ*θ*∥w-v∥^2-2*θ*inner(u-v)(w-v)), abel,
    rw [eq₁, le_add_iff_nonneg_right] at this,
    have eq₂ : θ*θ*∥w-v∥^2-2*θ*inner(u-v)(w-v)=θ*(θ*∥w-v∥^2-2*inner(u-v)(w-v)), ring,
    rw eq₂ at this,
    have := le_of_sub_nonneg (nonneg_of_mul_nonneg_left this hθ₁),
    exact this,
  by_cases hq : q = 0,
  { rw hq at this,
    have : p ≤ 0,
      have := this (1:ℝ) (by norm_num) (by norm_num),
      linarith,
    exact this },
  { have q_pos : 0 < q,
      apply lt_of_le_of_ne, exact pow_two_nonneg _, intro h, exact hq h.symm,
    by_contradiction hp, rw not_le at hp,
    let θ := min (1:ℝ) (p / q),
    have eq₁ : θ*q ≤ p := calc
      θ*q ≤ (p/q) * q : mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_two_nonneg _)
      ... = p : div_mul_cancel _ hq,
    have : 2 * p ≤ p := calc
      2 * p ≤ θ*q : by { refine this θ (lt_min (by norm_num) (div_pos hp q_pos)) (by norm_num) }
      ... ≤ p : eq₁,
    linarith }
end
begin
  assume h,
  letI : nonempty K := ⟨⟨v, hv⟩⟩,
  apply le_antisymm,
  { apply le_cinfi, assume w,
    apply nonneg_le_nonneg_of_squares_le (norm_nonneg _),
    have := h w w.2,
    exact calc
      ∥u - v∥ * ∥u - v∥ ≤ ∥u - v∥ * ∥u - v∥ - 2 * inner (u - v) ((w:α) - v) : by linarith
      ... ≤ ∥u - v∥^2 - 2 * inner (u - v) ((w:α) - v) + ∥(w:α) - v∥^2 :
        by { rw pow_two, refine le_add_of_nonneg_right _, exact pow_two_nonneg _ }
      ... = ∥(u - v) - (w - v)∥^2 : norm_sub_pow_two.symm
      ... = ∥u - w∥ * ∥u - w∥ :
        by { have : (u - v) - (w - v) = u - w, abel, rw [this, pow_two] } },
  { show (⨅ (w : K), ∥u - w∥) ≤ (λw:K, ∥u - w∥) ⟨v, hv⟩,
      apply cinfi_le, use 0, rintros y ⟨z, rfl⟩, exact norm_nonneg _ }
end

/--
Existence of minimizers.
Let `u` be a point in an inner product space, and let `K` be a nonempty complete subspace.
Then there exists a unique `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
This point `v` is usually called the orthogonal projection of `u` onto `K`.
-/
theorem real.exists_norm_eq_infi_of_complete_subspace (K : subspace ℝ β)
  (h : is_complete (↑K : set β)) : ∀ u : β, ∃ v ∈ K, ∥u - v∥ = ⨅ w : (↑K : set β), ∥u - w∥ :=
real.exists_norm_eq_infi_of_complete_convex ⟨0, K.zero_mem⟩ h K.convex

/--
Characterization of minimizers in the above theorem.
Let `u` be a point in an inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `∥u - v∥` if and only if
for all `w ∈ K`, `inner (u - v) w = 0` (i.e., `u - v` is orthogonal to the subspace `K`)
-/
theorem real.norm_eq_infi_iff_inner_eq_zero (K : subspace ℝ β) {u : β} {v : β}
  (hv : v ∈ K) : ∥u - v∥ = (⨅ w : (↑K : set β), ∥u - w∥) ↔ ∀ w ∈ K, ⟪u - v, w⟫_ℝ = 0 :=
iff.intro
begin
  assume h,
  have h : ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0,
  { rwa [norm_eq_infi_iff_inner_le_zero] at h, exacts [K.convex, hv] },
  assume w hw,
  have le : inner (u - v) w ≤ 0,
    let w' := w + v,
    have : w' ∈ K := submodule.add_mem _ hw hv,
    have h₁ := h w' this,
    have h₂ : w' - v = w, simp only [add_neg_cancel_right, sub_eq_add_neg],
    rw h₂ at h₁, exact h₁,
  have ge : inner (u - v) w ≥ 0,
    let w'' := -w + v,
    have : w'' ∈ K := submodule.add_mem _ (submodule.neg_mem _ hw) hv,
    have h₁ := h w'' this,
    have h₂ : w'' - v = -w, simp only [neg_inj, add_neg_cancel_right, sub_eq_add_neg],
    rw [h₂, inner_neg_right] at h₁,
    linarith,
    exact le_antisymm le ge
end
begin
  assume h,
  have : ∀ w ∈ K, inner (u - v) (w - v) ≤ 0,
    assume w hw,
    let w' := w - v,
    have : w' ∈ K := submodule.sub_mem _ hw hv,
    have h₁ := h w' this,
    exact le_of_eq h₁,
  rwa norm_eq_infi_iff_inner_le_zero,
  exacts [submodule.convex _, hv]
end

/-- The orthogonal projection onto a complete subspace, as an
unbundled function.  This definition is only intended for use in
setting up the bundled version `orthogonal_projection` and should not
be used once that is defined. -/
def real.orthogonal_projection_fn {K : submodule ℝ β} (h : is_complete (K : set β)) (v : β) :=
(real.exists_norm_eq_infi_of_complete_subspace K h v).some

/-- The unbundled orthogonal projection is in the given subspace.
This lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
lemma real.orthogonal_projection_fn_mem {K : submodule ℝ β} (h : is_complete (K : set β)) (v : β) :
  real.orthogonal_projection_fn h v ∈ K :=
(real.exists_norm_eq_infi_of_complete_subspace K h v).some_spec.some

/-- The characterization of the unbundled orthogonal projection.  This
lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
lemma real.orthogonal_projection_fn_inner_eq_zero {K : submodule ℝ β} (h : is_complete (K : set β))
  (v : β) : ∀ w ∈ K, ⟪v - real.orthogonal_projection_fn h v, w⟫_ℝ = 0 :=
begin
  rw ←norm_eq_infi_iff_inner_eq_zero K (orthogonal_projection_fn_mem h v),
  exact (exists_norm_eq_infi_of_complete_subspace K h v).some_spec.some_spec
end

/-- The unbundled orthogonal projection is the unique point in `K`
with the orthogonality property.  This lemma is only intended for use
in setting up the bundled version and should not be used once that is
defined. -/
lemma real.eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero {K : submodule ℝ β}
  (h : is_complete (K : set β)) {u v : β} (hvm : v ∈ K) (hvo : ∀ w ∈ K, ⟪u - v, w⟫_ℝ = 0) :
  v = real.orthogonal_projection_fn h u :=
begin
  rw [←sub_eq_zero, ←inner_self_eq_zero],
  have hvs : v - real.orthogonal_projection_fn h u ∈ K :=
    submodule.sub_mem K hvm (real.orthogonal_projection_fn_mem h u),
  have huo : inner (u - real.orthogonal_projection_fn h u) (v - real.orthogonal_projection_fn h u) = 0 :=
    orthogonal_projection_fn_inner_eq_zero h u _ hvs,
  have huv : inner (u - v) (v - orthogonal_projection_fn h u) = 0 := hvo _ hvs,
  have houv : inner ((u - orthogonal_projection_fn h u) - (u - v))
                    (v - orthogonal_projection_fn h u) = 0,
  { rw [inner_sub_left, huo, huv, sub_zero] },
  rwa sub_sub_sub_cancel_left at houv
end

/-- The orthogonal projection onto a complete subspace.  For most
purposes, `orthogonal_projection`, which removes the `is_complete`
hypothesis and is the identity map when the subspace is not complete,
should be used instead. -/
def real.orthogonal_projection_of_complete {K : submodule ℝ β} (h : is_complete (K : set β)) :
  linear_map ℝ β β :=
{ to_fun := real.orthogonal_projection_fn h,
  map_add' := λ x y, begin
    have hm : orthogonal_projection_fn h x + orthogonal_projection_fn h y ∈ K :=
      submodule.add_mem K (orthogonal_projection_fn_mem h x) (orthogonal_projection_fn_mem h y),
    have ho :
      ∀ w ∈ K, inner (x + y - (orthogonal_projection_fn h x + orthogonal_projection_fn h y)) w = 0,
    { intros w hw,
      rw [add_sub_comm, inner_add_left, orthogonal_projection_fn_inner_eq_zero h _ w hw,
          orthogonal_projection_fn_inner_eq_zero h _ w hw, add_zero] },
    rw eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero h hm ho
  end,
  map_smul' := λ c x, begin
    have hm : c • orthogonal_projection_fn h x ∈ K :=
      submodule.smul_mem K _ (orthogonal_projection_fn_mem h x),
    have ho : ∀ w ∈ K, inner (c • x - c • orthogonal_projection_fn h x) w = 0,
    { intros w hw,
      rw [←smul_sub, inner_smul_left, orthogonal_projection_fn_inner_eq_zero h _ w hw, mul_zero] },
    rw eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero h hm ho
  end }

/-- The orthogonal projection onto a subspace, which is expected to be
complete.  If the subspace is not complete, this uses the identity map
instead. -/
def real.orthogonal_projection (K : submodule ℝ β) : linear_map ℝ β β :=
if h : is_complete (K : set β) then real.orthogonal_projection_of_complete h else linear_map.id

/-- The definition of `orthogonal_projection` using `if`. -/
lemma real.orthogonal_projection_def (K : submodule ℝ β) :
  real.orthogonal_projection K =
    if h : is_complete (K : set β) then orthogonal_projection_of_complete h else linear_map.id :=
rfl

@[simp]
lemma real.orthogonal_projection_fn_eq {K : submodule ℝ β} (h : is_complete (K : set β)) (v : β) :
  orthogonal_projection_fn h v = orthogonal_projection K v :=
by { rw [orthogonal_projection_def, dif_pos h], refl }

/-- The orthogonal projection is in the given subspace. -/
lemma real.orthogonal_projection_mem {K : submodule ℝ β} (h : is_complete (K : set β)) (v : β) :
  orthogonal_projection K v ∈ K :=
begin
  rw ←orthogonal_projection_fn_eq h,
  exact orthogonal_projection_fn_mem h v
end

/-- The characterization of the orthogonal projection.  -/
@[simp]
lemma real.orthogonal_projection_inner_eq_zero (K : submodule ℝ β) (v : β) :
  ∀ w ∈ K, inner (v - orthogonal_projection K v) w = 0 :=
begin
  simp_rw orthogonal_projection_def,
  split_ifs,
  { exact orthogonal_projection_fn_inner_eq_zero h v },
  { simp },
end

/-- The orthogonal projection is the unique point in `K` with the
orthogonality property. -/
lemma real.eq_orthogonal_projection_of_mem_of_inner_eq_zero {K : submodule ℝ β}
  (h : is_complete (K : set β)) {u v : β} (hvm : v ∈ K) (hvo : ∀ w ∈ K, inner (u - v) w = 0) :
  v = orthogonal_projection K u :=
begin
  rw ←orthogonal_projection_fn_eq h,
  exact eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero h hvm hvo
end

/-- The subspace of vectors orthogonal to a given subspace. -/
def real.submodule.orthogonal (K : submodule ℝ β) : submodule ℝ β :=
{ carrier := {v | ∀ u ∈ K, inner u v = 0},
  zero_mem' := λ _ _, inner_zero_right,
  add_mem' := λ x y hx hy u hu, by rw [inner_add_right, hx u hu, hy u hu, add_zero],
  smul_mem' := λ c x hx u hu, by rw [inner_smul_right, hx u hu, mul_zero] }

/-- When a vector is in `K.orthogonal`. -/
lemma real.submodule.mem_orthogonal (K : submodule ℝ β) (v : β) :
  v ∈ K.orthogonal ↔ ∀ u ∈ K, inner u v = 0 :=
iff.rfl

/-- When a vector is in `K.orthogonal`, with the inner product the
other way round. -/
lemma real.submodule.mem_orthogonal' (K : submodule ℝ β) (v : β) :
  v ∈ K.orthogonal ↔ ∀ u ∈ K, inner v u = 0 :=
by simp_rw [submodule.mem_orthogonal, inner_comm]

/-- A vector in `K` is orthogonal to one in `K.orthogonal`. -/
lemma real.submodule.inner_right_of_mem_orthogonal {u v : β} {K : submodule ℝ β} (hu : u ∈ K)
    (hv : v ∈ K.orthogonal) : inner u v = 0 :=
(K.mem_orthogonal v).1 hv u hu

/-- A vector in `K.orthogonal` is orthogonal to one in `K`. -/
lemma real.submodule.inner_left_of_mem_orthogonal {u v : β} {K : submodule ℝ β} (hu : u ∈ K)
    (hv : v ∈ K.orthogonal) : inner v u = 0 :=
inner_comm u v ▸ submodule.inner_right_of_mem_orthogonal hu hv

/-- `K` and `K.orthogonal` have trivial intersection. -/
lemma real.submodule.orthogonal_disjoint (K : submodule ℝ β) : disjoint K K.orthogonal :=
begin
  simp_rw [submodule.disjoint_def, submodule.mem_orthogonal],
  exact λ x hx ho, inner_self_eq_zero.1 (ho x hx)
end

variables (β)

/-- `submodule.orthogonal` gives a `galois_connection` between
`submodule ℝ β` and its `order_dual`. -/
lemma real.submodule.orthogonal_gc :
  @galois_connection (submodule ℝ β) (order_dual $ submodule ℝ β) _ _
    submodule.orthogonal submodule.orthogonal :=
λ K₁ K₂, ⟨λ h v hv u hu, submodule.inner_left_of_mem_orthogonal hv (h hu),
          λ h v hv u hu, submodule.inner_left_of_mem_orthogonal hv (h hu)⟩

variables {β}

/-- `K` is contained in `K.orthogonal.orthogonal`. -/
lemma real.submodule.le_orthogonal_orthogonal (K : submodule ℝ α) : K ≤ K.orthogonal.orthogonal :=
(submodule.orthogonal_gc α).le_u_l _

/-- The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup. -/
lemma submodule.inf_orthogonal (K₁ K₂ : submodule ℝ α) :
  K₁.orthogonal ⊓ K₂.orthogonal = (K₁ ⊔ K₂).orthogonal :=
(submodule.orthogonal_gc α).l_sup.symm

/-- The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup. -/
lemma submodule.infi_orthogonal {ι : Type*} (K : ι → submodule ℝ α) :
  (⨅ i, (K i).orthogonal) = (supr K).orthogonal :=
(submodule.orthogonal_gc α).l_supr.symm

/-- The inf of a set of orthogonal subspaces equals the subspace
orthogonal to the sup. -/
lemma submodule.Inf_orthogonal (s : set $ submodule ℝ α) :
  (⨅ K ∈ s, submodule.orthogonal K) = (Sup s).orthogonal :=
(submodule.orthogonal_gc α).l_Sup.symm

/-- If `K` is complete, `K` and `K.orthogonal` span the whole
space. -/
lemma submodule.sup_orthogonal_of_is_complete {K : submodule ℝ α} (h : is_complete (K : set α)) :
  K ⊔ K.orthogonal = ⊤ :=
begin
  rw submodule.eq_top_iff',
  intro x,
  rw submodule.mem_sup,
  rcases exists_norm_eq_infi_of_complete_subspace K h x with ⟨v, hv, hvm⟩,
  rw norm_eq_infi_iff_inner_eq_zero K hv at hvm,
  use [v, hv, x - v],
  split,
  { rw submodule.mem_orthogonal',
    exact hvm },
  { exact add_sub_cancel'_right _ _ }
end

/-- If `K` is complete, `K` and `K.orthogonal` are complements of each
other. -/
lemma submodule.is_compl_orthogonal_of_is_complete {K : submodule ℝ α}
    (h : is_complete (K : set α)) : is_compl K K.orthogonal :=
⟨K.orthogonal_disjoint, le_of_eq (submodule.sup_orthogonal_of_is_complete h).symm⟩

end orthogonal
