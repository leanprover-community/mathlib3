/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis

Based on real_inner_product.lean:
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel
-/

import algebra.quadratic_discriminant
import analysis.special_functions.pow
import topology.metric_space.pi_Lp
import data.complex.is_R_or_C

/-!
# Inner Product Space

This file defines inner product spaces and proves its basic properties.

A complex inner product space is a vector space endowed with an inner product `⟨·,·⟩` which
satisfies `⟨x, y⟩ = conj ⟨y, x⟩`.

## Main results

- We define the class `complex_inner_product_space` with a number of basic properties, most
  notably the Cauchy-Schwarz inequality.
- We show that if `f i` is a complex inner product space for each `i`, then so is `Π i, f i`
- We define `complex_euclidean_space n` to be `n → ℂ` for any `fintype n`, and show that
  this a complex inner product space.

## Notation

We locally denote the inner product by `⟪·,·⟫`.

## Tags

inner product space, norm
-/

noncomputable theory

namespace is_R_or_C

open is_R_or_C set -- vector_space finite_dimensional submodule module
open_locale big_operators
open_locale topological_space

variables {α : Type*} {F : Type*} {G : Type*}
variables {K : Type*} [nondiscrete_normed_field K] [algebra ℝ K] [is_R_or_C K]
local notation `𝓚` := @is_R_or_C.of_real K _ _ _

-- Some stuff on complex numbers that don't seem to be in the library --
--namespace complex
--
--lemma abs_eq_re_of_im_zero_of_re_nonneg (x : ℂ) : x.im = 0 → x.re ≥ 0 → x.re = x.abs :=
--begin
--  intros im_zero re_nonneg,
--  have H₁ : x.re ≤ x.abs, exact re_le_abs x,
--  unfold abs,
--  unfold norm_sq,
--  rw[im_zero, mul_zero, add_zero, sqrt_mul_self],
--  exact re_nonneg,
--end
--
--lemma re_eq_abs_of_mul_conj (x : ℂ) : (x * (conj x)).re = (x * (conj x)).abs :=
--begin
--  unfold abs,
--  rw[mul_re, conj_re, conj_im],
--  ring,
--  unfold norm_sq,
--  rw[mul_re, mul_im, conj_re, conj_im, ←neg_mul_eq_neg_mul, sub_neg_eq_add],
--  ring,
--  have h₁ : x.re * x.im - x.im * x.re = 0, ring,
--  rw[h₁, mul_zero, add_zero],
--  have h₂ : 0 ≤ x.re * x.re + x.im * x.im,
--  {
--    calc
--      0 ≤ x.norm_sq  : by exact norm_sq_nonneg x
--      ... = x.re * x.re + x.im * x.im   : by unfold norm_sq,
--  },
--  rw[sqrt_mul h₂, mul_self_sqrt h₂, pow_two, pow_two],
--end
--
--lemma conj_mul_eq_norm_sq_left (x : ℂ) : x.conj * x = x.norm_sq :=
--  by { unfold norm_sq, ext, norm_num, norm_num, ring }
--
--lemma conj_mul_re_eq_norm_sq_left (x : ℂ) : (x.conj * x).re = x.norm_sq :=
--  by { rw[conj_mul_eq_norm_sq_left], norm_cast }
--
--lemma conj_mul_eq_norm_sq_right (x : ℂ) : x * x.conj = x.norm_sq :=
--  by { rw[mul_comm], exact conj_mul_eq_norm_sq_left x }
--
--lemma abs_eq_norm_sq_sqrt (x : ℂ) : x.abs = x.norm_sq.sqrt := rfl
--
--end complex

class has_inner (K α : Type*) := (inner : α → α → K)

export has_inner (inner)

section prio

set_option default_priority 100 -- see Note [default priority]
-- see Note[vector space definition] for why we extend `semimodule`.
/--
An inner product space is a vector space with an additional operation called inner product.
The norm could be derived from the inner product, instead we require the existence of a norm and
the fact that it is equal to `sqrt (inner x x)` to be able to put instances on `K` or product
spaces.

To construct a norm from an inner product, see `inner_product_space.of_core`.
-/
class inner_product_space (K : Type*) (α : Type*)
  [nondiscrete_normed_field K] [algebra ℝ K] [is_R_or_C K]
  extends normed_group α, normed_space K α, has_inner K α :=
(norm_sq_eq_inner : ∀ (x : α), ∥x∥^2 = re (inner x x))
(conj_sym  : ∀ x y, inner x y = conj (inner y x))
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
local postfix `†`:100 := @is_R_or_C.conj K _ _ _

def to_has_inner : has_inner K F := { inner := c.inner }
local attribute [instance] to_has_inner


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

lemma inner_smul_left {x y : F} {r : K} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
c.smul_left _ _ _

lemma inner_smul_right {x y : F} {r : K} : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_smul_left]; simp only [conj_conj, inner_conj_sym, ring_hom.map_mul]

@[simp] lemma inner_zero_left {x : F} : ⟪0, x⟫ = 0 :=
by rw [←zero_smul K (0 : F), inner_smul_left]; simp only [zero_mul, ring_hom.map_zero]

@[simp] lemma inner_re_zero_left {x : F} : re ⟪0, x⟫ = 0 :=
by rw [←zero_smul K (0 : F), inner_smul_left];
  simp only [inner_zero_left, mul_zero, add_monoid_hom.map_zero]

@[simp] lemma inner_zero_right {x : F} : ⟪x, 0⟫ = 0 :=
by rw [←inner_conj_sym, inner_zero_left]; simp only [ring_hom.map_zero]

@[simp] lemma inner_re_zero_right {x : F} : re ⟪x, 0⟫ = 0 :=
by rw [←inner_conj_sym, inner_zero_left]; simp only [ring_hom.map_zero, add_monoid_hom.map_zero]

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

lemma inner_mul_conj_re_abs {x y : F} : re (⟪x, y⟫ * ⟪y, x⟫) = abs (⟪x, y⟫ * ⟪y, x⟫) := sorry
--by { rw[←inner_conj_sym, mul_comm], exact complex.re_eq_abs_of_mul_conj (inner y x), }

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
Cauchy–Schwarz inequality
We need this for the `core` structure to prove the triangle inequality below when
showing the core is a normed group.
-/
lemma inner_mul_inner_self_le (x y : F) : re (⟪x, y⟫ * ⟪y, x⟫) ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
begin
  have hquad : ∀ t : ℝ, 0 ≤ re ⟪y, y⟫ * t * t + abs (⟪x, y⟫ + ⟪y, x⟫) * t + re ⟪x, x⟫,
  { intro t,
    calc
      0   ≤ re ⟪x + (𝓚 t) • y, x + (𝓚 t) • y⟫   : inner_self_nonneg
      ... = re ⟪y, y⟫ * t * t + (re ⟪x, y⟫ + re ⟪y, x⟫) * t + re ⟪x, x⟫
              : begin
                  simp [inner_add_add_self, inner_sub_sub_self, inner_smul_right,
                        inner_smul_left, of_real_mul_re],
                  ring
                end
      ... = re ⟪y, y⟫ * t * t + re (⟪x, y⟫ + ⟪y, x⟫) * t + re ⟪x, x⟫
              : by simp only [add_monoid_hom.map_add]
      ... = re ⟪y, y⟫ * t * t + abs (⟪x, y⟫ + ⟪y, x⟫) * t + re ⟪x, x⟫
              : begin
                sorry,
              end },
  have h₁ : re ⟪y, x⟫ = re ⟪x, y⟫ := inner_symm_re,
  rw [mul_re, h₁],
  have hdisc := discriminant_le_zero hquad,
  have hdisc' : 4 * re ⟪x, y⟫^2 ≤ 4 * (re ⟪x, x⟫ * re ⟪y, y⟫),
  { rw [discrim, pow_two] at hdisc,
    simp [h₁] at hdisc,
    rw [←mul_assoc],
    ring at hdisc,
    exact hdisc },

  --exact (mul_le_mul_left (show (0 : ℝ) < 4, by linarith)).mp hdisc'
  sorry,
end

/-- Norm constructed from a `complex_inner_product_space.core` structure, defined to be the square root
of the scalar product. -/
def to_has_norm : has_norm F :=
{ norm := λ x, sqrt (inner x x).re }

local attribute [instance] to_has_norm


lemma norm_eq_sqrt_inner (x : F) : ∥x∥ = sqrt (inner x x).re := rfl

lemma inner_self_eq_norm_square (x : F) : (inner x x).re = ∥x∥ * ∥x∥ :=
  by rw[norm_eq_sqrt_inner, ←sqrt_mul inner_self_nonneg (inner x x).re,
        sqrt_mul_self inner_self_nonneg]

/-- Expand the square -/
lemma norm_add_pow_two {x y : F} : ∥x + y∥^2 = ∥x∥^2 + 2 * (inner x y).re + ∥y∥^2 :=
begin
  repeat {rw [pow_two, ←inner_self_eq_norm_square]},
  rw[inner_add_add_self, two_mul],
  simp only [add_re, add_assoc, add_left_inj, add_right_inj],
  rw [inner_conj_sym, conj_re],
end

/-- Same lemma as above but in a different form -/
lemma norm_add_mul_self {x y : F} : ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + 2 * (inner x y).re + ∥y∥ * ∥y∥ :=
    by { repeat {rw [← pow_two]}, exact norm_add_pow_two }

/-- Expand the square -/
lemma norm_sub_pow_two {x y : F} : ∥x - y∥^2 = ∥x∥^2 - 2 * (inner x y).re + ∥y∥^2 :=
begin
repeat {rw [pow_two, ←inner_self_eq_norm_square]},
rw[inner_sub_sub_self],
have H : (inner x x - inner x y - inner y x + inner y y).re
    = (inner x x).re - 2* (inner x y).re + (inner y y).re,
calc
  (inner x x - inner x y - inner y x + inner y y).re
      = (inner x x).re - (inner x y).re - (inner y x).re + (inner y y).re  : by simp
  ... = -(inner y x).re - (inner x y).re + (inner x x).re + (inner y y).re  : by ring
  ... = -(inner x y).conj.re - (inner x y).re + (inner x x).re + (inner y y).re : by rw[inner_conj_sym]
  ... = -(inner x y).re - (inner x y).re + (inner x x).re + (inner y y).re : by rw[conj_re]
  ... = (inner x x).re - 2*(inner x y).re + (inner y y).re : by ring,
exact H,
end

-- Same lemma as above but in a different form -/
--lemma norm_sub_mul_self {x y : α} : ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ - 2 * (inner x y).re + ∥y∥ * ∥y∥ :=
--  by { repeat {rw [← pow_two]}, exact norm_sub_pow_two }

-- Cauchy–Schwarz inequality with norm -/
lemma abs_inner_le_norm (x y : F) : abs (inner x y) ≤ ∥x∥ * ∥y∥ :=
nonneg_le_nonneg_of_squares_le (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
begin
  have H : ∥x∥ * ∥y∥ * (∥x∥ * ∥y∥) = (inner y y).re * (inner x x).re,
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
  rw[←add_re, parallelogram_law, two_mul, two_mul],
  refl,
end

/-- Normed group structure constructed from a `complex_inner_product_space.core`
structure -/
def to_normed_group : normed_group F :=
normed_group.of_core F
{ norm_eq_zero_iff := assume x,
  begin
    split,
    intro H,
    change sqrt (inner x x).re = 0 at H,
    rw[sqrt_eq_zero inner_self_nonneg] at H,
    have H' : inner x x = 0,
    { ext, assumption, rw[inner_self_nonneg_im], refl, },
    rwa[←inner_self_eq_zero],
    --
    intro H,
    rw H,
    change sqrt (inner (0 : F) 0).re = 0,
    rw[inner_zero_left, zero_re, sqrt_zero],
  end,
  triangle := assume x y,
  begin
    have := calc
      ∥x + y∥ * ∥x + y∥ = (inner (x + y) (x + y)).re : (inner_self_eq_norm_square _).symm
      ... = (inner x x + inner x y + inner y x + inner y y).re : by rw[inner_add_add_self]
      ... = (inner x x + inner x y + inner y x).re + (inner y y).re : by rw[add_re]
      ... = (inner x x + inner x y).re + (inner y x).re + (inner y y).re : by rw[add_re]
      ... = (inner x x).re + (inner x y).re + (inner y x).re + (inner y y).re : by rw[add_re]
      ... = (inner x x).re + (inner y y).re + (inner x y).re + (inner y x).re : by ring
      ... ≤ (inner x x).re + (inner y y).re + (inner x y).re + (inner y x).abs :
            begin
              have : (inner y x).re ≤ (inner y x).abs, exact re_le_abs (inner y x),
              apply add_le_add_left this,
            end
      ... = (inner x x).re + (inner y y).re + (inner y x).abs + (inner x y).re: by ring
      ... ≤ (inner x x).re + (inner y y).re + (inner y x).abs + (inner x y).abs:
            begin
              have : (inner x y).re ≤ (inner x y).abs, exact re_le_abs (inner x y),
              apply add_le_add_left this,
            end
      ... ≤ (inner x x).re + (inner y y).re + (∥y∥ * ∥x∥) + (∥x∥ * ∥y∥) :
              by linarith[abs_inner_le_norm x y, abs_inner_le_norm y x]
      ... = (inner x x).re + (inner y y).re + 2* (∥x∥ * ∥y∥) : by ring
      ... = (∥x∥ + ∥y∥) * (∥x∥ + ∥y∥) : by { simp only [inner_self_eq_norm_square], ring },
    exact nonneg_le_nonneg_of_squares_le (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this
  end,
  norm_neg := λx, show sqrt ((inner (-x) (-x)).re) = (sqrt (inner x x).re), by rw[inner_neg_neg],
}

local attribute [instance] to_normed_group

/-
Normed space structure constructed from a `complex_inner_product_space.core` structure
-/
def to_normed_space : normed_space ℂ F :=
{ norm_smul_le := assume r x,
  begin
    rw [norm_eq_sqrt_inner, inner_smul_left, inner_smul_right],
    have := calc
    (r.conj * (r * inner x x)).re.sqrt
        = ((r.conj * r) * (inner x x)).re.sqrt : by ring
    ... = (↑(r.norm_sq) * (inner x x)).re.sqrt : by rw[complex.conj_mul_eq_norm_sq_left]
    ... = ((r.norm_sq : ℂ) * ↑(norm_sq x)).re.sqrt : by rw[inner_norm_sq_eq_inner_self]
    ... = (r.norm_sq * norm_sq x).sqrt : by norm_cast
    ... = r.norm_sq.sqrt * (norm_sq x).sqrt : sqrt_mul (norm_sq_nonneg r) (norm_sq x),

    rw[this],
    unfold norm,
    rw[norm_eq_sqrt_inner, ←inner_norm_sq_eq_inner_self_re, complex.abs_eq_norm_sq_sqrt],
  end
}

end complex_inner_product_space.of_core

/-- Given a `complex_inner_product_space.core` structure on a space, one can use it to turn
the space into a complex inner product space, constructing the norm out of the inner
product -/

def complex_inner_product_space.of_core [add_comm_group F] [semimodule ℂ F]
  (c : complex_inner_product_space.core F) : complex_inner_product_space F :=
begin
  letI : normed_group F := @complex_inner_product_space.of_core.to_normed_group F _ _ c,
  letI : normed_space ℂ F := @complex_inner_product_space.of_core.to_normed_space F _ _ c,
  exact { norm_eq_sqrt_inner := λ x, rfl, .. c }
end

/-! ### Properties of complex inner product spaces -/

variables [complex_inner_product_space α]

export complex_inner_product_space (norm_eq_sqrt_inner)

section basic_properties

lemma inner_conj_sym (x y : α) : inner x y = conj (inner y x) := complex_inner_product_space.conj_sym x y

lemma inner_self_nonneg_im {x : α} : (inner x x).im = 0 := complex_inner_product_space.nonneg_im _

lemma inner_self_im_zero {x : α} : (inner x x).im = 0 := complex_inner_product_space.nonneg_im _

lemma inner_add_left {x y z : α} : inner (x + y) z = inner x z + inner y z :=
complex_inner_product_space.add_left _ _ _

lemma inner_add_right {x y z : α} : inner x (y + z) = inner x y + inner x z :=
begin
  rw[inner_conj_sym, inner_add_left, conj_add],
  conv
  begin
    to_rhs,
    rw inner_conj_sym,
    conv
    begin
      congr, skip, rw inner_conj_sym,
    end
  end,
end

lemma inner_smul_left {x y : α} {r : ℂ} : inner (r • x) y = (conj r) * inner x y :=
complex_inner_product_space.smul_left _ _ _

lemma inner_smul_right {x y : α} {r : ℂ} : inner x (r • y) = r * inner x y :=
by rw [inner_conj_sym, inner_smul_left, complex.conj_mul, conj_conj, ←inner_conj_sym]

@[simp] lemma inner_zero_left {x : α} : inner 0 x = 0 :=
by rw [← zero_smul ℂ (0:α), inner_smul_left, conj_zero, zero_mul]

@[simp] lemma inner_re_zero_left {x : α} : (inner 0 x).re = 0 :=
by { rw [← zero_smul ℂ (0:α), inner_smul_left, conj_zero, zero_mul], refl }

@[simp] lemma inner_zero_right {x : α} : inner x 0 = 0 :=
by rw [inner_conj_sym, inner_zero_left, conj_zero]

@[simp] lemma inner_re_zero_right {x : α} : (inner x 0).re = 0 :=
by { rw [inner_conj_sym, inner_zero_left], refl }

lemma inner_self_nonneg {x : α} : 0 ≤ (inner x x).re :=
begin
  classical,
  by_cases h : x = 0, simp[h],
  -- x ≠ 0
  have : 0 < sqrt (inner x x).re,
    rw[←norm_eq_sqrt_inner], exact norm_pos_iff.mpr h,
  exact le_of_lt (sqrt_pos.1 this),
end

@[simp] lemma inner_self_eq_zero {x : α} : inner x x = 0 ↔ x = 0 :=
begin
  split,
  -- inner x x = 0 → x = 0
  intro h,
  have h₁ : (inner x x).re = 0, simp only [h, zero_re],
  have h₂ : (inner x x).re ≥ 0, simp only [h₁, ge_iff_le],
  rw[←sqrt_eq_zero h₂, ←norm_eq_sqrt_inner] at h₁,
  exact norm_eq_zero.mp h₁,
  -- x = 0 → inner x x = 0
  intro h,
  rw[h, inner_zero_left],
end

@[simp] lemma inner_self_nonpos {x : α} : (inner x x).re ≤ 0 ↔ x = 0 :=
begin
  split,
  intro h,
  rw ←inner_self_eq_zero,
  have H₁ : (inner x x).re ≥ 0, exact inner_self_nonneg,
  have H₂ : (inner x x).re = 0, exact le_antisymm h H₁,
  ext, exact H₂,
  exact inner_self_im_zero,
  --
  intro h,
  rw [h, inner_zero_left], refl,
end

@[simp] lemma inner_self_re_tocomplex {x : α} : ((inner x x).re : ℂ) = inner x x :=
  by { ext, norm_num, rw[inner_self_nonneg_im], norm_num }

@[simp] lemma inner_self_re_abs {x : α} : (inner x x).re = (inner x x).abs :=
begin
  have H : inner x x = (inner x x).re + (inner x x).im * I,
  { rw re_add_im, },
  rw[H, add_re, mul_re, I_re, mul_zero, I_im, mul_one, zero_sub],
  norm_cast,
  rw [neg_zero, add_zero, inner_self_nonneg_im],
  simp only [abs_of_real, add_zero, of_real_zero, zero_mul],
  rw[complex.abs_eq_re_of_im_zero_of_re_nonneg (inner x x) inner_self_im_zero],
  rw [abs_abs (inner x x)],
  exact inner_self_nonneg,
end

lemma inner_self_abs_tocomplex {x : α} : ((inner x x).abs : ℂ) = inner x x :=
  by { rw[←inner_self_re_abs], exact inner_self_re_tocomplex }

@[simp] lemma inner_abs_conj_sym {x y : α} : (inner x y).abs = (inner y x).abs :=
  by rw [inner_conj_sym, abs_conj]

@[simp] lemma inner_neg_left {x y : α} : inner (-x) y = -inner x y :=
by { rw [← neg_one_smul ℂ x, inner_smul_left], simp }

@[simp] lemma inner_neg_right {x y : α} : inner x (-y) = -inner x y :=
by { rw [inner_conj_sym, inner_neg_left, inner_conj_sym, conj_neg, conj_conj] }

@[simp] lemma inner_neg_neg {x y : α} : inner (-x) (-y) = inner x y := by simp

@[simp] lemma inner_self_conj {x : α} : (inner x x).conj = (inner x x) :=
  by {ext, rw[conj_re], rw[conj_im, inner_self_im_zero, neg_zero]}

lemma inner_sub_left {x y z : α} : inner (x - y) z = inner x z - inner y z :=
by { simp [sub_eq_add_neg, inner_add_left] }

lemma inner_sub_right {x y z : α} : inner x (y - z) = inner x y - inner x z :=
by { simp [sub_eq_add_neg, inner_add_right] }

lemma inner_mul_conj_re_abs {x y : α} : (inner x y * inner y x).re = (inner x y * inner y x).abs :=
by { rw[inner_conj_sym, mul_comm], exact complex.re_eq_abs_of_mul_conj (inner y x), }

/-- Expand `inner (x + y) (x + y)` -/
lemma inner_add_add_self {x y : α} : inner (x + y) (x + y) = inner x x + inner x y + inner y x + inner y y :=
begin
  have H : inner (x + y) (x + y) = (inner x x + inner x y) + inner y (x+y),
  {
    calc
    inner (x + y) (x + y) = inner x (x+y) + inner y (x+y)                   : by rw[inner_add_left]
    ...                   = inner x x + inner x y + inner y (x+y)           : by rw[inner_add_right]
    ...                   = (inner x x + inner x y) + inner y (x+y)         : by simp,
  },
  conv at H
  begin
    to_rhs,
    congr, skip,
    rw inner_add_right,
  end,
  rw H,
  simp only [add_assoc],
end

/- Expand `inner (x - y) (x - y)` -/
lemma inner_sub_sub_self {x y : α} : inner (x - y) (x - y) = inner x x - inner x y - inner y x + inner y y :=
begin
  rw[sub_eq_add_neg, inner_add_add_self],
  simp only [inner_neg_neg, inner_neg_left, add_left_inj, inner_neg_right],
  rw[neg_neg, ←sub_eq_add_neg, ←sub_eq_add_neg],
end

/- Parallelogram law -/
lemma parallelogram_law {x y : α} :
  inner (x + y) (x + y) + inner (x - y) (x - y) = 2 * (inner x x + inner y y) :=
by simp [inner_add_add_self, inner_sub_sub_self, two_mul, sub_eq_add_neg, add_comm, add_left_comm]

/-
Cauchy–Schwarz inequality
Follows the second proof on Wikipedia
-/
lemma inner_mul_inner_self_le (x y : α) :
    (inner x y).abs * (inner y x).abs ≤ (inner x x).re * (inner y y).re :=
begin
  by_cases y_zero : inner y y = 0,
  --- first suppose ⟨y,y⟩ = 0:
  have hzero : y = 0,
    { exact inner_self_eq_zero.mp y_zero, },
  rw[hzero, inner_zero_left, inner_zero_right, complex.abs_zero,
      zero_mul, inner_zero_left, zero_re, mul_comm, zero_mul],
  --- now suppose ⟨y,y⟩ ≠ 0:
  change (inner y y) ≠ 0 at y_zero,
  have H_expr : ∀ (t : ℂ),
       inner (x - t•y) (x - t•y)
       = inner x x - t* (inner x y) - (conj t) * inner y x + t* (conj t) * inner y y,
  {
    intro t,
    calc
      inner (x - t•y) (x - t•y)
          = inner x x - inner x (t•y) - inner (t•y) x + inner (t•y) (t•y)
                : by rw[inner_sub_sub_self]
      ... = inner x x - t * inner x y - (conj t) * (inner y x) + t * inner (t•y) y
                : by rw[inner_smul_left, inner_smul_right, inner_smul_right]
      ... = inner x x - t * inner x y - (conj t) * (inner y x) + t* (conj t)* inner y y
                : by rw[inner_smul_left, mul_assoc],
  },
  have H_expr_inneryy : ∀ (t : ℂ),
       (inner y y) * inner (x - t•y) (x - t•y)
       = (inner y y) * inner x x
         - t* (inner y y) * (inner x y)
         - (conj t) * inner y y * inner y x
         + t*(conj t) * inner y y * inner y y,
  { intro t, rw[H_expr], ring, },
  -- Now choose a t to substitute:
  set T := (inner y x) / (inner y y) with Ht,
  set term1 := T * (inner y y)*(inner x y) with Hterm1,
  set term2 := (conj T) * (inner y y) * (inner y x) with Hterm2,
  set term3 := T * (conj T) * (inner y y) * (inner y y) with Hterm3,
  have H₁ : term1 = (inner y x) * (inner x y),
    { rw[Hterm1, Ht, div_mul_cancel (inner y x) y_zero], },
  have H₂ : term2 =  (inner y x) * (inner x y),
    {rw[Hterm2, conj_div, inner_self_conj, ←inner_conj_sym, div_mul_cancel (inner x y) y_zero, mul_comm] },
  have H₃ : term3 = (inner y x) * (inner x y),
  {
    rw[Hterm3, Ht, conj_div, inner_self_conj, ←inner_conj_sym, mul_assoc],
    rw[div_eq_mul_inv, div_eq_mul_inv],
    have H₄ : inner y x * (inner y y)⁻¹ * (inner x y * (inner y y)⁻¹) * (inner y y * inner y y)
                 = inner y x * inner x y * ((inner y y)⁻¹ * inner y y) * ((inner y y)⁻¹ * inner y y),
                 {ring},
    rw[H₄, inv_mul_cancel y_zero, mul_one, mul_one, mul_comm],
  },

  have H_step1 : (inner y y) * inner (x - T • y) (x - T • y)
        = (inner y y) * (inner x x) - term1 - term2 + term3,
    rw[Hterm1, Hterm2, Hterm3, H_expr_inneryy T],
  have H_key : (inner y y) * inner (x - T • y) (x - T • y)
      = (inner y y) * (inner x x) - inner y x * inner x y,
  {
    calc
    (inner y y) * inner (x - T • y) (x - T • y)
         = inner y y * inner x x - term1 - term2 + term3
                    : H_step1
    ...  = inner y y * inner x x - inner y x * inner x y
              - inner y x * inner x y + inner y x * inner x y
                    : by rw[H₁, H₂, H₃]
    ...  = inner y y * inner x x - inner y x * inner x y
                    : by ring,
  },
  have H_final : 0 ≤ ((inner y y) * inner (x - T • y) (x - T • y)).re,
  {
    rw [mul_re (inner y y) (inner (x - T • y)(x - T • y))],
    rw[inner_self_nonneg_im, inner_self_nonneg_im, mul_zero, sub_zero],
    have yynonneg : (inner y y).re ≥ 0, exact inner_self_nonneg,
    have bignonneg : (inner (x - T • y) (x - T • y)).re ≥ 0, exact inner_self_nonneg,
    exact mul_nonneg yynonneg bignonneg,
  },

  have H_split_re : (inner y y * inner x x).re  = (inner y y).re * (inner x x).re,
    { rw[mul_re, inner_self_nonneg_im, zero_mul, sub_zero] },
  have H_final_final : 0 ≤ (inner y y).re * (inner x x).re - (inner y x * inner x y).abs,
  {
    calc
    0   ≤ ((inner y y) * inner (x - T • y) (x - T • y)).re
                : H_final
    ... = (inner y y * inner x x - inner y x * inner x y).re
                : by rw[H_key]
    ... = (inner y y * inner x x).re - (inner y x * inner x y).re
                : by rw[sub_re]
    ... = (inner y y).re * (inner x x).re - (inner y x * inner x y).re
                : by rw[H_split_re]
    ... = (inner y y).re * (inner x x).re - (inner y x * inner x y).abs
                : by rw[inner_mul_conj_re_abs]
  },
  rw[←complex.abs_mul],
  conv
  begin
    to_rhs,
    rw[mul_comm],
  end,
  rw[mul_comm],
  linarith,
end

end basic_properties


/-! ### Complex inner product space structure on product spaces -/

/-
 If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space,
then `Π i, f i` is an inner product space as well. This is not an instance to avoid conflict
with the default instance for the norm on `Π i, f i`.
-/
instance pi_Lp.complex_inner_product_space {ι : Type*} [fintype ι] (f : ι → Type*)
  [Π i, complex_inner_product_space (f i)] : complex_inner_product_space (pi_Lp 2 one_le_two f) :=
{
  inner := λ x y, ∑ i, inner (x i) (y i),
  norm_eq_sqrt_inner :=
    begin
      assume x,
      unfold inner,
      have h₁ : ∀ (x : ℂ), x.re.sqrt = x.re^(1 / (2:ℝ)),
        intro y,
        rw[sqrt_eq_rpow],
      rw[pi_Lp.norm_eq, h₁],
      rw[←finset.sum_hom finset.univ re],
      have h₂ : ∀ (j : ι), (inner (x j) (x j)).re = ∥x j∥^2,
        intro j,
        rw[norm_eq_sqrt_inner, sqr_sqrt inner_self_nonneg],
      simp[h₂],
      congr',
      ext1,
      rw[←rpow_nat_cast],
      norm_cast,
    end,
  conj_sym :=
    begin
        intros x y,
        unfold inner,
        rw[←finset.sum_hom finset.univ complex.conj],
        apply finset.sum_congr, refl,
        intros z h,
        rw[inner_conj_sym],
    end,
  nonneg_im :=
    begin
      intro x,
      unfold inner,
      rw[←finset.sum_hom finset.univ complex.im],
      have H : ∀ i, (inner (x i) (x i)).im = 0,
        { intro i, exact inner_self_nonneg_im },
      apply finset.sum_eq_zero,
      intros z h,
      exact inner_self_nonneg_im,
    end,
  add_left := λ x y z,
    show ∑ i, inner (x i + y i) (z i) = ∑ i, inner (x i) (z i) + ∑ i, inner (y i) (z i),
    by simp only [inner_add_left, finset.sum_add_distrib],
  smul_left := λ x y r,
    show ∑ (i : ι), inner (r • x i) (y i) = (conj r) * ∑ i, inner (x i) (y i),
    by simp only [finset.mul_sum, inner_smul_left]
}

/-
The set of complex numbers is a complex inner product space.
-/
instance complex.complex_inner_product_space : complex_inner_product_space ℂ :=
{ inner := (λ x y, (conj x) * y),
  norm_eq_sqrt_inner :=
    by { intro x, rw[complex.conj_mul_re_eq_norm_sq_left], refl },
  conj_sym := assume x y,
    by {unfold inner, rw[conj_mul y.conj x, conj_conj, mul_comm]},
  nonneg_im :=
    begin
      intro x,
      unfold inner,
      rw[mul_im, conj_re, conj_im],
      ring,
    end,
  add_left := by { intros x y z, unfold inner, rw[conj_add], ring},
  smul_left :=
    begin
      intros x y z,
      unfold inner,
      simp only [complex.conj_mul, algebra.id.smul_eq_mul],
      ring,
    end
}


/-- The standard complex Euclidean space, functions on a finite type. For an `n`-dimensional space
use `complex_euclidean_space (fin n)`.  -/
@[reducible, nolint unused_arguments]
def complex_euclidean_space (n : Type*) [fintype n] : Type* := pi_Lp 2 one_le_two (λ (i : n), ℂ)

section pi_Lp
local attribute [reducible] pi_Lp
variables {ι : Type*} [fintype ι]

instance : finite_dimensional ℂ (complex_euclidean_space ι) := by apply_instance

@[simp] lemma findim_complex_euclidean_space :
  finite_dimensional.findim ℂ (complex_euclidean_space ι) = fintype.card ι := by simp

lemma findim_complex_euclidean_space_fin {n : ℕ} :
  finite_dimensional.findim ℂ (complex_euclidean_space (fin n)) = n := by simp

end pi_Lp


/-
Orthogonality: `x` and `y` are orthogonal if `⟨x,y⟩ = 0`.
-/

section orthogonal

variables {ι : Type*}

def is_orthogonal_set (v : ι → α) := ∀ i j : ι, i ≠ j → inner (v i) (v j) = 0

def is_normalized_set (v : ι → α) := ∀ i : ι, inner (v i) (v i) = 1

def is_orthonormal_set (v : ι → α) := is_orthogonal_set v ∧ is_normalized_set v

def is_orthonormal_basis (v : ι → α) := is_basis ℂ v ∧ is_orthonormal_set v

end orthogonal

end is_R_or_C
