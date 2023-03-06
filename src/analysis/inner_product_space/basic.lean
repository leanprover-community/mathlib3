/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
import algebra.direct_sum.module
import analysis.complex.basic
import analysis.convex.uniform
import analysis.normed_space.completion
import analysis.normed_space.bounded_linear_maps
import linear_algebra.bilinear_form

/-!
# Inner product space

This file defines inner product spaces and proves the basic properties.  We do not formally
define Hilbert spaces, but they can be obtained using the pair of assumptions
`[inner_product_space 𝕜 E] [complete_space E]`.

An inner product space is a vector space endowed with an inner product. It generalizes the notion of
dot product in `ℝ^n` and provides the means of defining the length of a vector and the angle between
two vectors. In particular vectors `x` and `y` are orthogonal if their inner product equals zero.
We define both the real and complex cases at the same time using the `is_R_or_C` typeclass.

This file proves general results on inner product spaces. For the specific construction of an inner
product structure on `n → 𝕜` for `𝕜 = ℝ` or `ℂ`, see `euclidean_space` in
`analysis.inner_product_space.pi_L2`.

## Main results

- We define the class `inner_product_space 𝕜 E` extending `normed_space 𝕜 E` with a number of basic
  properties, most notably the Cauchy-Schwarz inequality. Here `𝕜` is understood to be either `ℝ`
  or `ℂ`, through the `is_R_or_C` typeclass.
- We show that the inner product is continuous, `continuous_inner`, and bundle it as the
  the continuous sesquilinear map `innerSL` (see also `innerₛₗ` for the non-continuous version).
- We define `orthonormal`, a predicate on a function `v : ι → E`, and prove the existence of a
  maximal orthonormal set, `exists_maximal_orthonormal`.  Bessel's inequality,
  `orthonormal.tsum_inner_products_le`, states that given an orthonormal set `v` and a vector `x`,
  the sum of the norm-squares of the inner products `⟪v i, x⟫` is no more than the norm-square of
  `x`. For the existence of orthonormal bases, Hilbert bases, etc., see the file
  `analysis.inner_product_space.projection`.
- The `orthogonal_complement` of a submodule `K` is defined, and basic API established.  Some of
  the more subtle results about the orthogonal complement are delayed to
  `analysis.inner_product_space.projection`.

## Notation

We globally denote the real and complex inner products by `⟪·, ·⟫_ℝ` and `⟪·, ·⟫_ℂ` respectively.
We also provide two notation namespaces: `real_inner_product_space`, `complex_inner_product_space`,
which respectively introduce the plain notation `⟪·, ·⟫` for the real and complex inner product.

The orthogonal complement of a submodule `K` is denoted by `Kᗮ`.

## Implementation notes

We choose the convention that inner products are conjugate linear in the first argument and linear
in the second.

## Tags

inner product space, Hilbert space, norm

## References
*  [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
*  [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/

noncomputable theory

open is_R_or_C real filter
open_locale big_operators topology complex_conjugate

variables {𝕜 E F : Type*} [is_R_or_C 𝕜]

/-- Syntactic typeclass for types endowed with an inner product -/
class has_inner (𝕜 E : Type*) := (inner : E → E → 𝕜)

export has_inner (inner)

notation `⟪`x`, `y`⟫_ℝ` := @inner ℝ _ _ x y
notation `⟪`x`, `y`⟫_ℂ` := @inner ℂ _ _ x y

section notations

localized "notation (name := inner.real)
  `⟪`x`, `y`⟫` := @inner ℝ _ _ x y" in real_inner_product_space
localized "notation (name := inner.complex)
  `⟪`x`, `y`⟫` := @inner ℂ _ _ x y" in complex_inner_product_space

end notations

/--
An inner product space is a vector space with an additional operation called inner product.
The norm could be derived from the inner product, instead we require the existence of a norm and
the fact that `‖x‖^2 = re ⟪x, x⟫` to be able to put instances on `𝕂` or product
spaces.

To construct a norm from an inner product, see `inner_product_space.of_core`.
-/
class inner_product_space (𝕜 : Type*) (E : Type*) [is_R_or_C 𝕜]
  extends normed_add_comm_group E, normed_space 𝕜 E, has_inner 𝕜 E :=
(norm_sq_eq_inner : ∀ (x : E), ‖x‖^2 = re (inner x x))
(conj_sym  : ∀ x y, conj (inner y x) = inner x y)
(add_left  : ∀ x y z, inner (x + y) z = inner x z + inner y z)
(smul_left : ∀ x y r, inner (r • x) y = (conj r) * inner x y)

attribute [nolint dangerous_instance] inner_product_space.to_normed_add_comm_group
-- note [is_R_or_C instance]

/-!
### Constructing a normed space structure from an inner product

In the definition of an inner product space, we require the existence of a norm, which is equal
(but maybe not defeq) to the square root of the scalar product. This makes it possible to put
an inner product space structure on spaces with a preexisting norm (for instance `ℝ`), with good
properties. However, sometimes, one would like to define the norm starting only from a well-behaved
scalar product. This is what we implement in this paragraph, starting from a structure
`inner_product_space.core` stating that we have a nice scalar product.

Our goal here is not to develop a whole theory with all the supporting API, as this will be done
below for `inner_product_space`. Instead, we implement the bare minimum to go as directly as
possible to the construction of the norm and the proof of the triangular inequality.

Warning: Do not use this `core` structure if the space you are interested in already has a norm
instance defined on it, otherwise this will create a second non-defeq norm instance!
-/

/-- A structure requiring that a scalar product is positive definite and symmetric, from which one
can construct an `inner_product_space` instance in `inner_product_space.of_core`. -/
@[nolint has_nonempty_instance]
structure inner_product_space.core
  (𝕜 : Type*) (F : Type*)
  [is_R_or_C 𝕜] [add_comm_group F] [module 𝕜 F] :=
(inner     : F → F → 𝕜)
(conj_sym  : ∀ x y, conj (inner y x) = inner x y)
(nonneg_re : ∀ x, 0 ≤ re (inner x x))
(definite  : ∀ x, inner x x = 0 → x = 0)
(add_left  : ∀ x y z, inner (x + y) z = inner x z + inner y z)
(smul_left : ∀ x y r, inner (r • x) y = (conj r) * inner x y)

/- We set `inner_product_space.core` to be a class as we will use it as such in the construction
of the normed space structure that it produces. However, all the instances we will use will be
local to this proof. -/
attribute [class] inner_product_space.core

namespace inner_product_space.of_core

variables [add_comm_group F] [module 𝕜 F] [c : inner_product_space.core 𝕜 F]
include c

local notation `⟪`x`, `y`⟫` := @inner 𝕜 F _ x y
local notation `norm_sqK` := @is_R_or_C.norm_sq 𝕜 _
local notation `reK` := @is_R_or_C.re 𝕜 _
local notation `absK` := @is_R_or_C.abs 𝕜 _
local notation `ext_iff` := @is_R_or_C.ext_iff 𝕜 _
local postfix `†`:90 := star_ring_end _

/-- Inner product defined by the `inner_product_space.core` structure. -/
def to_has_inner : has_inner 𝕜 F := { inner := c.inner }
local attribute [instance] to_has_inner

/-- The norm squared function for `inner_product_space.core` structure. -/
def norm_sq (x : F) := reK ⟪x, x⟫

local notation `norm_sqF` := @norm_sq 𝕜 F _ _ _ _

lemma inner_conj_sym (x y : F) : ⟪y, x⟫† = ⟪x, y⟫ := c.conj_sym x y

lemma inner_self_nonneg {x : F} : 0 ≤ re ⟪x, x⟫ := c.nonneg_re _

lemma inner_self_nonneg_im {x : F} : im ⟪x, x⟫ = 0 :=
by rw [← @of_real_inj 𝕜, im_eq_conj_sub]; simp [inner_conj_sym]

lemma inner_self_im_zero {x : F} : im ⟪x, x⟫ = 0 :=
inner_self_nonneg_im

lemma inner_add_left {x y z : F} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
c.add_left _ _ _

lemma inner_add_right {x y z : F} : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ :=
by rw [←inner_conj_sym, inner_add_left, ring_hom.map_add]; simp only [inner_conj_sym]

lemma inner_norm_sq_eq_inner_self (x : F) : (norm_sqF x : 𝕜) = ⟪x, x⟫ :=
begin
  rw ext_iff,
  exact ⟨by simp only [of_real_re]; refl, by simp only [inner_self_nonneg_im, of_real_im]⟩
end

lemma inner_re_symm {x y : F} : re ⟪x, y⟫ = re ⟪y, x⟫ :=
by rw [←inner_conj_sym, conj_re]

lemma inner_im_symm {x y : F} : im ⟪x, y⟫ = -im ⟪y, x⟫ :=
by rw [←inner_conj_sym, conj_im]

lemma inner_smul_left {x y : F} {r : 𝕜} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
c.smul_left _ _ _

lemma inner_smul_right {x y : F} {r : 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_smul_left]; simp only [conj_conj, inner_conj_sym, ring_hom.map_mul]

lemma inner_zero_left {x : F} : ⟪0, x⟫ = 0 :=
by rw [←zero_smul 𝕜 (0 : F), inner_smul_left]; simp only [zero_mul, ring_hom.map_zero]

lemma inner_zero_right {x : F} : ⟪x, 0⟫ = 0 :=
by rw [←inner_conj_sym, inner_zero_left]; simp only [ring_hom.map_zero]

lemma inner_self_eq_zero {x : F} : ⟪x, x⟫ = 0 ↔ x = 0 :=
iff.intro (c.definite _) (by { rintro rfl, exact inner_zero_left })

lemma inner_self_re_to_K {x : F} : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
by norm_num [ext_iff, inner_self_nonneg_im]

lemma inner_abs_conj_sym {x y : F} : abs ⟪x, y⟫ = abs ⟪y, x⟫ :=
by rw [←inner_conj_sym, abs_conj]

lemma inner_neg_left {x y : F} : ⟪-x, y⟫ = -⟪x, y⟫ :=
by { rw [← neg_one_smul 𝕜 x, inner_smul_left], simp }

lemma inner_neg_right {x y : F} : ⟪x, -y⟫ = -⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_neg_left]; simp only [ring_hom.map_neg, inner_conj_sym]

lemma inner_sub_left {x y z : F} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_left, inner_neg_left] }

lemma inner_sub_right {x y z : F} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_right, inner_neg_right] }

lemma inner_mul_conj_re_abs {x y : F} : re (⟪x, y⟫ * ⟪y, x⟫) = abs (⟪x, y⟫ * ⟪y, x⟫) :=
by { rw [←inner_conj_sym, mul_comm], exact re_eq_abs_of_mul_conj (inner y x), }

/-- Expand `inner (x + y) (x + y)` -/
lemma inner_add_add_self {x y : F} : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_add_left, inner_add_right]; ring

/- Expand `inner (x - y) (x - y)` -/
lemma inner_sub_sub_self {x y : F} : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_sub_left, inner_sub_right]; ring

/--
**Cauchy–Schwarz inequality**. This proof follows "Proof 2" on Wikipedia.
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
    have h₄ : ⟪y, y⟫ = re ⟪y, y⟫ := by simp only [inner_self_re_to_K],
    have h₅ : re ⟪y, y⟫ > 0,
    { refine lt_of_le_of_ne inner_self_nonneg _,
      intro H,
      apply hy',
      rw ext_iff,
      exact ⟨by simp only [H, zero_re'],
             by simp only [inner_self_nonneg_im, add_monoid_hom.map_zero]⟩ },
    have h₆ : re ⟪y, y⟫ ≠ 0 := ne_of_gt h₅,
    have hmain := calc
      0   ≤ re ⟪x - T • y, x - T • y⟫
                  : inner_self_nonneg
      ... = re ⟪x, x⟫ - re ⟪T • y, x⟫ - re ⟪x, T • y⟫ + re ⟪T • y, T • y⟫
                  : by simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right, h₁, h₂,
                      neg_mul, add_monoid_hom.map_add, mul_re,
                      conj_im, add_monoid_hom.map_sub, mul_neg, conj_re, neg_neg]
      ... = re ⟪x, x⟫ - re (T† * ⟪y, x⟫) - re (T * ⟪x, y⟫) + re (T * T† * ⟪y, y⟫)
                  : by simp only [inner_smul_left, inner_smul_right, mul_assoc]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ / ⟪y, y⟫ * ⟪y, x⟫)
                  : by field_simp [-mul_re, inner_conj_sym, hT, map_div₀, h₁, h₃]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / ⟪y, y⟫)
                  : by rw ←mul_div_right_comm
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / re ⟪y, y⟫)
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

lemma norm_eq_sqrt_inner (x : F) : ‖x‖ = sqrt (re ⟪x, x⟫) := rfl

lemma inner_self_eq_norm_mul_norm (x : F) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ :=
by rw [norm_eq_sqrt_inner, ←sqrt_mul inner_self_nonneg (re ⟪x, x⟫),
  sqrt_mul_self inner_self_nonneg]

lemma sqrt_norm_sq_eq_norm {x : F} : sqrt (norm_sqF x) = ‖x‖ := rfl

/-- Cauchy–Schwarz inequality with norm -/
lemma abs_inner_le_norm (x y : F) : abs ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ :=
nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
begin
  have H : ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖) = re ⟪y, y⟫ * re ⟪x, x⟫,
  { simp only [inner_self_eq_norm_mul_norm], ring, },
  rw H,
  conv
  begin
    to_lhs, congr, rw [inner_abs_conj_sym],
  end,
  exact inner_mul_inner_self_le y x,
end

/-- Normed group structure constructed from an `inner_product_space.core` structure -/
def to_normed_add_comm_group : normed_add_comm_group F :=
add_group_norm.to_normed_add_comm_group
{ to_fun := λ x, sqrt (re ⟪x, x⟫),
  map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero],
  neg' := λ x, by simp only [inner_neg_left, neg_neg, inner_neg_right],
  add_le' := λ x y, begin
    have h₁ : abs ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := abs_inner_le_norm _ _,
    have h₂ : re ⟪x, y⟫ ≤ abs ⟪x, y⟫ := re_le_abs _,
    have h₃ : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := by linarith,
    have h₄ : re ⟪y, x⟫ ≤ ‖x‖ * ‖y‖ := by rwa [←inner_conj_sym, conj_re],
    have : ‖x + y‖ * ‖x + y‖ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖),
    { simp only [←inner_self_eq_norm_mul_norm, inner_add_add_self, mul_add, mul_comm, map_add],
      linarith },
    exact nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this,
  end,
  eq_zero_of_map_eq_zero' := λ x hx, (inner_self_eq_zero : ⟪x, x⟫ = 0 ↔ x = 0).1 $ begin
    change sqrt (re ⟪x, x⟫) = 0 at hx,
    rw [sqrt_eq_zero inner_self_nonneg] at hx,
    exact ext (by simp [hx]) (by simp [inner_self_im_zero]),
  end }

local attribute [instance] to_normed_add_comm_group

/-- Normed space structure constructed from a `inner_product_space.core` structure -/
def to_normed_space : normed_space 𝕜 F :=
{ norm_smul_le := assume r x,
  begin
    rw [norm_eq_sqrt_inner, inner_smul_left, inner_smul_right, ←mul_assoc],
    rw [conj_mul_eq_norm_sq_left, of_real_mul_re, sqrt_mul, ←inner_norm_sq_eq_inner_self,
        of_real_re],
    { simp [sqrt_norm_sq_eq_norm, is_R_or_C.sqrt_norm_sq_eq_norm] },
    { exact norm_sq_nonneg r }
  end }

end inner_product_space.of_core

/-- Given a `inner_product_space.core` structure on a space, one can use it to turn
the space into an inner product space, constructing the norm out of the inner product -/
def inner_product_space.of_core [add_comm_group F] [module 𝕜 F]
  (c : inner_product_space.core 𝕜 F) : inner_product_space 𝕜 F :=
begin
  letI : normed_add_comm_group F :=
    @inner_product_space.of_core.to_normed_add_comm_group 𝕜 F _ _ _ c,
  letI : normed_space 𝕜 F := @inner_product_space.of_core.to_normed_space 𝕜 F _ _ _ c,
  exact { norm_sq_eq_inner := λ x,
    begin
      have h₁ : ‖x‖^2 = (sqrt (re (c.inner x x))) ^ 2 := rfl,
      have h₂ : 0 ≤ re (c.inner x x) := inner_product_space.of_core.inner_self_nonneg,
      simp [h₁, sq_sqrt, h₂],
    end,
    ..c }
end

/-! ### Properties of inner product spaces -/

variables [inner_product_space 𝕜 E] [inner_product_space ℝ F]
variables [dec_E : decidable_eq E]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y
local notation `IK` := @is_R_or_C.I 𝕜 _
local notation `absR` := has_abs.abs
local notation `absK` := @is_R_or_C.abs 𝕜 _
local postfix `†`:90 := star_ring_end _

export inner_product_space (norm_sq_eq_inner)

section basic_properties

@[simp] lemma inner_conj_sym (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ := inner_product_space.conj_sym _ _
lemma real_inner_comm (x y : F) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := @inner_conj_sym ℝ _ _ _ x y

lemma inner_eq_zero_sym {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0 :=
⟨λ h, by simp [←inner_conj_sym, h], λ h, by simp [←inner_conj_sym, h]⟩

@[simp] lemma inner_self_nonneg_im {x : E} : im ⟪x, x⟫ = 0 :=
by rw [← @of_real_inj 𝕜, im_eq_conj_sub]; simp

lemma inner_self_im_zero {x : E} : im ⟪x, x⟫ = 0 := inner_self_nonneg_im

lemma inner_add_left {x y z : E} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
inner_product_space.add_left _ _ _

lemma inner_add_right {x y z : E} : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ :=
by { rw [←inner_conj_sym, inner_add_left, ring_hom.map_add], simp only [inner_conj_sym] }

lemma inner_re_symm {x y : E} : re ⟪x, y⟫ = re ⟪y, x⟫ :=
by rw [←inner_conj_sym, conj_re]

lemma inner_im_symm {x y : E} : im ⟪x, y⟫ = -im ⟪y, x⟫ :=
by rw [←inner_conj_sym, conj_im]

lemma inner_smul_left {x y : E} {r : 𝕜} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
inner_product_space.smul_left _ _ _
lemma real_inner_smul_left {x y : F} {r : ℝ} : ⟪r • x, y⟫_ℝ = r * ⟪x, y⟫_ℝ := inner_smul_left

lemma inner_smul_real_left {x y : E} {r : ℝ} : ⟪(r : 𝕜) • x, y⟫ = r • ⟪x, y⟫ :=
by { rw [inner_smul_left, conj_of_real, algebra.smul_def], refl }

lemma inner_smul_right {x y : E} {r : 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_smul_left, ring_hom.map_mul, conj_conj, inner_conj_sym]
lemma real_inner_smul_right {x y : F} {r : ℝ} : ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ := inner_smul_right

lemma inner_smul_real_right {x y : E} {r : ℝ} : ⟪x, (r : 𝕜) • y⟫ = r • ⟪x, y⟫ :=
by { rw [inner_smul_right, algebra.smul_def], refl }

/-- The inner product as a sesquilinear form.

Note that in the case `𝕜 = ℝ` this is a bilinear form. -/
@[simps]
def sesq_form_of_inner : E →ₗ[𝕜] E →ₗ⋆[𝕜] 𝕜 :=
linear_map.mk₂'ₛₗ (ring_hom.id 𝕜) (star_ring_end _)
  (λ x y, ⟪y, x⟫)
  (λ x y z, inner_add_right)
  (λ r x y, inner_smul_right)
  (λ x y z, inner_add_left)
  (λ r x y, inner_smul_left)

/-- The real inner product as a bilinear form. -/
@[simps]
def bilin_form_of_real_inner : bilin_form ℝ F :=
{ bilin := inner,
  bilin_add_left := λ x y z, inner_add_left,
  bilin_smul_left := λ a x y, inner_smul_left,
  bilin_add_right := λ x y z, inner_add_right,
  bilin_smul_right := λ a x y, inner_smul_right }

/-- An inner product with a sum on the left. -/
lemma sum_inner {ι : Type*} (s : finset ι) (f : ι → E) (x : E) :
  ⟪∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫ := (sesq_form_of_inner x).map_sum

/-- An inner product with a sum on the right. -/
lemma inner_sum {ι : Type*} (s : finset ι) (f : ι → E) (x : E) :
  ⟪x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫ := (linear_map.flip sesq_form_of_inner x).map_sum

/-- An inner product with a sum on the left, `finsupp` version. -/
lemma finsupp.sum_inner {ι : Type*} (l : ι →₀ 𝕜) (v : ι → E) (x : E) :
  ⟪l.sum (λ (i : ι) (a : 𝕜), a • v i), x⟫
  = l.sum (λ (i : ι) (a : 𝕜), (conj a) • ⟪v i, x⟫) :=
by { convert sum_inner l.support (λ a, l a • v a) x,
     simp only [inner_smul_left, finsupp.sum, smul_eq_mul] }

/-- An inner product with a sum on the right, `finsupp` version. -/
lemma finsupp.inner_sum {ι : Type*} (l : ι →₀ 𝕜) (v : ι → E) (x : E) :
  ⟪x, l.sum (λ (i : ι) (a : 𝕜), a • v i)⟫ = l.sum (λ (i : ι) (a : 𝕜), a • ⟪x, v i⟫) :=
by { convert inner_sum l.support (λ a, l a • v a) x,
     simp only [inner_smul_right, finsupp.sum, smul_eq_mul] }

lemma dfinsupp.sum_inner {ι : Type*} [dec : decidable_eq ι] {α : ι → Type*}
  [Π i, add_zero_class (α i)] [Π i (x : α i), decidable (x ≠ 0)]
  (f : Π i, α i → E) (l : Π₀ i, α i) (x : E) :
  ⟪l.sum f, x⟫ = l.sum (λ i a, ⟪f i a, x⟫) :=
by simp only [dfinsupp.sum, sum_inner, smul_eq_mul] {contextual := tt}

lemma dfinsupp.inner_sum {ι : Type*} [dec : decidable_eq ι] {α : ι → Type*}
  [Π i, add_zero_class (α i)] [Π i (x : α i), decidable (x ≠ 0)]
  (f : Π i, α i → E) (l : Π₀ i, α i) (x : E) :
  ⟪x, l.sum f⟫ = l.sum (λ i a, ⟪x, f i a⟫) :=
by simp only [dfinsupp.sum, inner_sum, smul_eq_mul] {contextual := tt}

@[simp] lemma inner_zero_left {x : E} : ⟪0, x⟫ = 0 :=
by rw [← zero_smul 𝕜 (0:E), inner_smul_left, ring_hom.map_zero, zero_mul]

lemma inner_re_zero_left {x : E} : re ⟪0, x⟫ = 0 :=
by simp only [inner_zero_left, add_monoid_hom.map_zero]

@[simp] lemma inner_zero_right {x : E} : ⟪x, 0⟫ = 0 :=
by rw [←inner_conj_sym, inner_zero_left, ring_hom.map_zero]

lemma inner_re_zero_right {x : E} : re ⟪x, 0⟫ = 0 :=
by simp only [inner_zero_right, add_monoid_hom.map_zero]

lemma inner_self_nonneg {x : E} : 0 ≤ re ⟪x, x⟫ :=
by rw [←norm_sq_eq_inner]; exact pow_nonneg (norm_nonneg x) 2
lemma real_inner_self_nonneg {x : F} : 0 ≤ ⟪x, x⟫_ℝ := @inner_self_nonneg ℝ F _ _ x

@[simp] lemma inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 :=
begin
  split,
  { intro h,
    have h₁ : re ⟪x, x⟫ = 0 :=
    by rw is_R_or_C.ext_iff at h; simp only [h.1, zero_re'],
    rw [←norm_sq_eq_inner x] at h₁,
    rw [←norm_eq_zero],
    exact pow_eq_zero h₁ },
  { rintro rfl,
    exact inner_zero_left }
end

@[simp] lemma inner_self_nonpos {x : E} : re ⟪x, x⟫ ≤ 0 ↔ x = 0 :=
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

lemma real_inner_self_nonpos {x : F} : ⟪x, x⟫_ℝ ≤ 0 ↔ x = 0 :=
by { have h := @inner_self_nonpos ℝ F _ _ x, simpa using h }

@[simp] lemma inner_self_re_to_K {x : E} : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
is_R_or_C.ext_iff.2 ⟨by simp only [of_real_re], by simp only [inner_self_nonneg_im, of_real_im]⟩

lemma inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ = (‖x‖ ^ 2 : 𝕜) :=
begin
  suffices : (is_R_or_C.re ⟪x, x⟫ : 𝕜) = ‖x‖ ^ 2,
  { simpa only [inner_self_re_to_K] using this },
  exact_mod_cast (norm_sq_eq_inner x).symm
end

lemma inner_self_re_abs {x : E} : re ⟪x, x⟫ = abs ⟪x, x⟫ :=
begin
  conv_rhs { rw [←inner_self_re_to_K] },
  symmetry,
  exact is_R_or_C.abs_of_nonneg inner_self_nonneg,
end

lemma inner_self_abs_to_K {x : E} : (absK ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
by { rw [←inner_self_re_abs], exact inner_self_re_to_K }

lemma real_inner_self_abs {x : F} : absR ⟪x, x⟫_ℝ = ⟪x, x⟫_ℝ :=
by { have h := @inner_self_abs_to_K ℝ F _ _ x, simpa using h }

lemma inner_abs_conj_sym {x y : E} : abs ⟪x, y⟫ = abs ⟪y, x⟫ :=
by rw [←inner_conj_sym, abs_conj]

@[simp] lemma inner_neg_left {x y : E} : ⟪-x, y⟫ = -⟪x, y⟫ :=
by { rw [← neg_one_smul 𝕜 x, inner_smul_left], simp }

@[simp] lemma inner_neg_right {x y : E} : ⟪x, -y⟫ = -⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_neg_left]; simp only [ring_hom.map_neg, inner_conj_sym]

lemma inner_neg_neg {x y : E} : ⟪-x, -y⟫ = ⟪x, y⟫ := by simp

@[simp] lemma inner_self_conj {x : E} : ⟪x, x⟫† = ⟪x, x⟫ :=
by rw [is_R_or_C.ext_iff]; exact ⟨by rw [conj_re], by rw [conj_im, inner_self_im_zero, neg_zero]⟩

lemma inner_sub_left {x y z : E} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_left] }

lemma inner_sub_right {x y z : E} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_right] }

lemma inner_mul_conj_re_abs {x y : E} : re (⟪x, y⟫ * ⟪y, x⟫) = abs (⟪x, y⟫ * ⟪y, x⟫) :=
by { rw [←inner_conj_sym, mul_comm], exact re_eq_abs_of_mul_conj (inner y x), }

/-- Expand `⟪x + y, x + y⟫` -/
lemma inner_add_add_self {x y : E} : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_add_left, inner_add_right]; ring

/-- Expand `⟪x + y, x + y⟫_ℝ` -/
lemma real_inner_add_add_self {x y : F} : ⟪x + y, x + y⟫_ℝ = ⟪x, x⟫_ℝ + 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ :=
begin
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [←inner_conj_sym]; refl,
  simp only [inner_add_add_self, this, add_left_inj],
  ring,
end

/- Expand `⟪x - y, x - y⟫` -/
lemma inner_sub_sub_self {x y : E} : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_sub_left, inner_sub_right]; ring

/-- Expand `⟪x - y, x - y⟫_ℝ` -/
lemma real_inner_sub_sub_self {x y : F} : ⟪x - y, x - y⟫_ℝ = ⟪x, x⟫_ℝ - 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ :=
begin
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [←inner_conj_sym]; refl,
  simp only [inner_sub_sub_self, this, add_left_inj],
  ring,
end

variable (𝕜)
include 𝕜

lemma ext_inner_left {x y : E} (h : ∀ v, ⟪v, x⟫ = ⟪v, y⟫) : x = y :=
by rw [←sub_eq_zero, ←inner_self_eq_zero, inner_sub_right, sub_eq_zero, h (x - y)]

lemma ext_inner_right {x y : E} (h : ∀ v, ⟪x, v⟫ = ⟪y, v⟫) : x = y :=
by rw [←sub_eq_zero, ←inner_self_eq_zero, inner_sub_left, sub_eq_zero, h (x - y)]

omit 𝕜
variable {𝕜}

/-- Parallelogram law -/
lemma parallelogram_law {x y : E} :
  ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫) :=
by simp [inner_add_add_self, inner_sub_sub_self, two_mul, sub_eq_add_neg, add_comm, add_left_comm]

/-- Cauchy–Schwarz inequality. This proof follows "Proof 2" on Wikipedia. -/
lemma inner_mul_inner_self_le (x y : E) : abs ⟪x, y⟫ * abs ⟪y, x⟫ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
begin
  by_cases hy : y = 0,
  { rw [hy], simp only [is_R_or_C.abs_zero, inner_zero_left, mul_zero, add_monoid_hom.map_zero] },
  { have hy' : ⟪y, y⟫ ≠ 0 := inner_self_eq_zero.not.2 hy,
    set T := ⟪y, x⟫ / ⟪y, y⟫ with hT,
    have h₁ : re ⟪y, x⟫ = re ⟪x, y⟫ := inner_re_symm,
    have h₂ : im ⟪y, x⟫ = -im ⟪x, y⟫ := inner_im_symm,
    have h₃ : ⟪y, x⟫ * ⟪x, y⟫ * ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = ⟪y, x⟫ * ⟪x, y⟫ / ⟪y, y⟫,
    { rw [mul_div_assoc],
      have : ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = 1 / ⟪y, y⟫ :=
        by rw [div_mul_eq_div_mul_one_div, div_self hy', one_mul],
      rw [this, div_eq_mul_inv, one_mul, ←div_eq_mul_inv] },
    have h₄ : ⟪y, y⟫ = re ⟪y, y⟫ := inner_self_re_to_K.symm,
    have h₅ : re ⟪y, y⟫ > 0,
    { refine lt_of_le_of_ne inner_self_nonneg _,
      intro H,
      apply hy',
      rw is_R_or_C.ext_iff,
      exact ⟨by simp only [H, zero_re'],
             by simp only [inner_self_nonneg_im, add_monoid_hom.map_zero]⟩ },
    have h₆ : re ⟪y, y⟫ ≠ 0 := ne_of_gt h₅,
    have hmain := calc
      0   ≤ re ⟪x - T • y, x - T • y⟫
                  : inner_self_nonneg
      ... = re ⟪x, x⟫ - re ⟪T • y, x⟫ - re ⟪x, T • y⟫ + re ⟪T • y, T • y⟫
                  : by simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right, h₁, h₂,
                      neg_mul, add_monoid_hom.map_add, conj_im,
                      add_monoid_hom.map_sub, mul_neg, conj_re, neg_neg, mul_re]
      ... = re ⟪x, x⟫ - re (T† * ⟪y, x⟫) - re (T * ⟪x, y⟫) + re (T * T† * ⟪y, y⟫)
                  : by simp only [inner_smul_left, inner_smul_right, mul_assoc]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ / ⟪y, y⟫ * ⟪y, x⟫)
                  : by simp only [map_div₀, h₃, inner_conj_sym, sub_add_cancel]
                    with field_simps {discharger := tactic.field_simp.ne_zero}
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / ⟪y, y⟫)
                  : by rw ←mul_div_right_comm
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / re ⟪y, y⟫)
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

/-- Cauchy–Schwarz inequality for real inner products. -/
lemma real_inner_mul_inner_self_le (x y : F) : ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ :=
begin
  have h₁ : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [←inner_conj_sym]; refl,
  have h₂ := @inner_mul_inner_self_le ℝ F _ _ x y,
  dsimp at h₂,
  have h₃ := abs_mul_abs_self ⟪x, y⟫_ℝ,
  rw [h₁] at h₂,
  simpa [h₃] using h₂,
end

/-- A family of vectors is linearly independent if they are nonzero
and orthogonal. -/
lemma linear_independent_of_ne_zero_of_inner_eq_zero {ι : Type*} {v : ι → E}
  (hz : ∀ i, v i ≠ 0) (ho : ∀ i j, i ≠ j → ⟪v i, v j⟫ = 0) : linear_independent 𝕜 v :=
begin
  rw linear_independent_iff',
  intros s g hg i hi,
  have h' : g i * inner (v i) (v i) = inner (v i) (∑ j in s, g j • v j),
  { rw inner_sum,
    symmetry,
    convert finset.sum_eq_single i _ _,
    { rw inner_smul_right },
    { intros j hj hji,
      rw [inner_smul_right, ho i j hji.symm, mul_zero] },
    { exact λ h, false.elim (h hi) } },
  simpa [hg, hz] using h'
end

end basic_properties

section orthonormal_sets
variables {ι : Type*} [dec_ι : decidable_eq ι] (𝕜)

include 𝕜

/-- An orthonormal set of vectors in an `inner_product_space` -/
def orthonormal (v : ι → E) : Prop :=
(∀ i, ‖v i‖ = 1) ∧ (∀ {i j}, i ≠ j → ⟪v i, v j⟫ = 0)

omit 𝕜

variables {𝕜}

include dec_ι
/-- `if ... then ... else` characterization of an indexed set of vectors being orthonormal.  (Inner
product equals Kronecker delta.) -/
lemma orthonormal_iff_ite {v : ι → E} :
  orthonormal 𝕜 v ↔ ∀ i j, ⟪v i, v j⟫ = if i = j then (1:𝕜) else (0:𝕜) :=
begin
  split,
  { intros hv i j,
    split_ifs,
    { simp [h, inner_self_eq_norm_sq_to_K, hv.1] },
    { exact hv.2 h } },
  { intros h,
    split,
    { intros i,
      have h' : ‖v i‖ ^ 2 = 1 ^ 2 := by simp [norm_sq_eq_inner, h i i],
      have h₁ : 0 ≤ ‖v i‖ := norm_nonneg _,
      have h₂ : (0:ℝ) ≤ 1 := zero_le_one,
      rwa sq_eq_sq h₁ h₂ at h' },
    { intros i j hij,
      simpa [hij] using h i j } }
end
omit dec_ι

include dec_E
/-- `if ... then ... else` characterization of a set of vectors being orthonormal.  (Inner product
equals Kronecker delta.) -/
theorem orthonormal_subtype_iff_ite {s : set E} :
  orthonormal 𝕜 (coe : s → E) ↔
  (∀ v ∈ s, ∀ w ∈ s, ⟪v, w⟫ = if v = w then 1 else 0) :=
begin
  rw orthonormal_iff_ite,
  split,
  { intros h v hv w hw,
    convert h ⟨v, hv⟩ ⟨w, hw⟩ using 1,
    simp },
  { rintros h ⟨v, hv⟩ ⟨w, hw⟩,
    convert h v hv w hw using 1,
    simp }
end
omit dec_E

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
lemma orthonormal.inner_right_finsupp {v : ι → E} (hv : orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) :
  ⟪v i, finsupp.total ι E 𝕜 v l⟫ = l i :=
by classical; simp [finsupp.total_apply, finsupp.inner_sum, orthonormal_iff_ite.mp hv]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
lemma orthonormal.inner_right_sum
  {v : ι → E} (hv : orthonormal 𝕜 v) (l : ι → 𝕜) {s : finset ι} {i : ι} (hi : i ∈ s) :
  ⟪v i, ∑ i in s, (l i) • (v i)⟫ = l i :=
by classical; simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp hv, hi]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
lemma orthonormal.inner_right_fintype [fintype ι]
  {v : ι → E} (hv : orthonormal 𝕜 v) (l : ι → 𝕜) (i : ι) :
  ⟪v i, ∑ i : ι, (l i) • (v i)⟫ = l i :=
hv.inner_right_sum l (finset.mem_univ _)

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
lemma orthonormal.inner_left_finsupp {v : ι → E} (hv : orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) :
  ⟪finsupp.total ι E 𝕜 v l, v i⟫ = conj (l i) :=
by rw [← inner_conj_sym, hv.inner_right_finsupp]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
lemma orthonormal.inner_left_sum
  {v : ι → E} (hv : orthonormal 𝕜 v) (l : ι → 𝕜) {s : finset ι} {i : ι} (hi : i ∈ s) :
  ⟪∑ i in s, (l i) • (v i), v i⟫ = conj (l i) :=
by classical; simp only
[sum_inner, inner_smul_left, orthonormal_iff_ite.mp hv, hi, mul_boole, finset.sum_ite_eq', if_true]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
lemma orthonormal.inner_left_fintype [fintype ι]
  {v : ι → E} (hv : orthonormal 𝕜 v) (l : ι → 𝕜) (i : ι) :
  ⟪∑ i : ι, (l i) • (v i), v i⟫ = conj (l i) :=
hv.inner_left_sum l (finset.mem_univ _)

/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum over the first `finsupp`. -/
lemma orthonormal.inner_finsupp_eq_sum_left
  {v : ι → E} (hv : orthonormal 𝕜 v) (l₁ l₂ : ι →₀ 𝕜) :
  ⟪finsupp.total ι E 𝕜 v l₁, finsupp.total ι E 𝕜 v l₂⟫ = l₁.sum (λ i y, conj y * l₂ i) :=
by simp only [l₁.total_apply _, finsupp.sum_inner, hv.inner_right_finsupp, smul_eq_mul]

/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum over the second `finsupp`. -/
lemma orthonormal.inner_finsupp_eq_sum_right
  {v : ι → E} (hv : orthonormal 𝕜 v) (l₁ l₂ : ι →₀ 𝕜) :
  ⟪finsupp.total ι E 𝕜 v l₁, finsupp.total ι E 𝕜 v l₂⟫ = l₂.sum (λ i y, conj (l₁ i) * y) :=
by simp only [l₂.total_apply _, finsupp.inner_sum, hv.inner_left_finsupp, mul_comm, smul_eq_mul]

/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum. -/
lemma orthonormal.inner_sum
  {v : ι → E} (hv : orthonormal 𝕜 v) (l₁ l₂ : ι → 𝕜) (s : finset ι) :
  ⟪∑ i in s, l₁ i • v i, ∑ i in s, l₂ i • v i⟫ = ∑ i in s, conj (l₁ i) * l₂ i :=
begin
  simp_rw [sum_inner, inner_smul_left],
  refine finset.sum_congr rfl (λ i hi, _),
  rw hv.inner_right_sum l₂ hi
end

/--
The double sum of weighted inner products of pairs of vectors from an orthonormal sequence is the
sum of the weights.
-/
lemma orthonormal.inner_left_right_finset {s : finset ι}  {v : ι → E} (hv : orthonormal 𝕜 v)
  {a : ι → ι → 𝕜} : ∑ i in s, ∑ j in s, (a i j) • ⟪v j, v i⟫ = ∑ k in s, a k k :=
by classical; simp [orthonormal_iff_ite.mp hv, finset.sum_ite_of_true]

/-- An orthonormal set is linearly independent. -/
lemma orthonormal.linear_independent {v : ι → E} (hv : orthonormal 𝕜 v) :
  linear_independent 𝕜 v :=
begin
  rw linear_independent_iff,
  intros l hl,
  ext i,
  have key : ⟪v i, finsupp.total ι E 𝕜 v l⟫ = ⟪v i, 0⟫ := by rw hl,
  simpa only [hv.inner_right_finsupp, inner_zero_right] using key
end

/-- A subfamily of an orthonormal family (i.e., a composition with an injective map) is an
orthonormal family. -/
lemma orthonormal.comp
  {ι' : Type*} {v : ι → E} (hv : orthonormal 𝕜 v) (f : ι' → ι) (hf : function.injective f) :
  orthonormal 𝕜 (v ∘ f) :=
begin
  classical,
  rw orthonormal_iff_ite at ⊢ hv,
  intros i j,
  convert hv (f i) (f j) using 1,
  simp [hf.eq_iff]
end

/-- An injective family `v : ι → E` is orthonormal if and only if `coe : (range v) → E` is
orthonormal. -/
lemma orthonormal_subtype_range {v : ι → E} (hv : function.injective v) :
  orthonormal 𝕜 (coe : set.range v → E) ↔ orthonormal 𝕜 v :=
begin
  let f : ι ≃ set.range v := equiv.of_injective v hv,
  refine ⟨λ h, h.comp f f.injective, λ h, _⟩,
  rw ← equiv.self_comp_of_injective_symm hv,
  exact h.comp f.symm f.symm.injective,
end

/-- If `v : ι → E` is an orthonormal family, then `coe : (range v) → E` is an orthonormal
family. -/
lemma orthonormal.to_subtype_range {v : ι → E} (hv : orthonormal 𝕜 v) :
  orthonormal 𝕜 (coe : set.range v → E) :=
(orthonormal_subtype_range hv.linear_independent.injective).2 hv

/-- A linear combination of some subset of an orthonormal set is orthogonal to other members of the
set. -/
lemma orthonormal.inner_finsupp_eq_zero
  {v : ι → E} (hv : orthonormal 𝕜 v) {s : set ι} {i : ι} (hi : i ∉ s) {l : ι →₀ 𝕜}
  (hl : l ∈ finsupp.supported 𝕜 𝕜 s) :
  ⟪finsupp.total ι E 𝕜 v l, v i⟫ = 0 :=
begin
  rw finsupp.mem_supported' at hl,
  simp only [hv.inner_left_finsupp, hl i hi, map_zero],
end

/-- Given an orthonormal family, a second family of vectors is orthonormal if every vector equals
the corresponding vector in the original family or its negation. -/
lemma orthonormal.orthonormal_of_forall_eq_or_eq_neg {v w : ι → E} (hv : orthonormal 𝕜 v)
  (hw : ∀ i, w i = v i ∨ w i = -(v i)) : orthonormal 𝕜 w :=
begin
  classical,
  rw orthonormal_iff_ite at *,
  intros i j,
  cases hw i with hi hi; cases hw j with hj hj; split_ifs with h;
  simpa only [hi, hj, h, inner_neg_right, inner_neg_left,
              neg_neg, eq_self_iff_true, neg_eq_zero] using hv i j
end

/- The material that follows, culminating in the existence of a maximal orthonormal subset, is
adapted from the corresponding development of the theory of linearly independents sets.  See
`exists_linear_independent` in particular. -/

variables (𝕜 E)
lemma orthonormal_empty : orthonormal 𝕜 (λ x, x : (∅ : set E) → E) :=
by classical; simp [orthonormal_subtype_iff_ite]
variables {𝕜 E}

lemma orthonormal_Union_of_directed
  {η : Type*} {s : η → set E} (hs : directed (⊆) s) (h : ∀ i, orthonormal 𝕜 (λ x, x : s i → E)) :
  orthonormal 𝕜 (λ x, x : (⋃ i, s i) → E) :=
begin
  classical,
  rw orthonormal_subtype_iff_ite,
  rintros x ⟨_, ⟨i, rfl⟩, hxi⟩ y ⟨_, ⟨j, rfl⟩, hyj⟩,
  obtain ⟨k, hik, hjk⟩ := hs i j,
  have h_orth : orthonormal 𝕜 (λ x, x : (s k) → E) := h k,
  rw orthonormal_subtype_iff_ite at h_orth,
  exact h_orth x (hik hxi) y (hjk hyj)
end

lemma orthonormal_sUnion_of_directed
  {s : set (set E)} (hs : directed_on (⊆) s)
  (h : ∀ a ∈ s, orthonormal 𝕜 (λ x, x : (a : set E) → E)) :
  orthonormal 𝕜 (λ x, x : (⋃₀ s) → E) :=
by rw set.sUnion_eq_Union; exact orthonormal_Union_of_directed hs.directed_coe (by simpa using h)

/-- Given an orthonormal set `v` of vectors in `E`, there exists a maximal orthonormal set
containing it. -/
lemma exists_maximal_orthonormal {s : set E} (hs : orthonormal 𝕜 (coe : s → E)) :
  ∃ w ⊇ s, orthonormal 𝕜 (coe : w → E) ∧ ∀ u ⊇ w, orthonormal 𝕜 (coe : u → E) → u = w :=
begin
  obtain ⟨b, bi, sb, h⟩ := zorn_subset_nonempty {b | orthonormal 𝕜 (coe : b → E)} _ _ hs,
  { refine ⟨b, sb, bi, _⟩,
    exact λ u hus hu, h u hu hus },
  { refine λ c hc cc c0, ⟨⋃₀ c, _, _⟩,
    { exact orthonormal_sUnion_of_directed cc.directed_on (λ x xc, hc xc) },
    { exact λ _, set.subset_sUnion_of_mem } }
end

lemma orthonormal.ne_zero {v : ι → E} (hv : orthonormal 𝕜 v) (i : ι) : v i ≠ 0 :=
begin
  have : ‖v i‖ ≠ 0,
  { rw hv.1 i,
    norm_num },
  simpa using this
end

open finite_dimensional

/-- A family of orthonormal vectors with the correct cardinality forms a basis. -/
def basis_of_orthonormal_of_card_eq_finrank [fintype ι] [nonempty ι] {v : ι → E}
  (hv : orthonormal 𝕜 v) (card_eq : fintype.card ι = finrank 𝕜 E) :
  basis ι 𝕜 E :=
basis_of_linear_independent_of_card_eq_finrank hv.linear_independent card_eq

@[simp] lemma coe_basis_of_orthonormal_of_card_eq_finrank [fintype ι] [nonempty ι] {v : ι → E}
  (hv : orthonormal 𝕜 v) (card_eq : fintype.card ι = finrank 𝕜 E) :
  (basis_of_orthonormal_of_card_eq_finrank hv card_eq : ι → E) = v :=
coe_basis_of_linear_independent_of_card_eq_finrank _ _

end orthonormal_sets

section norm

lemma norm_eq_sqrt_inner (x : E) : ‖x‖ = sqrt (re ⟪x, x⟫) :=
calc ‖x‖ = sqrt (‖x‖ ^ 2) : (sqrt_sq (norm_nonneg _)).symm
... = sqrt (re ⟪x, x⟫) : congr_arg _ (norm_sq_eq_inner _)

lemma norm_eq_sqrt_real_inner (x : F) : ‖x‖ = sqrt ⟪x, x⟫_ℝ :=
by { have h := @norm_eq_sqrt_inner ℝ F _ _ x, simpa using h }

lemma inner_self_eq_norm_mul_norm (x : E) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ :=
by rw [norm_eq_sqrt_inner, ←sqrt_mul inner_self_nonneg (re ⟪x, x⟫),
  sqrt_mul_self inner_self_nonneg]

lemma inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖^2 :=
by rw [pow_two, inner_self_eq_norm_mul_norm]

lemma real_inner_self_eq_norm_mul_norm (x : F) : ⟪x, x⟫_ℝ = ‖x‖ * ‖x‖ :=
by { have h := @inner_self_eq_norm_mul_norm ℝ F _ _ x, simpa using h }

lemma real_inner_self_eq_norm_sq (x : F) : ⟪x, x⟫_ℝ = ‖x‖^2 :=
by rw [pow_two, real_inner_self_eq_norm_mul_norm]

/-- Expand the square -/
lemma norm_add_sq {x y : E} : ‖x + y‖^2 = ‖x‖^2 + 2 * (re ⟪x, y⟫) + ‖y‖^2 :=
begin
  repeat {rw [sq, ←inner_self_eq_norm_mul_norm]},
  rw [inner_add_add_self, two_mul],
  simp only [add_assoc, add_left_inj, add_right_inj, add_monoid_hom.map_add],
  rw [←inner_conj_sym, conj_re],
end

alias norm_add_sq ← norm_add_pow_two

/-- Expand the square -/
lemma norm_add_sq_real {x y : F} : ‖x + y‖^2 = ‖x‖^2 + 2 * ⟪x, y⟫_ℝ + ‖y‖^2 :=
by { have h := @norm_add_sq ℝ F _ _, simpa using h }

alias norm_add_sq_real ← norm_add_pow_two_real

/-- Expand the square -/
lemma norm_add_mul_self {x y : E} : ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * (re ⟪x, y⟫) + ‖y‖ * ‖y‖ :=
by { repeat {rw [← sq]}, exact norm_add_sq }

/-- Expand the square -/
lemma norm_add_mul_self_real {x y : F} : ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * ⟪x, y⟫_ℝ + ‖y‖ * ‖y‖ :=
by { have h := @norm_add_mul_self ℝ F _ _, simpa using h }

/-- Expand the square -/
lemma norm_sub_sq {x y : E} : ‖x - y‖^2 = ‖x‖^2 - 2 * (re ⟪x, y⟫) + ‖y‖^2 :=
begin
  repeat {rw [sq, ←inner_self_eq_norm_mul_norm]},
  rw [inner_sub_sub_self],
  calc
    re (⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫)
        = re ⟪x, x⟫ - re ⟪x, y⟫ - re ⟪y, x⟫ + re ⟪y, y⟫  : by simp only [map_add, map_sub]
    ... = -re ⟪y, x⟫ - re ⟪x, y⟫ + re ⟪x, x⟫ + re ⟪y, y⟫  : by ring
    ... = -re (⟪x, y⟫†) - re ⟪x, y⟫ + re ⟪x, x⟫ + re ⟪y, y⟫ : by rw [inner_conj_sym]
    ... = -re ⟪x, y⟫ - re ⟪x, y⟫ + re ⟪x, x⟫ + re ⟪y, y⟫ : by rw [conj_re]
    ... = re ⟪x, x⟫ - 2*re ⟪x, y⟫ + re ⟪y, y⟫ : by ring
end

alias norm_sub_sq ← norm_sub_pow_two

/-- Expand the square -/
lemma norm_sub_sq_real {x y : F} : ‖x - y‖^2 = ‖x‖^2 - 2 * ⟪x, y⟫_ℝ + ‖y‖^2 :=
norm_sub_sq

alias norm_sub_sq_real ← norm_sub_pow_two_real

/-- Expand the square -/
lemma norm_sub_mul_self {x y : E} : ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖ :=
by { repeat {rw [← sq]}, exact norm_sub_sq }

/-- Expand the square -/
lemma norm_sub_mul_self_real {x y : F} : ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * ⟪x, y⟫_ℝ + ‖y‖ * ‖y‖ :=
by { have h := @norm_sub_mul_self ℝ F _ _, simpa using h }

/-- Cauchy–Schwarz inequality with norm -/
lemma abs_inner_le_norm (x y : E) : abs ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ :=
nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
begin
  have : ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖) = (re ⟪x, x⟫) * (re ⟪y, y⟫),
    simp only [inner_self_eq_norm_mul_norm], ring,
  rw this,
  conv_lhs { congr, skip, rw [inner_abs_conj_sym] },
  exact inner_mul_inner_self_le _ _
end

lemma norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ :=
(is_R_or_C.norm_eq_abs _).le.trans (abs_inner_le_norm x y)

lemma nnnorm_inner_le_nnnorm (x y : E) : ‖⟪x, y⟫‖₊ ≤ ‖x‖₊ * ‖y‖₊ :=
norm_inner_le_norm x y

lemma re_inner_le_norm (x y : E) : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ :=
le_trans (re_le_abs (inner x y)) (abs_inner_le_norm x y)

/-- Cauchy–Schwarz inequality with norm -/
lemma abs_real_inner_le_norm (x y : F) : absR ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖ :=
by { have h := @abs_inner_le_norm ℝ F _ _ x y, simpa using h }

/-- Cauchy–Schwarz inequality with norm -/
lemma real_inner_le_norm (x y : F) : ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖ :=
le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)

include 𝕜
lemma parallelogram_law_with_norm (x y : E) :
  ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) :=
begin
  simp only [← inner_self_eq_norm_mul_norm],
  rw [← re.map_add, parallelogram_law, two_mul, two_mul],
  simp only [re.map_add],
end

lemma parallelogram_law_with_nnnorm (x y : E) :
  ‖x + y‖₊ * ‖x + y‖₊ + ‖x - y‖₊ * ‖x - y‖₊ = 2 * (‖x‖₊ * ‖x‖₊ + ‖y‖₊ * ‖y‖₊) :=
subtype.ext $ parallelogram_law_with_norm x y

omit 𝕜

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
lemma re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : E) :
  re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 :=
by { rw norm_add_mul_self, ring }

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
lemma re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : E) :
  re ⟪x, y⟫ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2 :=
by { rw [norm_sub_mul_self], ring }

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
lemma re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (x y : E) :
  re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x - y‖ * ‖x - y‖) / 4 :=
by { rw [norm_add_mul_self, norm_sub_mul_self], ring }

/-- Polarization identity: The imaginary part of the inner product, in terms of the norm. -/
lemma im_inner_eq_norm_sub_I_smul_mul_self_sub_norm_add_I_smul_mul_self_div_four (x y : E) :
  im ⟪x, y⟫ = (‖x - IK • y‖ * ‖x - IK • y‖ - ‖x + IK • y‖ * ‖x + IK • y‖) / 4 :=
by { simp only [norm_add_mul_self, norm_sub_mul_self, inner_smul_right, I_mul_re], ring }

/-- Polarization identity: The inner product, in terms of the norm. -/
lemma inner_eq_sum_norm_sq_div_four (x y : E) :
  ⟪x, y⟫ = (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 + (‖x - IK • y‖ ^ 2 - ‖x + IK • y‖ ^ 2) * IK) / 4 :=
begin
  rw [← re_add_im ⟪x, y⟫, re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
    im_inner_eq_norm_sub_I_smul_mul_self_sub_norm_add_I_smul_mul_self_div_four],
  push_cast,
  simp only [sq, ← mul_div_right_comm, ← add_div]
end

/-- Formula for the distance between the images of two nonzero points under an inversion with center
zero. See also `euclidean_geometry.dist_inversion_inversion` for inversions around a general
point. -/
lemma dist_div_norm_sq_smul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (R : ℝ) :
  dist ((R / ‖x‖) ^ 2 • x) ((R / ‖y‖) ^ 2 • y) = (R ^ 2 / (‖x‖ * ‖y‖)) * dist x y :=
have hx' : ‖x‖ ≠ 0, from norm_ne_zero_iff.2 hx,
have hy' : ‖y‖ ≠ 0, from norm_ne_zero_iff.2 hy,
calc dist ((R / ‖x‖) ^ 2 • x) ((R / ‖y‖) ^ 2 • y)
    = sqrt (‖(R / ‖x‖) ^ 2 • x - (R / ‖y‖) ^ 2 • y‖^2) :
  by rw [dist_eq_norm, sqrt_sq (norm_nonneg _)]
... = sqrt ((R ^ 2 / (‖x‖ * ‖y‖)) ^ 2 * ‖x - y‖ ^ 2) :
  congr_arg sqrt $ by { field_simp [sq, norm_sub_mul_self_real, norm_smul, real_inner_smul_left,
    inner_smul_right, real.norm_of_nonneg (mul_self_nonneg _)], ring }
... = (R ^ 2 / (‖x‖ * ‖y‖)) * dist x y :
  by rw [sqrt_mul (sq_nonneg _), sqrt_sq (norm_nonneg _),
    sqrt_sq (div_nonneg (sq_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))), dist_eq_norm]

@[priority 100] -- See note [lower instance priority]
instance inner_product_space.to_uniform_convex_space : uniform_convex_space F :=
⟨λ ε hε, begin
  refine ⟨2 - sqrt (4 - ε^2), sub_pos_of_lt $ (sqrt_lt' zero_lt_two).2 _, λ x hx y hy hxy, _⟩,
  { norm_num,
    exact pow_pos hε _ },
  rw sub_sub_cancel,
  refine le_sqrt_of_sq_le _,
  rw [sq, eq_sub_iff_add_eq.2 (parallelogram_law_with_norm x y), ←sq (‖x - y‖), hx, hy],
  norm_num,
  exact pow_le_pow_of_le_left hε.le hxy _,
end⟩

section complex

variables {V : Type*}
[inner_product_space ℂ V]

/--
A complex polarization identity, with a linear map
-/
lemma inner_map_polarization (T : V →ₗ[ℂ] V) (x y : V):
  ⟪ T y, x ⟫_ℂ = (⟪T (x + y) , x + y⟫_ℂ - ⟪T (x - y) , x - y⟫_ℂ +
    complex.I * ⟪T (x + complex.I • y) , x + complex.I • y⟫_ℂ -
    complex.I * ⟪T (x - complex.I • y), x - complex.I • y ⟫_ℂ) / 4 :=
begin
  simp only [map_add, map_sub, inner_add_left, inner_add_right, linear_map.map_smul,
             inner_smul_left, inner_smul_right, complex.conj_I, ←pow_two, complex.I_sq,
             inner_sub_left, inner_sub_right, mul_add, ←mul_assoc, mul_neg, neg_neg,
             sub_neg_eq_add, one_mul, neg_one_mul, mul_sub, sub_sub],
  ring,
end

lemma inner_map_polarization' (T : V →ₗ[ℂ] V) (x y : V):
  ⟪ T x, y ⟫_ℂ = (⟪T (x + y) , x + y⟫_ℂ - ⟪T (x - y) , x - y⟫_ℂ -
    complex.I * ⟪T (x + complex.I • y) , x + complex.I • y⟫_ℂ +
    complex.I * ⟪T (x - complex.I • y), x - complex.I • y ⟫_ℂ) / 4 :=
begin
  simp only [map_add, map_sub, inner_add_left, inner_add_right, linear_map.map_smul,
             inner_smul_left, inner_smul_right, complex.conj_I, ←pow_two, complex.I_sq,
             inner_sub_left, inner_sub_right, mul_add, ←mul_assoc, mul_neg, neg_neg,
             sub_neg_eq_add, one_mul, neg_one_mul, mul_sub, sub_sub],
  ring,
end

/--
A linear map `T` is zero, if and only if the identity `⟪T x, x⟫_ℂ = 0` holds for all `x`.
-/
lemma inner_map_self_eq_zero (T : V →ₗ[ℂ] V) :
  (∀ (x : V), ⟪T x, x⟫_ℂ = 0) ↔ T = 0 :=
begin
  split,
  { intro hT,
    ext x,
    simp only [linear_map.zero_apply, ← inner_self_eq_zero, inner_map_polarization, hT],
    norm_num },
  { rintro rfl x,
    simp only [linear_map.zero_apply, inner_zero_left] }
end

/--
Two linear maps `S` and `T` are equal, if and only if the identity `⟪S x, x⟫_ℂ = ⟪T x, x⟫_ℂ` holds
for all `x`.
-/
lemma ext_inner_map (S T : V →ₗ[ℂ] V) :
  (∀ (x : V), ⟪S x, x⟫_ℂ = ⟪T x, x⟫_ℂ) ↔ S = T :=
begin
  rw [←sub_eq_zero, ←inner_map_self_eq_zero],
  refine forall_congr (λ x, _),
  rw [linear_map.sub_apply, inner_sub_left, sub_eq_zero],
end

end complex

section

variables {ι : Type*} {ι' : Type*} {ι'' : Type*}
variables {E' : Type*} [inner_product_space 𝕜 E']
variables {E'' : Type*} [inner_product_space 𝕜 E'']

/-- A linear isometry preserves the inner product. -/
@[simp] lemma linear_isometry.inner_map_map (f : E →ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ :=
by simp [inner_eq_sum_norm_sq_div_four, ← f.norm_map]

/-- A linear isometric equivalence preserves the inner product. -/
@[simp] lemma linear_isometry_equiv.inner_map_map (f : E ≃ₗᵢ[𝕜] E') (x y : E) :
  ⟪f x, f y⟫ = ⟪x, y⟫ :=
f.to_linear_isometry.inner_map_map x y

/-- A linear map that preserves the inner product is a linear isometry. -/
def linear_map.isometry_of_inner (f : E →ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E →ₗᵢ[𝕜] E' :=
⟨f, λ x, by simp only [norm_eq_sqrt_inner, h]⟩

@[simp] lemma linear_map.coe_isometry_of_inner (f : E →ₗ[𝕜] E') (h) :
  ⇑(f.isometry_of_inner h) = f := rfl

@[simp] lemma linear_map.isometry_of_inner_to_linear_map (f : E →ₗ[𝕜] E') (h) :
  (f.isometry_of_inner h).to_linear_map = f := rfl

/-- A linear equivalence that preserves the inner product is a linear isometric equivalence. -/
def linear_equiv.isometry_of_inner (f : E ≃ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) :
  E ≃ₗᵢ[𝕜] E' :=
⟨f, ((f : E →ₗ[𝕜] E').isometry_of_inner h).norm_map⟩

@[simp] lemma linear_equiv.coe_isometry_of_inner (f : E ≃ₗ[𝕜] E') (h) :
  ⇑(f.isometry_of_inner h) = f := rfl

@[simp] lemma linear_equiv.isometry_of_inner_to_linear_equiv (f : E ≃ₗ[𝕜] E') (h) :
  (f.isometry_of_inner h).to_linear_equiv = f := rfl

/-- A linear isometry preserves the property of being orthonormal. -/
lemma linear_isometry.orthonormal_comp_iff {v : ι → E} (f : E →ₗᵢ[𝕜] E') :
  orthonormal 𝕜 (f ∘ v) ↔ orthonormal 𝕜 v :=
begin
  classical,
  simp_rw [orthonormal_iff_ite, linear_isometry.inner_map_map]
end

/-- A linear isometry preserves the property of being orthonormal. -/
lemma orthonormal.comp_linear_isometry {v : ι → E} (hv : orthonormal 𝕜 v) (f : E →ₗᵢ[𝕜] E') :
  orthonormal 𝕜 (f ∘ v) :=
by rwa f.orthonormal_comp_iff

/-- A linear isometric equivalence preserves the property of being orthonormal. -/
lemma orthonormal.comp_linear_isometry_equiv {v : ι → E} (hv : orthonormal 𝕜 v) (f : E ≃ₗᵢ[𝕜] E') :
  orthonormal 𝕜 (f ∘ v) :=
hv.comp_linear_isometry f.to_linear_isometry

/-- A linear isometric equivalence, applied with `basis.map`, preserves the property of being
orthonormal. -/
lemma orthonormal.map_linear_isometry_equiv {v : basis ι 𝕜 E} (hv : orthonormal 𝕜 v)
  (f : E ≃ₗᵢ[𝕜] E') : orthonormal 𝕜 (v.map f.to_linear_equiv) :=
hv.comp_linear_isometry_equiv f

/-- A linear map that sends an orthonormal basis to orthonormal vectors is a linear isometry. -/
def linear_map.isometry_of_orthonormal (f : E →ₗ[𝕜] E') {v : basis ι 𝕜 E} (hv : orthonormal 𝕜 v)
  (hf : orthonormal 𝕜 (f ∘ v)) : E →ₗᵢ[𝕜] E' :=
f.isometry_of_inner $ λ x y, by rw [←v.total_repr x, ←v.total_repr y, finsupp.apply_total,
                                    finsupp.apply_total, hv.inner_finsupp_eq_sum_left,
                                    hf.inner_finsupp_eq_sum_left]

@[simp] lemma linear_map.coe_isometry_of_orthonormal (f : E →ₗ[𝕜] E') {v : basis ι 𝕜 E}
  (hv : orthonormal 𝕜 v) (hf : orthonormal 𝕜 (f ∘ v)) :
  ⇑(f.isometry_of_orthonormal hv hf) = f :=
rfl

@[simp] lemma linear_map.isometry_of_orthonormal_to_linear_map (f : E →ₗ[𝕜] E') {v : basis ι 𝕜 E}
  (hv : orthonormal 𝕜 v) (hf : orthonormal 𝕜 (f ∘ v)) :
  (f.isometry_of_orthonormal hv hf).to_linear_map = f :=
rfl

/-- A linear equivalence that sends an orthonormal basis to orthonormal vectors is a linear
isometric equivalence. -/
def linear_equiv.isometry_of_orthonormal (f : E ≃ₗ[𝕜] E') {v : basis ι 𝕜 E} (hv : orthonormal 𝕜 v)
  (hf : orthonormal 𝕜 (f ∘ v)) : E ≃ₗᵢ[𝕜] E' :=
f.isometry_of_inner $ λ x y, begin
  rw ←linear_equiv.coe_coe at hf,
  rw [←v.total_repr x, ←v.total_repr y, ←linear_equiv.coe_coe, finsupp.apply_total,
      finsupp.apply_total, hv.inner_finsupp_eq_sum_left, hf.inner_finsupp_eq_sum_left]
end

@[simp] lemma linear_equiv.coe_isometry_of_orthonormal (f : E ≃ₗ[𝕜] E') {v : basis ι 𝕜 E}
  (hv : orthonormal 𝕜 v) (hf : orthonormal 𝕜 (f ∘ v)) :
  ⇑(f.isometry_of_orthonormal hv hf) = f :=
rfl

@[simp] lemma linear_equiv.isometry_of_orthonormal_to_linear_equiv (f : E ≃ₗ[𝕜] E')
  {v : basis ι 𝕜 E} (hv : orthonormal 𝕜 v) (hf : orthonormal 𝕜 (f ∘ v)) :
  (f.isometry_of_orthonormal hv hf).to_linear_equiv = f :=
rfl

/-- A linear isometric equivalence that sends an orthonormal basis to a given orthonormal basis. -/
def orthonormal.equiv {v : basis ι 𝕜 E} (hv : orthonormal 𝕜 v) {v' : basis ι' 𝕜 E'}
  (hv' : orthonormal 𝕜 v') (e : ι ≃ ι') : E ≃ₗᵢ[𝕜] E' :=
(v.equiv v' e).isometry_of_orthonormal hv begin
  have h : (v.equiv v' e) ∘ v = v' ∘ e,
  { ext i,
    simp },
  rw h,
  exact hv'.comp _ e.injective
end

@[simp] lemma orthonormal.equiv_to_linear_equiv {v : basis ι 𝕜 E} (hv : orthonormal 𝕜 v)
  {v' : basis ι' 𝕜 E'} (hv' : orthonormal 𝕜 v') (e : ι ≃ ι') :
  (hv.equiv hv' e).to_linear_equiv = v.equiv v' e :=
rfl

@[simp] lemma orthonormal.equiv_apply {ι' : Type*} {v : basis ι 𝕜 E} (hv : orthonormal 𝕜 v)
  {v' : basis ι' 𝕜 E'} (hv' : orthonormal 𝕜 v') (e : ι ≃ ι') (i : ι) :
  hv.equiv hv' e (v i) = v' (e i) :=
basis.equiv_apply _ _ _ _

@[simp] lemma orthonormal.equiv_refl {v : basis ι 𝕜 E} (hv : orthonormal 𝕜 v) :
  hv.equiv hv (equiv.refl ι) = linear_isometry_equiv.refl 𝕜 E :=
v.ext_linear_isometry_equiv $ λ i,
  by simp only [orthonormal.equiv_apply, equiv.coe_refl, id.def, linear_isometry_equiv.coe_refl]

@[simp] lemma orthonormal.equiv_symm {v : basis ι 𝕜 E} (hv : orthonormal 𝕜 v) {v' : basis ι' 𝕜 E'}
  (hv' : orthonormal 𝕜 v') (e : ι ≃ ι') : (hv.equiv hv' e).symm = hv'.equiv hv e.symm :=
v'.ext_linear_isometry_equiv $ λ i, (hv.equiv hv' e).injective $
  by simp only [linear_isometry_equiv.apply_symm_apply, orthonormal.equiv_apply, e.apply_symm_apply]

@[simp] lemma orthonormal.equiv_trans {v : basis ι 𝕜 E} (hv : orthonormal 𝕜 v) {v' : basis ι' 𝕜 E'}
  (hv' : orthonormal 𝕜 v') (e : ι ≃ ι') {v'' : basis ι'' 𝕜 E''} (hv'' : orthonormal 𝕜 v'')
  (e' : ι' ≃ ι'') : (hv.equiv hv' e).trans (hv'.equiv hv'' e') = hv.equiv hv'' (e.trans e') :=
v.ext_linear_isometry_equiv $ λ i,
  by simp only [linear_isometry_equiv.trans_apply, orthonormal.equiv_apply, e.coe_trans]

lemma orthonormal.map_equiv {v : basis ι 𝕜 E} (hv : orthonormal 𝕜 v) {v' : basis ι' 𝕜 E'}
  (hv' : orthonormal 𝕜 v') (e : ι ≃ ι') :
  v.map ((hv.equiv hv' e).to_linear_equiv) = v'.reindex e.symm :=
v.map_equiv _ _

end

/-- Polarization identity: The real inner product, in terms of the norm. -/
lemma real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : F) :
  ⟪x, y⟫_ℝ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 :=
re_to_real.symm.trans $
  re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y

/-- Polarization identity: The real inner product, in terms of the norm. -/
lemma real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : F) :
  ⟪x, y⟫_ℝ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2 :=
re_to_real.symm.trans $
  re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y

/-- Pythagorean theorem, if-and-only-if vector inner product form. -/
lemma norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
  ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ = 0 :=
begin
  rw [norm_add_mul_self, add_right_cancel_iff, add_right_eq_self, mul_eq_zero],
  norm_num
end

/-- Pythagorean theorem, if-and-if vector inner product form using square roots. -/
lemma norm_add_eq_sqrt_iff_real_inner_eq_zero {x y : F} :
  ‖x + y‖ = sqrt (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_ℝ = 0 :=
by rw [←norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, eq_comm,
  sqrt_eq_iff_mul_self_eq (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (norm_nonneg _)]

/-- Pythagorean theorem, vector inner product form. -/
lemma norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ = 0) :
  ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
begin
  rw [norm_add_mul_self, add_right_cancel_iff, add_right_eq_self, mul_eq_zero],
  apply or.inr,
  simp only [h, zero_re'],
end

/-- Pythagorean theorem, vector inner product form. -/
lemma norm_add_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
  ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
(norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector
inner product form. -/
lemma norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
  ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ = 0 :=
begin
  rw [norm_sub_mul_self, add_right_cancel_iff, sub_eq_add_neg, add_right_eq_self, neg_eq_zero,
      mul_eq_zero],
  norm_num
end

/-- Pythagorean theorem, subtracting vectors, if-and-if vector inner product form using square
roots. -/
lemma norm_sub_eq_sqrt_iff_real_inner_eq_zero {x y : F} :
  ‖x - y‖ = sqrt (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_ℝ = 0 :=
by rw [←norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, eq_comm,
  sqrt_eq_iff_mul_self_eq (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (norm_nonneg _)]

/-- Pythagorean theorem, subtracting vectors, vector inner product
form. -/
lemma norm_sub_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
  ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
(norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

/-- The sum and difference of two vectors are orthogonal if and only
if they have the same norm. -/
lemma real_inner_add_sub_eq_zero_iff (x y : F) : ⟪x + y, x - y⟫_ℝ = 0 ↔ ‖x‖ = ‖y‖ :=
begin
  conv_rhs { rw ←mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _) },
  simp only [←inner_self_eq_norm_mul_norm, inner_add_left, inner_sub_right,
            real_inner_comm y x, sub_eq_zero, re_to_real],
  split,
  { intro h,
    rw [add_comm] at h,
    linarith },
  { intro h,
    linarith }
end

/-- Given two orthogonal vectors, their sum and difference have equal norms. -/
lemma norm_sub_eq_norm_add {v w : E} (h : ⟪v, w⟫ = 0) : ‖w - v‖ = ‖w + v‖ :=
begin
  rw ←mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _),
  simp only [h, ←inner_self_eq_norm_mul_norm, sub_neg_eq_add, sub_zero, map_sub, zero_re', zero_sub,
    add_zero, map_add, inner_add_right, inner_sub_left, inner_sub_right, inner_re_symm, zero_add]
end

/-- The real inner product of two vectors, divided by the product of their
norms, has absolute value at most 1. -/
lemma abs_real_inner_div_norm_mul_norm_le_one (x y : F) : absR (⟪x, y⟫_ℝ / (‖x‖ * ‖y‖)) ≤ 1 :=
begin
  rw _root_.abs_div,
  by_cases h : 0 = absR (‖x‖ * ‖y‖),
  { rw [←h, div_zero],
    norm_num },
  { change 0 ≠ absR (‖x‖ * ‖y‖) at h,
    rw div_le_iff' (lt_of_le_of_ne (ge_iff_le.mp (_root_.abs_nonneg (‖x‖ * ‖y‖))) h),
    convert abs_real_inner_le_norm x y using 1,
    rw [_root_.abs_mul, _root_.abs_of_nonneg (norm_nonneg x), _root_.abs_of_nonneg (norm_nonneg y),
        mul_one] }
end

/-- The inner product of a vector with a multiple of itself. -/
lemma real_inner_smul_self_left (x : F) (r : ℝ) : ⟪r • x, x⟫_ℝ = r * (‖x‖ * ‖x‖) :=
by rw [real_inner_smul_left, ←real_inner_self_eq_norm_mul_norm]

/-- The inner product of a vector with a multiple of itself. -/
lemma real_inner_smul_self_right (x : F) (r : ℝ) : ⟪x, r • x⟫_ℝ = r * (‖x‖ * ‖x‖) :=
by rw [inner_smul_right, ←real_inner_self_eq_norm_mul_norm]

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
lemma abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
  {x : E} {r : 𝕜} (hx : x ≠ 0) (hr : r ≠ 0) : abs ⟪x, r • x⟫ / (‖x‖ * ‖r • x‖) = 1 :=
begin
  have hx' : ‖x‖ ≠ 0 := by simp [norm_eq_zero, hx],
  have hr' : abs r ≠ 0 := by simp [is_R_or_C.abs_eq_zero, hr],
  rw [inner_smul_right, is_R_or_C.abs_mul, ←inner_self_re_abs, inner_self_eq_norm_mul_norm,
      norm_smul],
  rw [is_R_or_C.norm_eq_abs, ←mul_assoc, ←div_div, mul_div_cancel _ hx',
     ←div_div, mul_comm, mul_div_cancel _ hr', div_self hx'],
end

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
lemma abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
  {x : F} {r : ℝ} (hx : x ≠ 0) (hr : r ≠ 0) : absR ⟪x, r • x⟫_ℝ / (‖x‖ * ‖r • x‖) = 1 :=
begin
  rw ← abs_to_real,
  exact abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr
end

/-- The inner product of a nonzero vector with a positive multiple of
itself, divided by the product of their norms, has value 1. -/
lemma real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul
  {x : F} {r : ℝ} (hx : x ≠ 0) (hr : 0 < r) : ⟪x, r • x⟫_ℝ / (‖x‖ * ‖r • x‖) = 1 :=
begin
  rw [real_inner_smul_self_right, norm_smul, real.norm_eq_abs, ←mul_assoc ‖x‖, mul_comm _ (absR r),
      mul_assoc, _root_.abs_of_nonneg (le_of_lt hr), div_self],
  exact mul_ne_zero (ne_of_gt hr)
    (λ h, hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero h)))
end

/-- The inner product of a nonzero vector with a negative multiple of
itself, divided by the product of their norms, has value -1. -/
lemma real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul
  {x : F} {r : ℝ} (hx : x ≠ 0) (hr : r < 0) : ⟪x, r • x⟫_ℝ / (‖x‖ * ‖r • x‖) = -1 :=
begin
  rw [real_inner_smul_self_right, norm_smul, real.norm_eq_abs, ←mul_assoc ‖x‖, mul_comm _ (absR r),
      mul_assoc, abs_of_neg hr, neg_mul, div_neg_eq_neg_div, div_self],
  exact mul_ne_zero (ne_of_lt hr)
    (λ h, hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero h)))
end

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
lemma abs_inner_div_norm_mul_norm_eq_one_iff (x y : E) :
  abs (⟪x, y⟫ / (‖x‖ * ‖y‖)) = 1 ↔ (x ≠ 0 ∧ ∃ (r : 𝕜), r ≠ 0 ∧ y = r • x) :=
begin
  split,
  { intro h,
    have hx0 : x ≠ 0,
    { intro hx0,
      rw [hx0, inner_zero_left, zero_div] at h,
      norm_num at h, },
    refine and.intro hx0 _,
    set r := ⟪x, y⟫ / (‖x‖ * ‖x‖) with hr,
    use r,
    set t := y - r • x with ht,
    have ht0 : ⟪x, t⟫ = 0,
    { rw [ht, inner_sub_right, inner_smul_right, hr],
      norm_cast,
      rw [←inner_self_eq_norm_mul_norm, inner_self_re_to_K,
          div_mul_cancel _ (λ h, hx0 (inner_self_eq_zero.1 h)), sub_self] },
    replace h : ‖r • x‖ / ‖t + r • x‖ = 1,
    { rw [←sub_add_cancel y (r • x), ←ht, inner_add_right, ht0, zero_add, inner_smul_right,
        is_R_or_C.abs_div, is_R_or_C.abs_mul, ←inner_self_re_abs,
        inner_self_eq_norm_mul_norm] at h,
      norm_cast at h,
      rwa [_root_.abs_mul, abs_norm_eq_norm, abs_norm_eq_norm, ←mul_assoc, mul_comm,
        mul_div_mul_left _ _ (λ h, hx0 (norm_eq_zero.1 h)), ←is_R_or_C.norm_eq_abs,
        ←norm_smul] at h },
    have hr0 : r ≠ 0,
    { intro hr0,
      rw [hr0, zero_smul, norm_zero, zero_div] at h,
      norm_num at h },
    refine and.intro hr0 _,
    have h2 : ‖r • x‖ ^ 2 = ‖t + r • x‖ ^ 2,
    { rw [eq_of_div_eq_one h] },
    replace h2 : ⟪r • x, r • x⟫ = ⟪t, t⟫ + ⟪t, r • x⟫ + ⟪r • x, t⟫ + ⟪r • x, r • x⟫,
    { rw [sq, sq, ←inner_self_eq_norm_mul_norm, ←inner_self_eq_norm_mul_norm ] at h2,
      have h2' := congr_arg (λ z : ℝ, (z : 𝕜)) h2,
      simp_rw [inner_self_re_to_K, inner_add_add_self] at h2',
      exact h2' },
    conv at h2 in ⟪r • x, t⟫ { rw [inner_smul_left, ht0, mul_zero] },
    symmetry' at h2,
    have h₁ : ⟪t, r • x⟫ = 0 := by { rw [inner_smul_right, ←inner_conj_sym, ht0], simp },
    rw [add_zero, h₁, add_left_eq_self, add_zero, inner_self_eq_zero] at h2,
    rw h2 at ht,
    exact eq_of_sub_eq_zero ht.symm },
  { intro h,
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    rw [hy, is_R_or_C.abs_div],
    norm_cast,
    rw [_root_.abs_mul, abs_norm_eq_norm, abs_norm_eq_norm],
    exact abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr }
end

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
lemma abs_real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
  absR (⟪x, y⟫_ℝ / (‖x‖ * ‖y‖)) = 1 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), r ≠ 0 ∧ y = r • x) :=
begin
  have := @abs_inner_div_norm_mul_norm_eq_one_iff ℝ F _ _ x y,
  simpa [coe_real_eq_id] using this,
end

/--
If the inner product of two vectors is equal to the product of their norms, then the two vectors
are multiples of each other. One form of the equality case for Cauchy-Schwarz.
Compare `inner_eq_norm_mul_iff`, which takes the stronger hypothesis `⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
lemma abs_inner_eq_norm_iff (x y : E) (hx0 : x ≠ 0) (hy0 : y ≠ 0):
  abs ⟪x, y⟫ = ‖x‖ * ‖y‖ ↔ ∃ (r : 𝕜), r ≠ 0 ∧ y = r • x :=
begin
  have hxy0 : ‖x‖ * ‖y‖ ≠ 0 := mul_ne_zero (norm_eq_zero.not.2 hx0) (norm_eq_zero.not.2 hy0),
  have h₁ : abs ⟪x, y⟫ = ‖x‖ * ‖y‖ ↔ abs (⟪x, y⟫ / (‖x‖ * ‖y‖)) = 1,
  { rw [←algebra_map.coe_mul, is_R_or_C.abs_div, is_R_or_C.abs_of_nonneg, div_eq_one_iff_eq hxy0],
    positivity },
  rw [h₁, abs_inner_div_norm_mul_norm_eq_one_iff x y],
  exact and_iff_right hx0,
end

/-- The inner product of two vectors, divided by the product of their
norms, has value 1 if and only if they are nonzero and one is
a positive multiple of the other. -/
lemma real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
  ⟪x, y⟫_ℝ / (‖x‖ * ‖y‖) = 1 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), 0 < r ∧ y = r • x) :=
begin
  split,
  { intro h,
    have ha := h,
    apply_fun absR at ha,
    norm_num at ha,
    rcases (abs_real_inner_div_norm_mul_norm_eq_one_iff x y).1 ha with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    use [hx, r],
    refine and.intro _ hy,
    by_contradiction hrneg,
    rw hy at h,
    rw real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul hx
      (lt_of_le_of_ne (le_of_not_lt hrneg) hr) at h,
    norm_num at h },
  { intro h,
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    rw hy,
    exact real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx hr }
end

/-- The inner product of two vectors, divided by the product of their
norms, has value -1 if and only if they are nonzero and one is
a negative multiple of the other. -/
lemma real_inner_div_norm_mul_norm_eq_neg_one_iff (x y : F) :
  ⟪x, y⟫_ℝ / (‖x‖ * ‖y‖) = -1 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), r < 0 ∧ y = r • x) :=
begin
  split,
  { intro h,
    have ha := h,
    apply_fun absR at ha,
    norm_num at ha,
    rcases (abs_real_inner_div_norm_mul_norm_eq_one_iff x y).1 ha with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    use [hx, r],
    refine and.intro _ hy,
    by_contradiction hrpos,
    rw hy at h,
    rw real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx
      (lt_of_le_of_ne (le_of_not_lt hrpos) hr.symm) at h,
    norm_num at h },
  { intro h,
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    rw hy,
    exact real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul hx hr }
end

/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ‖x‖ * ‖y‖`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `abs_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
lemma inner_eq_norm_mul_iff {x y : E} :
  ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ (‖y‖ : 𝕜) • x = (‖x‖ : 𝕜) • y :=
begin
  by_cases h : (x = 0 ∨ y = 0), -- WLOG `x` and `y` are nonzero
  { cases h; simp [h] },
  calc ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ ‖x‖ * ‖y‖ = re ⟪x, y⟫ :
  begin
    norm_cast,
    split,
    { intros h',
      simp [h'] },
    { have cauchy_schwarz := abs_inner_le_norm x y,
      intros h',
      rw h' at ⊢ cauchy_schwarz,
      rwa re_eq_self_of_le }
  end
  ... ↔ 2 * ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖ - re ⟪x, y⟫) = 0 :
    by simp [h, show (2:ℝ) ≠ 0, by norm_num, sub_eq_zero]
  ... ↔ ‖(‖y‖:𝕜) • x - (‖x‖:𝕜) • y‖ * ‖(‖y‖:𝕜) • x - (‖x‖:𝕜) • y‖ = 0 :
  begin
    simp only [norm_sub_mul_self, inner_smul_left, inner_smul_right, norm_smul, conj_of_real,
      is_R_or_C.norm_eq_abs, abs_of_real, of_real_im, of_real_re, mul_re, abs_norm_eq_norm],
    refine eq.congr _ rfl,
    ring
  end
  ... ↔ (‖y‖ : 𝕜) • x = (‖x‖ : 𝕜) • y : by simp [norm_sub_eq_zero_iff]
end

/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ‖x‖ * ‖y‖`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `abs_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
lemma inner_eq_norm_mul_iff_real {x y : F} : ⟪x, y⟫_ℝ = ‖x‖ * ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y :=
inner_eq_norm_mul_iff

/-- If the inner product of two unit vectors is `1`, then the two vectors are equal. One form of
the equality case for Cauchy-Schwarz. -/
lemma inner_eq_norm_mul_iff_of_norm_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
  ⟪x, y⟫ = 1 ↔ x = y :=
by { convert inner_eq_norm_mul_iff using 2; simp [hx, hy] }

lemma inner_lt_norm_mul_iff_real {x y : F} :
  ⟪x, y⟫_ℝ < ‖x‖ * ‖y‖ ↔ ‖y‖ • x ≠ ‖x‖ • y :=
calc ⟪x, y⟫_ℝ < ‖x‖ * ‖y‖
    ↔ ⟪x, y⟫_ℝ ≠ ‖x‖ * ‖y‖ : ⟨ne_of_lt, lt_of_le_of_ne (real_inner_le_norm _ _)⟩
... ↔ ‖y‖ • x ≠ ‖x‖ • y : not_congr inner_eq_norm_mul_iff_real

/-- If the inner product of two unit vectors is strictly less than `1`, then the two vectors are
distinct. One form of the equality case for Cauchy-Schwarz. -/
lemma inner_lt_one_iff_real_of_norm_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
  ⟪x, y⟫_ℝ < 1 ↔ x ≠ y :=
by { convert inner_lt_norm_mul_iff_real; simp [hx, hy] }

/-- The inner product of two weighted sums, where the weights in each
sum add to 0, in terms of the norms of pairwise differences. -/
lemma inner_sum_smul_sum_smul_of_sum_eq_zero {ι₁ : Type*} {s₁ : finset ι₁} {w₁ : ι₁ → ℝ}
    (v₁ : ι₁ → F) (h₁ : ∑ i in s₁, w₁ i = 0) {ι₂ : Type*} {s₂ : finset ι₂} {w₂ : ι₂ → ℝ}
    (v₂ : ι₂ → F) (h₂ : ∑ i in s₂, w₂ i = 0) :
  ⟪(∑ i₁ in s₁, w₁ i₁ • v₁ i₁), (∑ i₂ in s₂, w₂ i₂ • v₂ i₂)⟫_ℝ =
    (-∑ i₁ in s₁, ∑ i₂ in s₂, w₁ i₁ * w₂ i₂ * (‖v₁ i₁ - v₂ i₂‖ * ‖v₁ i₁ - v₂ i₂‖)) / 2 :=
by simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
            real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
            ←div_sub_div_same, ←div_add_div_same, mul_sub_left_distrib, left_distrib,
            finset.sum_sub_distrib, finset.sum_add_distrib, ←finset.mul_sum, ←finset.sum_mul,
            h₁, h₂, zero_mul, mul_zero, finset.sum_const_zero, zero_add, zero_sub, finset.mul_sum,
            neg_div, finset.sum_div, mul_div_assoc, mul_assoc]

/-- The inner product as a sesquilinear map. -/
def innerₛₗ : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜 :=
linear_map.mk₂'ₛₗ _ _ (λ v w, ⟪v, w⟫) (λ _ _ _, inner_add_left) (λ _ _ _, inner_smul_left)
(λ _ _ _, inner_add_right) (λ _ _ _, inner_smul_right)

@[simp] lemma innerₛₗ_apply_coe (v : E) : (innerₛₗ v : E → 𝕜) = λ w, ⟪v, w⟫ := rfl

@[simp] lemma innerₛₗ_apply (v w : E) : innerₛₗ v w = ⟪v, w⟫ := rfl

/-- The inner product as a continuous sesquilinear map. Note that `to_dual_map` (resp. `to_dual`)
in `inner_product_space.dual` is a version of this given as a linear isometry (resp. linear
isometric equivalence). -/
def innerSL : E →L⋆[𝕜] E →L[𝕜] 𝕜 :=
linear_map.mk_continuous₂ innerₛₗ 1
(λ x y, by simp only [norm_inner_le_norm, one_mul, innerₛₗ_apply])

@[simp] lemma innerSL_apply_coe (v : E) : (innerSL v : E → 𝕜) = λ w, ⟪v, w⟫ := rfl

@[simp] lemma innerSL_apply (v w : E) : innerSL v w = ⟪v, w⟫ := rfl

/-- `innerSL` is an isometry. Note that the associated `linear_isometry` is defined in
`inner_product_space.dual` as `to_dual_map`.  -/
@[simp] lemma innerSL_apply_norm {x : E} : ‖(innerSL x : E →L[𝕜] 𝕜)‖ = ‖x‖ :=
begin
  refine le_antisymm ((innerSL x : E →L[𝕜] 𝕜).op_norm_le_bound (norm_nonneg _)
    (λ y, norm_inner_le_norm _ _)) _,
  cases eq_or_lt_of_le (norm_nonneg x) with h h,
  { have : x = 0 := norm_eq_zero.mp (eq.symm h),
    simp [this] },
  { refine (mul_le_mul_right h).mp _,
    calc ‖x‖ * ‖x‖ = ‖x‖ ^ 2 : by ring
    ... = re ⟪x, x⟫ : norm_sq_eq_inner _
    ... ≤ abs ⟪x, x⟫ : re_le_abs _
    ... = ‖innerSL x x‖ : by { rw [←is_R_or_C.norm_eq_abs], refl }
    ... ≤ ‖innerSL x‖ * ‖x‖ : (innerSL x : E →L[𝕜] 𝕜).le_op_norm _ }
end

/-- The inner product as a continuous sesquilinear map, with the two arguments flipped. -/
def innerSL_flip : E →L[𝕜] E →L⋆[𝕜] 𝕜 :=
@continuous_linear_map.flipₗᵢ' 𝕜 𝕜 𝕜 E E 𝕜 _ _ _ _ _ _ _ _ _ (ring_hom.id 𝕜) (star_ring_end 𝕜) _ _
  innerSL

@[simp] lemma innerSL_flip_apply {x y : E} : innerSL_flip x y = ⟪y, x⟫ := rfl

namespace continuous_linear_map

variables  {E' : Type*} [inner_product_space 𝕜 E']

/-- Given `f : E →L[𝕜] E'`, construct the continuous sesquilinear form `λ x y, ⟪x, A y⟫`, given
as a continuous linear map. -/
def to_sesq_form : (E →L[𝕜] E') →L[𝕜] E' →L⋆[𝕜] E →L[𝕜] 𝕜 :=
↑((continuous_linear_map.flipₗᵢ' E E' 𝕜
  (star_ring_end 𝕜) (ring_hom.id 𝕜)).to_continuous_linear_equiv) ∘L
(continuous_linear_map.compSL E E' (E' →L⋆[𝕜] 𝕜) (ring_hom.id 𝕜) (ring_hom.id 𝕜) innerSL_flip)

@[simp] lemma to_sesq_form_apply_coe (f : E →L[𝕜] E') (x : E') :
  to_sesq_form f x = (innerSL x).comp f := rfl

lemma to_sesq_form_apply_norm_le {f : E →L[𝕜] E'} {v : E'} : ‖to_sesq_form f v‖ ≤ ‖f‖ * ‖v‖ :=
begin
  refine op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _,
  intro x,
  have h₁ : ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_op_norm _ _,
  have h₂ := @norm_inner_le_norm 𝕜 E' _ _ v (f x),
  calc ‖⟪v, f x⟫‖ ≤ ‖v‖ * ‖f x‖       :  h₂
              ... ≤ ‖v‖ * (‖f‖ * ‖x‖)  : mul_le_mul_of_nonneg_left h₁ (norm_nonneg v)
              ... = ‖f‖ * ‖v‖ * ‖x‖    : by ring,
end

end continuous_linear_map

/-- When an inner product space `E` over `𝕜` is considered as a real normed space, its inner
product satisfies `is_bounded_bilinear_map`.

In order to state these results, we need a `normed_space ℝ E` instance. We will later establish
such an instance by restriction-of-scalars, `inner_product_space.is_R_or_C_to_real 𝕜 E`, but this
instance may be not definitionally equal to some other “natural” instance. So, we assume
`[normed_space ℝ E]`.
-/
lemma is_bounded_bilinear_map_inner [normed_space ℝ E] :
  is_bounded_bilinear_map ℝ (λ p : E × E, ⟪p.1, p.2⟫) :=
{ add_left := λ _ _ _, inner_add_left,
  smul_left := λ r x y,
    by simp only [← algebra_map_smul 𝕜 r x, algebra_map_eq_of_real, inner_smul_real_left],
  add_right := λ _ _ _, inner_add_right,
  smul_right := λ r x y,
    by simp only [← algebra_map_smul 𝕜 r y, algebra_map_eq_of_real, inner_smul_real_right],
  bound := ⟨1, zero_lt_one, λ x y,
    by { rw [one_mul], exact norm_inner_le_norm x y, }⟩ }

end norm

section bessels_inequality

variables {ι: Type*} (x : E) {v : ι → E}

/-- Bessel's inequality for finite sums. -/
lemma orthonormal.sum_inner_products_le {s : finset ι} (hv : orthonormal 𝕜 v) :
  ∑ i in s, ‖⟪v i, x⟫‖ ^ 2 ≤ ‖x‖ ^ 2 :=
begin
  have h₂ : ∑ i in s, ∑ j in s, ⟪v i, x⟫ * ⟪x, v j⟫ * ⟪v j, v i⟫
    = (∑ k in s, (⟪v k, x⟫ * ⟪x, v k⟫) : 𝕜),
  { exact hv.inner_left_right_finset },
  have h₃ : ∀ z : 𝕜, re (z * conj (z)) = ‖z‖ ^ 2,
  { intro z,
    simp only [mul_conj, norm_sq_eq_def'],
    norm_cast, },
  suffices hbf: ‖x -  ∑ i in s, ⟪v i, x⟫ • (v i)‖ ^ 2 = ‖x‖ ^ 2 - ∑ i in s, ‖⟪v i, x⟫‖ ^ 2,
  { rw [←sub_nonneg, ←hbf],
    simp only [norm_nonneg, pow_nonneg], },
  rw [norm_sub_sq, sub_add],
  simp only [inner_product_space.norm_sq_eq_inner, inner_sum],
  simp only [sum_inner, two_mul, inner_smul_right, inner_conj_sym, ←mul_assoc, h₂, ←h₃,
  inner_conj_sym, add_monoid_hom.map_sum, finset.mul_sum, ←finset.sum_sub_distrib, inner_smul_left,
  add_sub_cancel'],
end

/-- Bessel's inequality. -/
lemma orthonormal.tsum_inner_products_le (hv : orthonormal 𝕜 v) :
  ∑' i, ‖⟪v i, x⟫‖ ^ 2 ≤ ‖x‖ ^ 2 :=
begin
  refine tsum_le_of_sum_le' _ (λ s, hv.sum_inner_products_le x),
  simp only [norm_nonneg, pow_nonneg]
end

/-- The sum defined in Bessel's inequality is summable. -/
lemma orthonormal.inner_products_summable (hv : orthonormal 𝕜 v) : summable (λ i, ‖⟪v i, x⟫‖ ^ 2) :=
begin
  use ⨆ s : finset ι, ∑ i in s, ‖⟪v i, x⟫‖ ^ 2,
  apply has_sum_of_is_lub_of_nonneg,
  { intro b,
    simp only [norm_nonneg, pow_nonneg], },
  { refine is_lub_csupr _,
    use ‖x‖ ^ 2,
    rintro y ⟨s, rfl⟩,
    exact hv.sum_inner_products_le x }
end

end bessels_inequality

/-- A field `𝕜` satisfying `is_R_or_C` is itself a `𝕜`-inner product space. -/
instance is_R_or_C.inner_product_space : inner_product_space 𝕜 𝕜 :=
{ to_normed_add_comm_group := non_unital_normed_ring.to_normed_add_comm_group,
  inner := λ x y, conj x * y,
  norm_sq_eq_inner := λ x,
    by { unfold inner, rw [mul_comm, mul_conj, of_real_re, norm_sq_eq_def'] },
  conj_sym := λ x y, by simp only [mul_comm, map_mul, star_ring_end_self_apply],
  add_left := λ x y z, by simp only [add_mul, map_add],
  smul_left := λ x y z, by simp only [mul_assoc, smul_eq_mul, map_mul] }

@[simp] lemma is_R_or_C.inner_apply (x y : 𝕜) : ⟪x, y⟫ = (conj x) * y := rfl

/-! ### Inner product space structure on subspaces -/

/-- Induced inner product on a submodule. -/
instance submodule.inner_product_space (W : submodule 𝕜 E) : inner_product_space 𝕜 W :=
{ to_normed_add_comm_group := submodule.normed_add_comm_group _,
  inner             := λ x y, ⟪(x:E), (y:E)⟫,
  conj_sym          := λ _ _, inner_conj_sym _ _ ,
  norm_sq_eq_inner  := λ _, norm_sq_eq_inner _,
  add_left          := λ _ _ _ , inner_add_left,
  smul_left         := λ _ _ _, inner_smul_left,
  ..submodule.normed_space W }

/-- The inner product on submodules is the same as on the ambient space. -/
@[simp] lemma submodule.coe_inner (W : submodule 𝕜 E) (x y : W) : ⟪x, y⟫ = ⟪(x:E), ↑y⟫ := rfl

lemma orthonormal.cod_restrict {ι : Type*} {v : ι → E} (hv : orthonormal 𝕜 v)
  (s : submodule 𝕜 E) (hvs : ∀ i, v i ∈ s) :
  @orthonormal 𝕜 s _ _ ι (set.cod_restrict v s hvs) :=
s.subtypeₗᵢ.orthonormal_comp_iff.mp hv

lemma orthonormal_span {ι : Type*} {v : ι → E} (hv : orthonormal 𝕜 v) :
  @orthonormal 𝕜 (submodule.span 𝕜 (set.range v)) _ _ ι
    (λ i : ι, ⟨v i, submodule.subset_span (set.mem_range_self i)⟩) :=
hv.cod_restrict (submodule.span 𝕜 (set.range v))
  (λ i, submodule.subset_span (set.mem_range_self i))

/-! ### Families of mutually-orthogonal subspaces of an inner product space -/

section orthogonal_family
variables {ι : Type*} [dec_ι : decidable_eq ι] (𝕜)
open_locale direct_sum

/-- An indexed family of mutually-orthogonal subspaces of an inner product space `E`.

The simple way to express this concept would be as a condition on `V : ι → submodule 𝕜 E`.  We
We instead implement it as a condition on a family of inner product spaces each equipped with an
isometric embedding into `E`, thus making it a property of morphisms rather than subobjects.

This definition is less lightweight, but allows for better definitional properties when the inner
product space structure on each of the submodules is important -- for example, when considering
their Hilbert sum (`pi_lp V 2`).  For example, given an orthonormal set of vectors `v : ι → E`,
we have an associated orthogonal family of one-dimensional subspaces of `E`, which it is convenient
to be able to discuss using `ι → 𝕜` rather than `Π i : ι, span 𝕜 (v i)`. -/
def orthogonal_family {G : ι → Type*} [Π i, inner_product_space 𝕜 (G i)] (V : Π i, G i →ₗᵢ[𝕜] E) :
  Prop :=
∀ ⦃i j⦄, i ≠ j → ∀ v : G i, ∀ w : G j, ⟪V i v, V j w⟫ = 0

variables {𝕜} {G : ι → Type*} [Π i, inner_product_space 𝕜 (G i)] {V : Π i, G i →ₗᵢ[𝕜] E}
  (hV : orthogonal_family 𝕜 V) [dec_V : Π i (x : G i), decidable (x ≠ 0)]

lemma orthonormal.orthogonal_family {v : ι → E} (hv : orthonormal 𝕜 v) :
  @orthogonal_family 𝕜 _ _ _ _ (λ i : ι, 𝕜) _
    (λ i, linear_isometry.to_span_singleton 𝕜 E (hv.1 i)) :=
λ i j hij a b, by simp [inner_smul_left, inner_smul_right, hv.2 hij]

include hV dec_ι
lemma orthogonal_family.eq_ite {i j : ι} (v : G i) (w : G j) :
  ⟪V i v, V j w⟫ = ite (i = j) ⟪V i v, V j w⟫ 0 :=
begin
  split_ifs,
  { refl },
  { exact hV h v w }
end

include dec_V
lemma orthogonal_family.inner_right_dfinsupp (l : ⨁ i, G i) (i : ι) (v : G i) :
  ⟪V i v, l.sum (λ j, V j)⟫ = ⟪v, l i⟫ :=
calc ⟪V i v, l.sum (λ j, V j)⟫
    = l.sum (λ j, λ w, ⟪V i v, V j w⟫) : dfinsupp.inner_sum (λ j, V j) l (V i v)
... = l.sum (λ j, λ w, ite (i=j) ⟪V i v, V j w⟫ 0) :
  congr_arg l.sum $ funext $ λ j, funext $ hV.eq_ite v
... = ⟪v, l i⟫ :
begin
  simp only [dfinsupp.sum, submodule.coe_inner, finset.sum_ite_eq, ite_eq_left_iff,
    dfinsupp.mem_support_to_fun],
  split_ifs with h h,
  { simp only [linear_isometry.inner_map_map] },
  { simp only [of_not_not h, inner_zero_right] },
end
omit dec_ι dec_V

lemma orthogonal_family.inner_right_fintype [fintype ι] (l : Π i, G i) (i : ι) (v : G i) :
  ⟪V i v, ∑ j : ι, V j (l j)⟫ = ⟪v, l i⟫ :=
by classical;
calc ⟪V i v, ∑ j : ι, V j (l j)⟫
    = ∑ j : ι, ⟪V i v, V j (l j)⟫: by rw inner_sum
... = ∑ j, ite (i = j) ⟪V i v, V j (l j)⟫ 0 :
  congr_arg (finset.sum finset.univ) $ funext $ λ j, (hV.eq_ite v (l j))
... = ⟪v, l i⟫ : by simp only [finset.sum_ite_eq, finset.mem_univ, (V i).inner_map_map, if_true]

lemma orthogonal_family.inner_sum (l₁ l₂ : Π i, G i) (s : finset ι) :
  ⟪∑ i in s, V i (l₁ i), ∑ j in s, V j (l₂ j)⟫ = ∑ i in s, ⟪l₁ i, l₂ i⟫ :=
by classical;
calc ⟪∑ i in s, V i (l₁ i), ∑ j in s, V j (l₂ j)⟫
    = ∑ j in s, ∑ i in s, ⟪V i (l₁ i), V j (l₂ j)⟫ : by simp only [sum_inner, inner_sum]
... = ∑ j in s, ∑ i in s, ite (i = j) ⟪V i (l₁ i), V j (l₂ j)⟫ 0 :
begin
  congr' with i,
  congr' with j,
  apply hV.eq_ite,
end
... = ∑ i in s, ⟪l₁ i, l₂ i⟫ : by simp only [finset.sum_ite_of_true,
  finset.sum_ite_eq', linear_isometry.inner_map_map, imp_self, implies_true_iff]

lemma orthogonal_family.norm_sum (l : Π i, G i) (s : finset ι) :
  ‖∑ i in s, V i (l i)‖ ^ 2 = ∑ i in s, ‖l i‖ ^ 2 :=
begin
  have : (‖∑ i in s, V i (l i)‖ ^ 2 : 𝕜) = ∑ i in s, ‖l i‖ ^ 2,
  { simp only [← inner_self_eq_norm_sq_to_K, hV.inner_sum] },
  exact_mod_cast this,
end

/-- The composition of an orthogonal family of subspaces with an injective function is also an
orthogonal family. -/
lemma orthogonal_family.comp {γ : Type*} {f : γ → ι} (hf : function.injective f) :
  orthogonal_family 𝕜 (λ g : γ, (V (f g) : G (f g) →ₗᵢ[𝕜] E)) :=
λ i j hij v w, hV (hf.ne hij) v w

lemma orthogonal_family.orthonormal_sigma_orthonormal {α : ι → Type*} {v_family : Π i, (α i) → G i}
  (hv_family : ∀ i, orthonormal 𝕜 (v_family i)) :
  orthonormal 𝕜 (λ a : Σ i, α i, V a.1 (v_family a.1 a.2)) :=
begin
  split,
  { rintros ⟨i, v⟩,
    simpa only [linear_isometry.norm_map] using (hv_family i).left v },
  rintros ⟨i, v⟩ ⟨j, w⟩ hvw,
  by_cases hij : i = j,
  { subst hij,
    have : v ≠ w := λ h, by { subst h, exact hvw rfl },
    simpa only [linear_isometry.inner_map_map] using (hv_family i).2 this },
  { exact hV hij (v_family i v) (v_family j w) }
end

include dec_ι
lemma orthogonal_family.norm_sq_diff_sum (f : Π i, G i) (s₁ s₂ : finset ι) :
  ‖∑ i in s₁, V i (f i) - ∑ i in s₂, V i (f i)‖ ^ 2
  = ∑ i in s₁ \ s₂, ‖f i‖ ^ 2 + ∑ i in s₂ \ s₁, ‖f i‖ ^ 2 :=
begin
  rw [← finset.sum_sdiff_sub_sum_sdiff, sub_eq_add_neg, ← finset.sum_neg_distrib],
  let F : Π i, G i := λ i, if i ∈ s₁ then f i else - (f i),
  have hF₁ : ∀ i ∈ s₁ \ s₂, F i = f i := λ i hi, if_pos (finset.sdiff_subset _ _ hi),
  have hF₂ : ∀ i ∈ s₂ \ s₁, F i = - f i := λ i hi, if_neg (finset.mem_sdiff.mp hi).2,
  have hF : ∀ i, ‖F i‖ = ‖f i‖,
  { intros i,
    dsimp only [F],
    split_ifs;
    simp only [eq_self_iff_true, norm_neg], },
  have : ‖∑ i in s₁ \ s₂, V i (F i) + ∑ i in s₂ \ s₁, V i (F i)‖ ^ 2 =
    ∑ i in s₁ \ s₂, ‖F i‖ ^ 2 + ∑ i in s₂ \ s₁, ‖F i‖ ^ 2,
  { have hs : disjoint (s₁ \ s₂) (s₂ \ s₁) := disjoint_sdiff_sdiff,
    simpa only [finset.sum_union hs] using hV.norm_sum F (s₁ \ s₂ ∪ s₂ \ s₁) },
  convert this using 4,
  { refine finset.sum_congr rfl (λ i hi, _),
    simp only [hF₁ i hi] },
  { refine finset.sum_congr rfl (λ i hi, _),
    simp only [hF₂ i hi, linear_isometry.map_neg] },
  { simp only [hF] },
  { simp only [hF] },
end

omit dec_ι

/-- A family `f` of mutually-orthogonal elements of `E` is summable, if and only if
`(λ i, ‖f i‖ ^ 2)` is summable. -/
lemma orthogonal_family.summable_iff_norm_sq_summable [complete_space E] (f : Π i, G i) :
  summable (λ i, V i (f i)) ↔ summable (λ i, ‖f i‖ ^ 2) :=
begin
  classical,
  simp only [summable_iff_cauchy_seq_finset, normed_add_comm_group.cauchy_seq_iff,
    real.norm_eq_abs],
  split,
  { intros hf ε hε,
    obtain ⟨a, H⟩ := hf _ (sqrt_pos.mpr hε),
    use a,
    intros s₁ hs₁ s₂ hs₂,
    rw ← finset.sum_sdiff_sub_sum_sdiff,
    refine (_root_.abs_sub _ _).trans_lt _,
    have : ∀ i, 0 ≤ ‖f i‖ ^ 2 := λ i : ι, sq_nonneg _,
    simp only [finset.abs_sum_of_nonneg' this],
    have : ∑ i in s₁ \ s₂, ‖f i‖ ^ 2 + ∑ i in s₂ \ s₁, ‖f i‖ ^ 2 < (sqrt ε) ^ 2,
    { rw [← hV.norm_sq_diff_sum, sq_lt_sq,
        _root_.abs_of_nonneg (sqrt_nonneg _), _root_.abs_of_nonneg (norm_nonneg _)],
      exact H s₁ hs₁ s₂ hs₂ },
    have hη := sq_sqrt (le_of_lt hε),
    linarith },
  { intros hf ε hε,
    have hε' : 0 < ε ^ 2 / 2 := half_pos (sq_pos_of_pos hε),
    obtain ⟨a, H⟩ := hf _ hε',
    use a,
    intros s₁ hs₁ s₂ hs₂,
    refine (abs_lt_of_sq_lt_sq' _ (le_of_lt hε)).2,
    have has : a ≤ s₁ ⊓ s₂ := le_inf hs₁ hs₂,
    rw hV.norm_sq_diff_sum,
    have Hs₁ : ∑ (x : ι) in s₁ \ s₂, ‖f x‖ ^ 2 < ε ^ 2 / 2,
    { convert H _ hs₁ _ has,
      have : s₁ ⊓ s₂ ⊆ s₁ := finset.inter_subset_left _ _,
      rw [← finset.sum_sdiff this, add_tsub_cancel_right, finset.abs_sum_of_nonneg'],
      { simp },
      { exact λ i, sq_nonneg _ } },
    have Hs₂ : ∑ (x : ι) in s₂ \ s₁, ‖f x‖ ^ 2 < ε ^ 2 /2,
    { convert H _ hs₂ _ has,
      have : s₁ ⊓ s₂ ⊆ s₂ := finset.inter_subset_right _ _,
      rw [← finset.sum_sdiff this, add_tsub_cancel_right, finset.abs_sum_of_nonneg'],
      { simp },
      { exact λ i, sq_nonneg _ } },
    linarith },
end

omit hV

/-- An orthogonal family forms an independent family of subspaces; that is, any collection of
elements each from a different subspace in the family is linearly independent. In particular, the
pairwise intersections of elements of the family are 0. -/
lemma orthogonal_family.independent {V : ι → submodule 𝕜 E}
  (hV : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ)) :
  complete_lattice.independent V :=
begin
  classical,
  apply complete_lattice.independent_of_dfinsupp_lsum_injective,
  rw [← @linear_map.ker_eq_bot _ _ _ _ _ _ (direct_sum.add_comm_group (λ i, V i)),
    submodule.eq_bot_iff],
  intros v hv,
  rw linear_map.mem_ker at hv,
  ext i,
  suffices : ⟪(v i : E), v i⟫ = 0,
  { simpa only [inner_self_eq_zero] using this },
  calc ⟪(v i : E), v i⟫ = ⟪(v i : E), dfinsupp.lsum ℕ (λ i, (V i).subtype) v⟫ :
    by simpa only [dfinsupp.sum_add_hom_apply, dfinsupp.lsum_apply_apply]
      using (hV.inner_right_dfinsupp v i (v i)).symm
  ... = 0 : by simp only [hv, inner_zero_right],
end

include dec_ι
lemma direct_sum.is_internal.collected_basis_orthonormal {V : ι → submodule 𝕜 E}
  (hV : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ))
  (hV_sum : direct_sum.is_internal (λ i, V i))
  {α : ι → Type*}
  {v_family : Π i, basis (α i) 𝕜 (V i)} (hv_family : ∀ i, orthonormal 𝕜 (v_family i)) :
  orthonormal 𝕜 (hV_sum.collected_basis v_family) :=
by simpa only [hV_sum.collected_basis_coe] using hV.orthonormal_sigma_orthonormal hv_family

end orthogonal_family

section is_R_or_C_to_real

variables {G : Type*}

variables (𝕜 E)
include 𝕜

/-- A general inner product implies a real inner product. This is not registered as an instance
since it creates problems with the case `𝕜 = ℝ`. -/
def has_inner.is_R_or_C_to_real : has_inner ℝ E :=
{ inner := λ x y, re ⟪x, y⟫ }

/-- A general inner product space structure implies a real inner product structure. This is not
registered as an instance since it creates problems with the case `𝕜 = ℝ`, but in can be used in a
proof to obtain a real inner product space structure from a given `𝕜`-inner product space
structure. -/
def inner_product_space.is_R_or_C_to_real : inner_product_space ℝ E :=
{ to_normed_add_comm_group := inner_product_space.to_normed_add_comm_group 𝕜,
  norm_sq_eq_inner := norm_sq_eq_inner,
  conj_sym := λ x y, inner_re_symm,
  add_left := λ x y z, by
  { change re ⟪x + y, z⟫ = re ⟪x, z⟫ + re ⟪y, z⟫,
    simp only [inner_add_left, map_add] },
  smul_left := λ x y r, by
  { change re ⟪(r : 𝕜) • x, y⟫ = r * re ⟪x, y⟫,
    simp only [inner_smul_left, conj_of_real, of_real_mul_re] },
  ..has_inner.is_R_or_C_to_real 𝕜 E,
  ..normed_space.restrict_scalars ℝ 𝕜 E }

variable {E}

lemma real_inner_eq_re_inner (x y : E) :
  @has_inner.inner ℝ E (has_inner.is_R_or_C_to_real 𝕜 E) x y = re ⟪x, y⟫ := rfl

lemma real_inner_I_smul_self (x : E) :
  @has_inner.inner ℝ E (has_inner.is_R_or_C_to_real 𝕜 E) x ((I : 𝕜) • x) = 0 :=
by simp [real_inner_eq_re_inner, inner_smul_right]

omit 𝕜

/-- A complex inner product implies a real inner product -/
instance inner_product_space.complex_to_real [inner_product_space ℂ G] : inner_product_space ℝ G :=
inner_product_space.is_R_or_C_to_real ℂ G

@[simp] protected lemma complex.inner (w z : ℂ) : ⟪w, z⟫_ℝ = (conj w * z).re := rfl

/-- The inner product on an inner product space of dimension 2 can be evaluated in terms
of a complex-number representation of the space. -/
lemma inner_map_complex [inner_product_space ℝ G] (f : G ≃ₗᵢ[ℝ] ℂ) (x y : G) :
  ⟪x, y⟫_ℝ = (conj (f x) * f y).re :=
by rw [← complex.inner, f.inner_map_map]

end is_R_or_C_to_real

section continuous

/-!
### Continuity of the inner product
-/

lemma continuous_inner : continuous (λ p : E × E, ⟪p.1, p.2⟫) :=
begin
  letI : inner_product_space ℝ E := inner_product_space.is_R_or_C_to_real 𝕜 E,
  exact is_bounded_bilinear_map_inner.continuous
end

variables {α : Type*}

lemma filter.tendsto.inner {f g : α → E} {l : filter α} {x y : E} (hf : tendsto f l (𝓝 x))
  (hg : tendsto g l (𝓝 y)) :
  tendsto (λ t, ⟪f t, g t⟫) l (𝓝 ⟪x, y⟫) :=
(continuous_inner.tendsto _).comp (hf.prod_mk_nhds hg)

variables [topological_space α] {f g : α → E} {x : α} {s : set α}

include 𝕜

lemma continuous_within_at.inner (hf : continuous_within_at f s x)
  (hg : continuous_within_at g s x) :
  continuous_within_at (λ t, ⟪f t, g t⟫) s x :=
hf.inner hg

lemma continuous_at.inner (hf : continuous_at f x) (hg : continuous_at g x) :
  continuous_at (λ t, ⟪f t, g t⟫) x :=
hf.inner hg

lemma continuous_on.inner (hf : continuous_on f s) (hg : continuous_on g s) :
  continuous_on (λ t, ⟪f t, g t⟫) s :=
λ x hx, (hf x hx).inner (hg x hx)

@[continuity]
lemma continuous.inner (hf : continuous f) (hg : continuous g) : continuous (λ t, ⟪f t, g t⟫) :=
continuous_iff_continuous_at.2 $ λ x, hf.continuous_at.inner hg.continuous_at

end continuous

section re_apply_inner_self

/-- Extract a real bilinear form from an operator `T`, by taking the pairing `λ x, re ⟪T x, x⟫`. -/
def continuous_linear_map.re_apply_inner_self (T : E →L[𝕜] E) (x : E) : ℝ := re ⟪T x, x⟫

lemma continuous_linear_map.re_apply_inner_self_apply (T : E →L[𝕜] E) (x : E) :
  T.re_apply_inner_self x = re ⟪T x, x⟫ :=
rfl

lemma continuous_linear_map.re_apply_inner_self_continuous (T : E →L[𝕜] E) :
  continuous T.re_apply_inner_self :=
re_clm.continuous.comp $ T.continuous.inner continuous_id

lemma continuous_linear_map.re_apply_inner_self_smul (T : E →L[𝕜] E) (x : E) {c : 𝕜} :
  T.re_apply_inner_self (c • x) = ‖c‖ ^ 2 * T.re_apply_inner_self x :=
by simp only [continuous_linear_map.map_smul, continuous_linear_map.re_apply_inner_self_apply,
  inner_smul_left, inner_smul_right, ← mul_assoc, mul_conj, norm_sq_eq_def', ← smul_re,
  algebra.smul_def (‖c‖ ^ 2) ⟪T x, x⟫, algebra_map_eq_of_real]

end re_apply_inner_self

/-! ### The orthogonal complement -/

section orthogonal
variables (K : submodule 𝕜 E)

/-- The subspace of vectors orthogonal to a given subspace. -/
def submodule.orthogonal : submodule 𝕜 E :=
{ carrier := {v | ∀ u ∈ K, ⟪u, v⟫ = 0},
  zero_mem' := λ _ _, inner_zero_right,
  add_mem' := λ x y hx hy u hu, by rw [inner_add_right, hx u hu, hy u hu, add_zero],
  smul_mem' := λ c x hx u hu, by rw [inner_smul_right, hx u hu, mul_zero] }

notation K`ᗮ`:1200 := submodule.orthogonal K

/-- When a vector is in `Kᗮ`. -/
lemma submodule.mem_orthogonal (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪u, v⟫ = 0 := iff.rfl

/-- When a vector is in `Kᗮ`, with the inner product the
other way round. -/
lemma submodule.mem_orthogonal' (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪v, u⟫ = 0 :=
by simp_rw [submodule.mem_orthogonal, inner_eq_zero_sym]

variables {K}

/-- A vector in `K` is orthogonal to one in `Kᗮ`. -/
lemma submodule.inner_right_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪u, v⟫ = 0 :=
(K.mem_orthogonal v).1 hv u hu

/-- A vector in `Kᗮ` is orthogonal to one in `K`. -/
lemma submodule.inner_left_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪v, u⟫ = 0 :=
by rw [inner_eq_zero_sym]; exact submodule.inner_right_of_mem_orthogonal hu hv

/-- A vector is in `(𝕜 ∙ u)ᗮ` iff it is orthogonal to `u`. -/
lemma submodule.mem_orthogonal_singleton_iff_inner_right {u v : E} : v ∈ (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0 :=
begin
  refine ⟨submodule.inner_right_of_mem_orthogonal (submodule.mem_span_singleton_self u), _⟩,
  intros hv w hw,
  rw submodule.mem_span_singleton at hw,
  obtain ⟨c, rfl⟩ := hw,
  simp [inner_smul_left, hv],
end

/-- A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`. -/
lemma submodule.mem_orthogonal_singleton_iff_inner_left {u v : E} : v ∈ (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0 :=
by rw [submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_sym]

lemma submodule.sub_mem_orthogonal_of_inner_left {x y : E}
  (h : ∀ (v : K), ⟪x, v⟫ = ⟪y, v⟫) : x - y ∈ Kᗮ :=
begin
  rw submodule.mem_orthogonal',
  intros u hu,
  rw [inner_sub_left, sub_eq_zero],
  exact h ⟨u, hu⟩,
end

lemma submodule.sub_mem_orthogonal_of_inner_right {x y : E}
  (h : ∀ (v : K), ⟪(v : E), x⟫ = ⟪(v : E), y⟫) : x - y ∈ Kᗮ :=
begin
  intros u hu,
  rw [inner_sub_right, sub_eq_zero],
  exact h ⟨u, hu⟩,
end

variables (K)

/-- `K` and `Kᗮ` have trivial intersection. -/
lemma submodule.inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥ :=
begin
  rw submodule.eq_bot_iff,
  intros x,
  rw submodule.mem_inf,
  exact λ ⟨hx, ho⟩, inner_self_eq_zero.1 (ho x hx)
end

/-- `K` and `Kᗮ` have trivial intersection. -/
lemma submodule.orthogonal_disjoint : disjoint K Kᗮ :=
by simp [disjoint_iff, K.inf_orthogonal_eq_bot]

/-- `Kᗮ` can be characterized as the intersection of the kernels of the operations of
inner product with each of the elements of `K`. -/
lemma orthogonal_eq_inter : Kᗮ = ⨅ v : K, linear_map.ker (innerSL (v:E) : E →L[𝕜] 𝕜) :=
begin
  apply le_antisymm,
  { rw le_infi_iff,
    rintros ⟨v, hv⟩ w hw,
    simpa using hw _ hv },
  { intros v hv w hw,
    simp only [submodule.mem_infi] at hv,
    exact hv ⟨w, hw⟩ }
end

/-- The orthogonal complement of any submodule `K` is closed. -/
lemma submodule.is_closed_orthogonal : is_closed (Kᗮ : set E) :=
begin
  rw orthogonal_eq_inter K,
  have := λ v : K, continuous_linear_map.is_closed_ker (innerSL (v:E) : E →L[𝕜] 𝕜),
  convert is_closed_Inter this,
  simp only [submodule.infi_coe],
end

/-- In a complete space, the orthogonal complement of any submodule `K` is complete. -/
instance [complete_space E] : complete_space Kᗮ := K.is_closed_orthogonal.complete_space_coe

variables (𝕜 E)

/-- `submodule.orthogonal` gives a `galois_connection` between
`submodule 𝕜 E` and its `order_dual`. -/
lemma submodule.orthogonal_gc :
  @galois_connection (submodule 𝕜 E) (submodule 𝕜 E)ᵒᵈ _ _
    submodule.orthogonal submodule.orthogonal :=
λ K₁ K₂, ⟨λ h v hv u hu, submodule.inner_left_of_mem_orthogonal hv (h hu),
          λ h v hv u hu, submodule.inner_left_of_mem_orthogonal hv (h hu)⟩

variables {𝕜 E}

/-- `submodule.orthogonal` reverses the `≤` ordering of two
subspaces. -/
lemma submodule.orthogonal_le {K₁ K₂ : submodule 𝕜 E} (h : K₁ ≤ K₂) : K₂ᗮ ≤ K₁ᗮ :=
(submodule.orthogonal_gc 𝕜 E).monotone_l h

/-- `submodule.orthogonal.orthogonal` preserves the `≤` ordering of two
subspaces. -/
lemma submodule.orthogonal_orthogonal_monotone {K₁ K₂ : submodule 𝕜 E} (h : K₁ ≤ K₂) :
  K₁ᗮᗮ ≤ K₂ᗮᗮ :=
submodule.orthogonal_le (submodule.orthogonal_le h)

/-- `K` is contained in `Kᗮᗮ`. -/
lemma submodule.le_orthogonal_orthogonal : K ≤ Kᗮᗮ := (submodule.orthogonal_gc 𝕜 E).le_u_l _

/-- The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup. -/
lemma submodule.inf_orthogonal (K₁ K₂ : submodule 𝕜 E) : K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ :=
(submodule.orthogonal_gc 𝕜 E).l_sup.symm

/-- The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup. -/
lemma submodule.infi_orthogonal {ι : Type*} (K : ι → submodule 𝕜 E) : (⨅ i, (K i)ᗮ) = (supr K)ᗮ :=
(submodule.orthogonal_gc 𝕜 E).l_supr.symm

/-- The inf of a set of orthogonal subspaces equals the subspace orthogonal to the sup. -/
lemma submodule.Inf_orthogonal (s : set $ submodule 𝕜 E) : (⨅ K ∈ s, Kᗮ) = (Sup s)ᗮ :=
(submodule.orthogonal_gc 𝕜 E).l_Sup.symm

@[simp] lemma submodule.top_orthogonal_eq_bot : (⊤ : submodule 𝕜 E)ᗮ = ⊥ :=
begin
  ext,
  rw [submodule.mem_bot, submodule.mem_orthogonal],
  exact ⟨λ h, inner_self_eq_zero.mp (h x submodule.mem_top), by { rintro rfl, simp }⟩
end

@[simp] lemma submodule.bot_orthogonal_eq_top : (⊥ : submodule 𝕜 E)ᗮ = ⊤ :=
begin
  rw [← submodule.top_orthogonal_eq_bot, eq_top_iff],
  exact submodule.le_orthogonal_orthogonal ⊤
end

@[simp] lemma submodule.orthogonal_eq_top_iff : Kᗮ = ⊤ ↔ K = ⊥ :=
begin
  refine ⟨_, by { rintro rfl, exact submodule.bot_orthogonal_eq_top }⟩,
  intro h,
  have : K ⊓ Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot,
  rwa [h, inf_comm, top_inf_eq] at this
end

lemma submodule.orthogonal_family_self :
  @orthogonal_family 𝕜 E _ _ _ (λ b, ((cond b K Kᗮ : submodule 𝕜 E) : Type*)) _
  (λ b, (cond b K Kᗮ).subtypeₗᵢ)
| tt tt := absurd rfl
| tt ff := λ _ x y, submodule.inner_right_of_mem_orthogonal x.prop y.prop
| ff tt := λ _ x y, submodule.inner_left_of_mem_orthogonal y.prop x.prop
| ff ff := absurd rfl

end orthogonal

namespace uniform_space.completion

open uniform_space function

instance {𝕜' E' : Type*} [topological_space 𝕜'] [uniform_space E'] [has_inner 𝕜' E'] :
  has_inner 𝕜' (completion E') :=
{ inner := curry $ (dense_inducing_coe.prod dense_inducing_coe).extend (uncurry inner) }

@[simp] lemma inner_coe (a b : E) :
  inner (a : completion E) (b : completion E) = (inner a b : 𝕜) :=
(dense_inducing_coe.prod dense_inducing_coe).extend_eq
  (continuous_inner : continuous (uncurry inner : E × E → 𝕜)) (a, b)

protected lemma continuous_inner :
  continuous (uncurry inner : completion E × completion E → 𝕜) :=
begin
  let inner' : E →+ E →+ 𝕜 :=
  { to_fun := λ x, (innerₛₗ x).to_add_monoid_hom,
    map_zero' := by ext x; exact inner_zero_left,
    map_add' := λ x y, by ext z; exact inner_add_left },
  have : continuous (λ p : E × E, inner' p.1 p.2) := continuous_inner,
  rw [completion.has_inner, uncurry_curry _],
  change continuous (((dense_inducing_to_compl E).prod (dense_inducing_to_compl E)).extend
    (λ p : E × E, inner' p.1 p.2)),
  exact (dense_inducing_to_compl E).extend_Z_bilin (dense_inducing_to_compl E) this,
end

protected lemma continuous.inner {α : Type*} [topological_space α]
  {f g : α → completion E} (hf : continuous f) (hg : continuous g) :
  continuous (λ x : α, inner (f x) (g x) : α → 𝕜) :=
uniform_space.completion.continuous_inner.comp (hf.prod_mk hg : _)

instance : inner_product_space 𝕜 (completion E) :=
{ to_normed_add_comm_group := infer_instance,
  norm_sq_eq_inner := λ x, completion.induction_on x
    (is_closed_eq
      (continuous_norm.pow 2)
      (continuous_re.comp (continuous.inner continuous_id' continuous_id')))
    (λ a, by simp only [norm_coe, inner_coe, inner_self_eq_norm_sq]),
  conj_sym := λ x y, completion.induction_on₂ x y
    (is_closed_eq
      (continuous_conj.comp (continuous.inner continuous_snd continuous_fst))
      (continuous.inner continuous_fst continuous_snd))
    (λ a b, by simp only [inner_coe, inner_conj_sym]),
  add_left := λ x y z, completion.induction_on₃ x y z
    (is_closed_eq
      (continuous.inner (continuous_fst.add (continuous_fst.comp continuous_snd))
        (continuous_snd.comp continuous_snd))
      ((continuous.inner continuous_fst (continuous_snd.comp continuous_snd)).add
        (continuous.inner (continuous_fst.comp continuous_snd)
          (continuous_snd.comp continuous_snd))))
    (λ a b c, by simp only [← coe_add, inner_coe, inner_add_left]),
  smul_left := λ x y c, completion.induction_on₂ x y
    (is_closed_eq
      (continuous.inner (continuous_fst.const_smul c) continuous_snd)
      ((continuous_mul_left _).comp (continuous.inner continuous_fst continuous_snd)))
    (λ a b, by simp only [← coe_smul c a, inner_coe, inner_smul_left]) }

end uniform_space.completion
