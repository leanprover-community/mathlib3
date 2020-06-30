/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel
-/
import algebra.quadratic_discriminant
import linear_algebra.bilinear_form
import tactic.apply_fun
import tactic.monotonicity
import topology.metric_space.pi_Lp

/-!
# Inner Product Space

This file defines real inner product space and proves its basic properties.

An inner product space is a vector space endowed with an inner product. It generalizes the notion of
dot product in `ℝ^n` and provides the means of defining the length of a vector and the angle between
two vectors. In particular vectors `x` and `y` are orthogonal if their inner product equals zero.

## Main statements

Existence of orthogonal projection onto nonempty complete subspace:
Let `u` be a point in an inner product space, and let `K` be a nonempty complete subspace.
Then there exists a unique `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
The point `v` is usually called the orthogonal projection of `u` onto `K`.

## Implementation notes

We decide to develop the theory of real inner product spaces and that of complex inner product
spaces separately.

## Tags

inner product space, norm, orthogonal projection

## References
*  [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
*  [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/

noncomputable theory

open real set
open_locale big_operators
open_locale topological_space

universes u v w

variables {α : Type u} {F : Type v} {G : Type w}

/-- Syntactic typeclass for types endowed with an inner product -/
class has_inner (α : Type*) := (inner : α → α → ℝ)

export has_inner (inner)

section prio

set_option default_priority 100 -- see Note [default priority]

-- the norm is embedded in the inner product space structure
-- to avoid definitional equality issues. See Note [forgetful inheritance].

/--
An inner product space is a real vector space with an additional operation called inner product.
Inner product spaces over complex vector space will be defined in another file.
The norm could be derived from the inner product, instead we require the existence of a norm and
the fact that it is equal to `sqrt (inner x x)` to be able to put instances on `ℝ` or product
spaces.

To construct a norm from an inner product, see `inner_product_space.of_core`.
-/
class inner_product_space (α : Type*) extends normed_group α, normed_space ℝ α, has_inner α :=
(norm_eq_sqrt_inner : ∀ (x : α), ∥x∥ = sqrt (inner x x))
(comm      : ∀ x y, inner x y = inner y x)
(add_left  : ∀ x y z, inner (x + y) z = inner x z + inner y z)
(smul_left : ∀ x y r, inner (r • x) y = r * inner x y)
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
  (F : Type*) [add_comm_group F] [semimodule ℝ F] :=
(inner     : F → F → ℝ)
(comm      : ∀ x y, inner x y = inner y x)
(nonneg    : ∀ x, 0 ≤ inner x x)
(definite  : ∀ x, inner x x = 0 → x = 0)
(add_left  : ∀ x y z, inner (x + y) z = inner x z + inner y z)
(smul_left : ∀ x y r, inner (r • x) y = r * inner x y)

/- We set `inner_product_space.core` to be a class as we will use it as such in the construction
of the normed space structure that it produces. However, all the instances we will use will be
local to this proof. -/
attribute [class] inner_product_space.core

namespace inner_product_space.of_core

variables [add_comm_group F] [semimodule ℝ F] [c : inner_product_space.core F]
include c

/-- Inner product constructed from an `inner_product_space.core` structure -/
def to_has_inner : has_inner F :=
{ inner := c.inner }

local attribute [instance] to_has_inner

lemma inner_comm (x y : F) : inner x y = inner y x := c.comm x y

lemma inner_add_left (x y z : F) : inner (x + y) z = inner x z + inner y z :=
c.add_left _ _ _

lemma inner_add_right (x y z : F) : inner x (y + z) = inner x y + inner x z :=
by { rw [inner_comm, inner_add_left], simp [inner_comm] }

lemma inner_smul_left (x y : F) (r : ℝ) : inner (r • x) y = r * inner x y :=
c.smul_left _ _ _

lemma inner_smul_right (x y : F) (r : ℝ) : inner x (r • y) = r * inner x y :=
by { rw [inner_comm, inner_smul_left, inner_comm] }

/-- Norm constructed from an `inner_product_space.core` structure, defined to be the square root
of the scalar product. -/
def to_has_norm : has_norm F :=
{ norm := λ x, sqrt (inner x x) }

local attribute [instance] to_has_norm

lemma norm_eq_sqrt_inner (x : F) : ∥x∥ = sqrt (inner x x) := rfl

lemma inner_self_eq_norm_square (x : F) : inner x x = ∥x∥ * ∥x∥ :=
(mul_self_sqrt (c.nonneg _)).symm

/-- Expand `inner (x + y) (x + y)` -/
lemma inner_add_add_self (x y : F) : inner (x + y) (x + y) = inner x x + 2 * inner x y + inner y y :=
by simpa [inner_add_left, inner_add_right, two_mul, add_assoc] using inner_comm _ _

/-- Cauchy–Schwarz inequality -/
lemma inner_mul_inner_self_le (x y : F) : inner x y * inner x y ≤ inner x x * inner y y :=
begin
  have : ∀ t, 0 ≤ inner y y * t * t + 2 * inner x y * t + inner x x, from
    assume t, calc
      0 ≤ inner (x+t•y) (x+t•y) : c.nonneg _
      ... = inner y y * t * t + 2 * inner x y * t + inner x x :
        by { simp only [inner_add_add_self, inner_smul_right, inner_smul_left], ring },
  have := discriminant_le_zero this, rw discrim at this,
  have h : (2 * inner x y)^2 - 4 * inner y y * inner x x =
                      4 * (inner x y * inner x y - inner x x * inner y y) := by ring,
  rw h at this,
  linarith
end

/-- Cauchy–Schwarz inequality with norm -/
lemma abs_inner_le_norm (x y : F) : abs (inner x y) ≤ ∥x∥ * ∥y∥ :=
nonneg_le_nonneg_of_squares_le (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
begin
  rw abs_mul_abs_self,
  have : ∥x∥ * ∥y∥ * (∥x∥ * ∥y∥) = inner x x * inner y y,
    simp only [inner_self_eq_norm_square], ring,
  rw this,
  exact inner_mul_inner_self_le _ _
end

/-- Normed group structure constructed from an `inner_product_space.core` structure. -/
def to_normed_group : normed_group F :=
normed_group.of_core F
{ norm_eq_zero_iff := assume x,
    begin
      split,
      { assume h,
        rw [norm_eq_sqrt_inner,  sqrt_eq_zero] at h,
        { exact c.definite x h },
        { exact c.nonneg x } },
      { rintros rfl,
        have : inner ((0 : ℝ) • (0 : F)) 0 = 0 * inner (0 : F) 0 := inner_smul_left _ _ _,
        simp at this,
        simp [norm, this] }
    end,
  norm_neg := assume x,
    begin
      have A : (- (1 : ℝ)) • x = -x, by simp,
      rw [norm_eq_sqrt_inner, norm_eq_sqrt_inner, ← A, inner_smul_left, inner_smul_right],
      simp,
    end,
  triangle := assume x y,
  begin
    have := calc
      ∥x + y∥ * ∥x + y∥ = inner (x + y) (x + y) : by rw inner_self_eq_norm_square
      ... = inner x x + 2 * inner x y + inner y y : inner_add_add_self _ _
      ... ≤ inner x x + 2 * (∥x∥ * ∥y∥) + inner y y :
        by linarith [abs_inner_le_norm x y, le_abs_self (inner x y)]
      ... = (∥x∥ + ∥y∥) * (∥x∥ + ∥y∥) : by { simp only [inner_self_eq_norm_square], ring },
    exact nonneg_le_nonneg_of_squares_le (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this
  end }

local attribute [instance] to_normed_group

/-- Normed space structure constructed from an `inner_product_space.core` structure. -/
def to_normed_space : normed_space ℝ F :=
{ norm_smul_le := assume r x, le_of_eq $
  begin
    have A : 0 ≤ ∥r∥ * ∥x∥ := mul_nonneg (abs_nonneg _) (sqrt_nonneg _),
    rw [norm_eq_sqrt_inner, sqrt_eq_iff_mul_self_eq _ A,
        inner_smul_left, inner_smul_right, inner_self_eq_norm_square],
    { calc
        abs(r) * ∥x∥ * (abs(r) * ∥x∥) = (abs(r) * abs(r)) * (∥x∥ * ∥x∥) : by ring
        ... = r * (r * (∥x∥ * ∥x∥)) : by { rw abs_mul_abs_self, ring } },
    { exact c.nonneg _ }
  end }

end inner_product_space.of_core

/-- Given an `inner_product_space.core` structure on a space, one can use it to turn the space into
an inner product space, constructing the norm out of the inner product. -/
def inner_product_space.of_core [add_comm_group F] [semimodule ℝ F]
  (c : inner_product_space.core F) : inner_product_space F :=
begin
  letI : normed_group F := @inner_product_space.of_core.to_normed_group F _ _ c,
  letI : normed_space ℝ F := @inner_product_space.of_core.to_normed_space F _ _ c,
  exact { norm_eq_sqrt_inner := λ x, rfl, .. c }
end

/-! ### Properties of inner product spaces -/

variables [inner_product_space α]

export inner_product_space (norm_eq_sqrt_inner)

section basic_properties

lemma inner_comm (x y : α) : inner x y = inner y x := inner_product_space.comm x y

lemma inner_add_left {x y z : α} : inner (x + y) z = inner x z + inner y z :=
inner_product_space.add_left _ _ _

lemma inner_add_right {x y z : α} : inner x (y + z) = inner x y + inner x z :=
by { rw [inner_comm, inner_add_left], simp [inner_comm] }

lemma inner_smul_left {x y : α} {r : ℝ} : inner (r • x) y = r * inner x y :=
inner_product_space.smul_left _ _ _

lemma inner_smul_right {x y : α} {r : ℝ} : inner x (r • y) = r * inner x y :=
by { rw [inner_comm, inner_smul_left, inner_comm] }

variables (α)

/-- The inner product as a bilinear form. -/
def bilin_form_of_inner : bilin_form ℝ α :=
{ bilin := inner,
  bilin_add_left := λ x y z, inner_add_left,
  bilin_smul_left := λ a x y, inner_smul_left,
  bilin_add_right := λ x y z, inner_add_right,
  bilin_smul_right := λ a x y, inner_smul_right }

variables {α}

/-- An inner product with a sum on the left. -/
lemma sum_inner {ι : Type*} (s : finset ι) (f : ι → α) (x : α) :
  inner (∑ i in s, f i) x = ∑ i in s, inner (f i) x :=
bilin_form.map_sum_left (bilin_form_of_inner α) _ _ _

/-- An inner product with a sum on the right. -/
lemma inner_sum {ι : Type*} (s : finset ι) (f : ι → α) (x : α) :
  inner x (∑ i in s, f i) = ∑ i in s, inner x (f i) :=
bilin_form.map_sum_right (bilin_form_of_inner α) _ _ _

@[simp] lemma inner_zero_left {x : α} : inner 0 x = 0 :=
by { rw [← zero_smul ℝ (0:α), inner_smul_left, zero_mul] }

@[simp] lemma inner_zero_right {x : α} : inner x 0 = 0 :=
by { rw [inner_comm, inner_zero_left] }

@[simp] lemma inner_self_eq_zero {x : α} : inner x x = 0 ↔ x = 0 :=
⟨λ h, by simpa [h] using norm_eq_sqrt_inner x, λ h, by simp [h]⟩

lemma inner_self_nonneg {x : α} : 0 ≤ inner x x :=
begin
  classical,
  by_cases h : x = 0,
  { simp [h] },
  { have : 0 < sqrt (inner x x),
    { rw ← norm_eq_sqrt_inner,
      exact norm_pos_iff.mpr h },
    exact le_of_lt (sqrt_pos.1 this) }
end

@[simp] lemma inner_self_nonpos {x : α} : inner x x ≤ 0 ↔ x = 0 :=
⟨λ h, inner_self_eq_zero.1 (le_antisymm h inner_self_nonneg),
  λ h, h.symm ▸ le_of_eq inner_zero_left⟩

@[simp] lemma inner_neg_left {x y : α} : inner (-x) y = -inner x y :=
by { rw [← neg_one_smul ℝ x, inner_smul_left], simp }

@[simp] lemma inner_neg_right {x y : α} : inner x (-y) = -inner x y :=
by { rw [inner_comm, inner_neg_left, inner_comm] }

@[simp] lemma inner_neg_neg {x y : α} : inner (-x) (-y) = inner x y := by simp

lemma inner_sub_left {x y z : α} : inner (x - y) z = inner x z - inner y z :=
by { simp [sub_eq_add_neg, inner_add_left] }

lemma inner_sub_right {x y z : α} : inner x (y - z) = inner x y - inner x z :=
by { simp [sub_eq_add_neg, inner_add_right] }

/-- Expand `inner (x + y) (x + y)` -/
lemma inner_add_add_self {x y : α} : inner (x + y) (x + y) = inner x x + 2 * inner x y + inner y y :=
by simpa [inner_add_left, inner_add_right, two_mul, add_assoc] using inner_comm _ _

/-- Expand `inner (x - y) (x - y)` -/
lemma inner_sub_sub_self {x y : α} : inner (x - y) (x - y) = inner x x - 2 * inner x y + inner y y :=
begin
  simp only [inner_sub_left, inner_sub_right, two_mul],
  simpa [sub_eq_add_neg, add_comm, add_left_comm] using inner_comm _ _
end

/-- Parallelogram law -/
lemma parallelogram_law {x y : α} :
  inner (x + y) (x + y) + inner (x - y) (x - y) = 2 * (inner x x + inner y y) :=
by simp [inner_add_add_self, inner_sub_sub_self, two_mul, sub_eq_add_neg, add_comm, add_left_comm]

/-- Cauchy–Schwarz inequality -/
lemma inner_mul_inner_self_le (x y : α) : inner x y * inner x y ≤ inner x x * inner y y :=
begin
  have : ∀ t, 0 ≤ inner y y * t * t + 2 * inner x y * t + inner x x, from
    assume t, calc
      0 ≤ inner (x+t•y) (x+t•y) : inner_self_nonneg
      ... = inner y y * t * t + 2 * inner x y * t + inner x x :
        by { simp only [inner_add_add_self, inner_smul_right, inner_smul_left], ring },
  have := discriminant_le_zero this, rw discrim at this,
  have h : (2 * inner x y)^2 - 4 * inner y y * inner x x =
                      4 * (inner x y * inner x y - inner x x * inner y y) := by ring,
  rw h at this,
  linarith
end

end basic_properties

section norm

lemma inner_self_eq_norm_square (x : α) : inner x x = ∥x∥ * ∥x∥ :=
by { rw norm_eq_sqrt_inner, exact (mul_self_sqrt inner_self_nonneg).symm }

/-- Expand the square -/
lemma norm_add_pow_two {x y : α} : ∥x + y∥^2 = ∥x∥^2 + 2 * inner x y + ∥y∥^2 :=
by { repeat {rw [pow_two, ← inner_self_eq_norm_square]}, exact inner_add_add_self }

/-- Same lemma as above but in a different form -/
lemma norm_add_mul_self {x y : α} : ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + 2 * inner x y + ∥y∥ * ∥y∥ :=
by { repeat {rw [← pow_two]}, exact norm_add_pow_two }

/-- Expand the square -/
lemma norm_sub_pow_two {x y : α} : ∥x - y∥^2 = ∥x∥^2 - 2 * inner x y + ∥y∥^2 :=
by { repeat {rw [pow_two, ← inner_self_eq_norm_square]}, exact inner_sub_sub_self }

/-- Same lemma as above but in a different form -/
lemma norm_sub_mul_self {x y : α} : ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ - 2 * inner x y + ∥y∥ * ∥y∥ :=
by { repeat {rw [← pow_two]}, exact norm_sub_pow_two }

/-- Cauchy–Schwarz inequality with norm -/
lemma abs_inner_le_norm (x y : α) : abs (inner x y) ≤ ∥x∥ * ∥y∥ :=
nonneg_le_nonneg_of_squares_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
begin
  rw abs_mul_abs_self,
  have : ∥x∥ * ∥y∥ * (∥x∥ * ∥y∥) = inner x x * inner y y,
    simp only [inner_self_eq_norm_square], ring,
  rw this,
  exact inner_mul_inner_self_le _ _
end

lemma parallelogram_law_with_norm {x y : α} :
  ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥) :=
by { simp only [(inner_self_eq_norm_square _).symm], exact parallelogram_law }

/-- The inner product, in terms of the norm. -/
lemma inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : α) :
  inner x y = (∥x + y∥ * ∥x + y∥ - ∥x∥ * ∥x∥ - ∥y∥ * ∥y∥) / 2 :=
begin
  rw norm_add_mul_self,
  ring
end

/-- The inner product, in terms of the norm. -/
lemma inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : α) :
  inner x y = (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ - ∥x - y∥ * ∥x - y∥) / 2 :=
begin
  rw norm_sub_mul_self,
  ring
end

/-- The inner product, in terms of the norm. -/
lemma inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (x y : α) :
  inner x y = (∥x + y∥ * ∥x + y∥ - ∥x - y∥ * ∥x - y∥) / 4 :=
begin
  rw [norm_add_mul_self, norm_sub_mul_self],
  ring
end

/-- Pythagorean theorem, if-and-only-if vector inner product form. -/
lemma norm_add_square_eq_norm_square_add_norm_square_iff_inner_eq_zero (x y : α) :
  ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ inner x y = 0 :=
begin
  rw [norm_add_mul_self, add_right_cancel_iff, add_right_eq_self, mul_eq_zero],
  norm_num
end

/-- Pythagorean theorem, vector inner product form. -/
lemma norm_add_square_eq_norm_square_add_norm_square {x y : α} (h : inner x y = 0) :
  ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ :=
(norm_add_square_eq_norm_square_add_norm_square_iff_inner_eq_zero x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector
inner product form. -/
lemma norm_sub_square_eq_norm_square_add_norm_square_iff_inner_eq_zero (x y : α) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ inner x y = 0 :=
begin
  rw [norm_sub_mul_self, add_right_cancel_iff, sub_eq_add_neg, add_right_eq_self, neg_eq_zero,
      mul_eq_zero],
  norm_num
end

/-- Pythagorean theorem, subtracting vectors, vector inner product
form. -/
lemma norm_sub_square_eq_norm_square_add_norm_square {x y : α} (h : inner x y = 0) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ :=
(norm_sub_square_eq_norm_square_add_norm_square_iff_inner_eq_zero x y).2 h

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value at most 1. -/
lemma abs_inner_div_norm_mul_norm_le_one (x y : α) : abs (inner x y / (∥x∥ * ∥y∥)) ≤ 1 :=
begin
  rw abs_div,
  by_cases h : 0 = abs (∥x∥ * ∥y∥),
  { rw [←h, div_zero],
    norm_num },
  { apply div_le_of_le_mul (lt_of_le_of_ne (ge_iff_le.mp (abs_nonneg (∥x∥ * ∥y∥))) h),
    convert abs_inner_le_norm x y using 1,
    rw [abs_mul, abs_of_nonneg (norm_nonneg x), abs_of_nonneg (norm_nonneg y), mul_one] }
end

/-- The inner product of a vector with a multiple of itself. -/
lemma inner_smul_self_left (x : α) (r : ℝ) : inner (r • x) x = r * (∥x∥ * ∥x∥) :=
by rw [inner_smul_left, ←inner_self_eq_norm_square]

/-- The inner product of a vector with a multiple of itself. -/
lemma inner_smul_self_right (x : α) (r : ℝ) : inner x (r • x) = r * (∥x∥ * ∥x∥) :=
by rw [inner_smul_right, ←inner_self_eq_norm_square]

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
lemma abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
  {x : α} {r : ℝ} (hx : x ≠ 0) (hr : r ≠ 0) : abs (inner x (r • x) / (∥x∥ * ∥r • x∥)) = 1 :=
begin
  rw [inner_smul_self_right, norm_smul, real.norm_eq_abs, ←mul_assoc ∥x∥, mul_comm _ (abs r),
      mul_assoc, abs_div, abs_mul r, abs_mul (abs r), abs_abs, div_self],
  exact mul_ne_zero (λ h, hr (eq_zero_of_abs_eq_zero h))
    (λ h, hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero (eq_zero_of_abs_eq_zero h))))
end

/-- The inner product of a nonzero vector with a positive multiple of
itself, divided by the product of their norms, has value 1. -/
lemma inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul
  {x : α} {r : ℝ} (hx : x ≠ 0) (hr : 0 < r) : inner x (r • x) / (∥x∥ * ∥r • x∥) = 1 :=
begin
  rw [inner_smul_self_right, norm_smul, real.norm_eq_abs, ←mul_assoc ∥x∥, mul_comm _ (abs r),
      mul_assoc, abs_of_nonneg (le_of_lt hr), div_self],
  exact mul_ne_zero (ne_of_gt hr)
    (λ h, hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero h)))
end

/-- The inner product of a nonzero vector with a negative multiple of
itself, divided by the product of their norms, has value -1. -/
lemma inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul
  {x : α} {r : ℝ} (hx : x ≠ 0) (hr : r < 0) : inner x (r • x) / (∥x∥ * ∥r • x∥) = -1 :=
begin
  rw [inner_smul_self_right, norm_smul, real.norm_eq_abs, ←mul_assoc ∥x∥, mul_comm _ (abs r),
      mul_assoc, abs_of_neg hr, ←neg_mul_eq_neg_mul, div_neg_eq_neg_div, div_self],
  exact mul_ne_zero (ne_of_lt hr)
    (λ h, hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero h)))
end

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
lemma abs_inner_div_norm_mul_norm_eq_one_iff (x y : α) :
  abs (inner x y / (∥x∥ * ∥y∥)) = 1 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), r ≠ 0 ∧ y = r • x) :=
begin
  split,
  { intro h,
    have hx0 : x ≠ 0,
    { intro hx0,
      rw [hx0, inner_zero_left, zero_div] at h,
      norm_num at h,
      exact h },
    refine and.intro hx0 _,
    set r := inner x y / (∥x∥ * ∥x∥) with hr,
    use r,
    set t := y - r • x with ht,
    have ht0 : inner x t = 0,
    { rw [ht, inner_sub_right, inner_smul_right, hr, ←inner_self_eq_norm_square,
          div_mul_cancel _ (λ h, hx0 (inner_self_eq_zero.1 h)), sub_self] },
    rw [←sub_add_cancel y (r • x), ←ht, inner_add_right, ht0, zero_add, inner_smul_right,
        inner_self_eq_norm_square, ←mul_assoc, mul_comm,
        mul_div_mul_left _ _ (λ h, hx0 (norm_eq_zero.1 h)), abs_div, abs_mul,
        abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _), ←real.norm_eq_abs,
        ←norm_smul] at h,
    have hr0 : r ≠ 0,
    { intro hr0,
      rw [hr0, zero_smul, norm_zero, zero_div] at h,
      norm_num at h },
    refine and.intro hr0 _,
    have h2 : ∥r • x∥ ^ 2 = ∥t + r • x∥ ^ 2,
    { congr' 1,
      refine eq_of_div_eq_one _ _ h,
      intro h0,
      rw [h0, div_zero] at h,
      norm_num at h },
    rw [pow_two, pow_two, ←inner_self_eq_norm_square, ←inner_self_eq_norm_square,
        inner_add_add_self] at h2,
    conv_rhs at h2 {
      congr,
      congr,
      skip,
      rw [inner_smul_right, inner_comm, ht0, mul_zero, mul_zero]
    },
    symmetry' at h2,
    rw [add_zero, add_left_eq_self, inner_self_eq_zero] at h2,
    rw h2 at ht,
    exact eq_of_sub_eq_zero ht.symm },
  { intro h,
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    rw hy,
    exact abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr }
end

/-- The inner product of two vectors, divided by the product of their
norms, has value 1 if and only if they are nonzero and one is
a positive multiple of the other. -/
lemma inner_div_norm_mul_norm_eq_one_iff (x y : α) :
  inner x y / (∥x∥ * ∥y∥) = 1 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), 0 < r ∧ y = r • x) :=
begin
  split,
  { intro h,
    have ha := h,
    apply_fun abs at ha,
    norm_num at ha,
    rcases (abs_inner_div_norm_mul_norm_eq_one_iff x y).1 ha with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    use [hx, r],
    refine and.intro _ hy,
    by_contradiction hrneg,
    rw hy at h,
    rw inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul hx
      (lt_of_le_of_ne' (le_of_not_lt hrneg) hr) at h,
    norm_num at h },
  { intro h,
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    rw hy,
    exact inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx hr }
end

/-- The inner product of two vectors, divided by the product of their
norms, has value -1 if and only if they are nonzero and one is
a negative multiple of the other. -/
lemma inner_div_norm_mul_norm_eq_neg_one_iff (x y : α) :
  inner x y / (∥x∥ * ∥y∥) = -1 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), r < 0 ∧ y = r • x) :=
begin
  split,
  { intro h,
    have ha := h,
    apply_fun abs at ha,
    norm_num at ha,
    rcases (abs_inner_div_norm_mul_norm_eq_one_iff x y).1 ha with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    use [hx, r],
    refine and.intro _ hy,
    by_contradiction hrpos,
    rw hy at h,
    rw inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx
      (lt_of_le_of_ne' (le_of_not_lt hrpos) hr.symm) at h,
    norm_num at h },
  { intro h,
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    rw hy,
    exact inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul hx hr }
end

/-- The inner product of two weighted sums, where the weights in each
sum add to 0, in terms of the norms of pairwise differences. -/
lemma inner_sum_smul_sum_smul_of_sum_eq_zero {ι₁ : Type*} {s₁ : finset ι₁} {w₁ : ι₁ → ℝ}
    (v₁ : ι₁ → α) (h₁ : ∑ i in s₁, w₁ i = 0) {ι₂ : Type*} {s₂ : finset ι₂} {w₂ : ι₂ → ℝ}
    (v₂ : ι₂ → α) (h₂ : ∑ i in s₂, w₂ i = 0) :
  inner (∑ i₁ in s₁, w₁ i₁ • v₁ i₁) (∑ i₂ in s₂, w₂ i₂ • v₂ i₂) =
    (-∑ i₁ in s₁, ∑ i₂ in s₂, w₁ i₁ * w₂ i₂ * (∥v₁ i₁ - v₂ i₂∥ * ∥v₁ i₁ - v₂ i₂∥)) / 2 :=
by simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
            inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
            ←div_sub_div_same, ←div_add_div_same, mul_sub_left_distrib, left_distrib,
            finset.sum_sub_distrib, finset.sum_add_distrib, ←finset.mul_sum, ←finset.sum_mul,
            h₁, h₂, zero_mul, mul_zero, finset.sum_const_zero, zero_add, zero_sub, finset.mul_sum,
            neg_div, finset.sum_div, mul_div_assoc, mul_assoc]

end norm

/-! ### Inner product space structure on product spaces -/

-- TODO [Lean 3.15]: drop some of these `show`s
/-- If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space,
then `Π i, f i` is an inner product space as well. Since `Π i, f i` is endowed with the sup norm,
we use instead `pi_Lp 2 one_le_two f` for the product space, which is endowed with the `L^2` norm.
-/
instance pi_Lp.inner_product_space
  (ι : Type*) [fintype ι] (f : ι → Type*) [Π i, inner_product_space (f i)] :
  inner_product_space (pi_Lp 2 one_le_two f) :=
{ inner := λ x y, ∑ i, inner (x i) (y i),
  norm_eq_sqrt_inner := begin
    assume x,
    have : (2 : ℝ)⁻¹ * 2 = 1, by norm_num,
    simp [inner, pi_Lp.norm_eq, norm_eq_sqrt_inner, sqrt_eq_rpow, ← rpow_mul (inner_self_nonneg),
          this],
  end,
  comm := λ x y, finset.sum_congr rfl $ λ i hi, inner_comm (x i) (y i),
  add_left := λ x y z,
    show ∑ i, inner (x i + y i) (z i) = ∑ i, inner (x i) (z i) + ∑ i, inner (y i) (z i),
    by simp only [inner_add_left, finset.sum_add_distrib],
  smul_left := λ x y r,
    show ∑ (i : ι), inner (r • x i) (y i) = r * ∑ i, inner (x i) (y i),
    by simp only [finset.mul_sum, inner_smul_left] }

/-- The type of real numbers is an inner product space. -/
instance real.inner_product_space : inner_product_space ℝ :=
{ inner := (*),
  norm_eq_sqrt_inner := λ x, by simp [inner, norm_eq_abs, sqrt_mul_self_eq_abs],
  comm := mul_comm,
  add_left := add_mul,
  smul_left := λ _ _ _, mul_assoc _ _ _ }

/-- The standard Euclidean space, functions on a finite type. For an `n`-dimensional space
use `euclidean_space (fin n)`.  -/
@[reducible, nolint unused_arguments]
def euclidean_space (n : Type*) [fintype n] : Type* := pi_Lp 2 one_le_two (λ (i : n), ℝ)

section pi_Lp
local attribute [reducible] pi_Lp
variables (n : Type*) [fintype n]

instance : finite_dimensional ℝ (euclidean_space n) :=
by apply_instance

@[simp] lemma findim_euclidean_space :
  finite_dimensional.findim ℝ (euclidean_space n) = fintype.card n :=
by simp

lemma findim_euclidean_space_fin {n : ℕ} :
  finite_dimensional.findim ℝ (euclidean_space (fin n)) = n :=
by simp

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
theorem exists_norm_eq_infi_of_complete_convex {K : set α} (ne : K.nonempty) (h₁ : is_complete K)
  (h₂ : convex K) : ∀ u : α, ∃ v ∈ K, ∥u - v∥ = ⨅ w : K, ∥u - w∥ := assume u,
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
  have norm_tendsto : tendsto (λ n, ∥u - w n∥) at_top (𝓝 δ),
  { have h : tendsto (λ n:ℕ, δ) at_top (𝓝 δ) := tendsto_const_nhds,
    have h' : tendsto (λ n:ℕ, δ + 1 / (n + 1)) at_top (𝓝 δ),
    { convert h.add tendsto_one_div_add_at_top_nhds_0_nat, simp only [add_zero] },
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h h'
      (λ x, δ_le _) (λ x, le_of_lt (hw _)) },
  -- Step 2: Prove that the sequence `w : ℕ → K` is a Cauchy sequence
  have seq_is_cauchy : cauchy_seq (λ n, ((w n):α)),
  { rw cauchy_seq_iff_le_tendsto_0, -- splits into three goals
    let b := λ n:ℕ, (8 * δ * (1/(n+1)) + 4 * (1/(n+1)) * (1/(n+1))),
    use (λn, sqrt (b n)),
    split,
    -- first goal :  `∀ (n : ℕ), 0 ≤ sqrt (b n)`
    assume n, exact sqrt_nonneg _,
    split,
    -- second goal : `∀ (n m N : ℕ), N ≤ n → N ≤ m → dist ↑(w n) ↑(w m) ≤ sqrt (b N)`
    assume p q N hp hq,
    let wp := ((w p):α), let wq := ((w q):α),
    let a := u - wq, let b := u - wp,
    let half := 1 / (2:ℝ), let div := 1 / ((N:ℝ) + 1),
    have : 4 * ∥u - half • (wq + wp)∥ * ∥u - half • (wq + wp)∥ + ∥wp - wq∥ * ∥wp - wq∥ =
      2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) :=
    calc
      4 * ∥u - half•(wq + wp)∥ * ∥u - half•(wq + wp)∥ + ∥wp - wq∥ * ∥wp - wq∥
          = (2*∥u - half•(wq + wp)∥) * (2 * ∥u - half•(wq + wp)∥) + ∥wp-wq∥*∥wp-wq∥ : by ring
      ... = (abs((2:ℝ)) * ∥u - half•(wq + wp)∥) * (abs((2:ℝ)) * ∥u - half•(wq+wp)∥) + ∥wp-wq∥*∥wp-wq∥ :
      by { rw abs_of_nonneg, exact add_nonneg zero_le_one zero_le_one }
      ... = ∥(2:ℝ) • (u - half • (wq + wp))∥ * ∥(2:ℝ) • (u - half • (wq + wp))∥ + ∥wp-wq∥ * ∥wp-wq∥ :
        by { rw [norm_smul], refl }
      ... = ∥a + b∥ * ∥a + b∥ + ∥a - b∥ * ∥a - b∥ :
      begin
        rw [smul_sub, smul_smul, mul_one_div_cancel (two_ne_zero : (2 : ℝ) ≠ 0),
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
    have eq₁ : tendsto (λ (n : ℕ), 8 * δ * (1 / (n + 1))) at_top (𝓝 (0:ℝ)),
    { convert (@tendsto_const_nhds _ _ _ (8 * δ) _).mul tendsto_one_div_add_at_top_nhds_0_nat,
      simp only [mul_zero] },
    have : tendsto (λ (n : ℕ), (4:ℝ) * (1 / (n + 1))) at_top (𝓝 (0:ℝ)),
    { convert (@tendsto_const_nhds _ _ _ (4:ℝ) _).mul tendsto_one_div_add_at_top_nhds_0_nat,
      simp only [mul_zero] },
    have eq₂ : tendsto (λ (n : ℕ), (4:ℝ) * (1 / (n + 1)) * (1 / (n + 1))) at_top (𝓝 (0:ℝ)),
    { convert this.mul tendsto_one_div_add_at_top_nhds_0_nat,
      simp only [mul_zero] },
    convert eq₁.add eq₂, simp only [add_zero] },
  -- Step 3: By completeness of `K`, let `w : ℕ → K` converge to some `v : K`.
  -- Prove that it satisfies all requirements.
  rcases cauchy_seq_tendsto_of_is_complete h₁ (λ n, _) seq_is_cauchy with ⟨v, hv, w_tendsto⟩,
  use v, use hv,
  have h_cont : continuous (λ v, ∥u - v∥) :=
    continuous.comp continuous_norm (continuous.sub continuous_const continuous_id),
  have : tendsto (λ n, ∥u - w n∥) at_top (𝓝 ∥u - v∥),
    convert (tendsto.comp h_cont.continuous_at w_tendsto),
  exact tendsto_nhds_unique at_top_ne_bot this norm_tendsto,
  exact subtype.mem _
end

/-- Characterization of minimizers in the above theorem -/
theorem norm_eq_infi_iff_inner_le_zero {K : set α} (h : convex K) {u : α} {v : α}
  (hv : v ∈ K) : ∥u - v∥ = (⨅ w : K, ∥u - w∥) ↔ ∀ w ∈ K, inner (u - v) (w - v) ≤ 0 :=
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
theorem exists_norm_eq_infi_of_complete_subspace (K : subspace ℝ α)
  (h : is_complete (↑K : set α)) : ∀ u : α, ∃ v ∈ K, ∥u - v∥ = ⨅ w : (↑K : set α), ∥u - w∥ :=
exists_norm_eq_infi_of_complete_convex ⟨0, K.zero_mem⟩ h K.convex

/--
Characterization of minimizers in the above theorem.
Let `u` be a point in an inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `∥u - v∥` if and only if
for all `w ∈ K`, `inner (u - v) w = 0` (i.e., `u - v` is orthogonal to the subspace `K`)
-/
theorem norm_eq_infi_iff_inner_eq_zero (K : subspace ℝ α) {u : α} {v : α}
  (hv : v ∈ K) : ∥u - v∥ = (⨅ w : (↑K : set α), ∥u - w∥) ↔ ∀ w ∈ K, inner (u - v) w = 0 :=
iff.intro
begin
  assume h,
  have h : ∀ w ∈ K, inner (u - v) (w - v) ≤ 0,
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
    have h₂ : w'' - v = -w, simp only [neg_inj', add_neg_cancel_right, sub_eq_add_neg],
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

end orthogonal
