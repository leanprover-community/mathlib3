/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import algebra.big_operators
import analysis.normed_space.real_inner_product
import analysis.normed_space.add_torsor

noncomputable theory
open_locale big_operators

/-!
# Euclidean spaces

This file defines Euclidean affine spaces.

## Implementation notes

Rather than requiring Euclidean affine spaces to be finite-dimensional
(as in the definition on Wikipedia), this is specified only for those
theorems that need it.

## References

* https://en.wikipedia.org/wiki/Euclidean_space

-/

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A `euclidean_affine_space V P` is an affine space with points `P`
over an `inner_product_space V`. -/
class euclidean_affine_space (V : Type*) (P : Type*) [inner_product_space V] [metric_space P]
  extends normed_add_torsor V P
end prio

/-- The standard Euclidean space, fin n → ℝ. -/
instance standard_euclidean_space_is_vector_space (n : ℕ) : vector_space ℝ (fin n → ℝ) :=
by apply_instance
instance standard_euclidean_space_has_inner (n : ℕ) : has_inner (fin n → ℝ) :=
{ inner := λ a b, ∑ i, a i * b i }
instance standard_euclidean_space_is_inner_product_space (n : ℕ) :
  inner_product_space (fin n → ℝ) :=
{ comm := begin
    intros x y,
    unfold inner,
    conv_lhs {
      congr,
      skip,
      funext,
      rw mul_comm
    }
  end,
  nonneg := begin
    intro x,
    unfold inner,
    exact finset.sum_nonneg (λ i hi, mul_self_nonneg _)
  end,
  definite := begin
    intro x,
    unfold inner,
    intro h,
    rw finset.sum_eq_zero_iff_of_nonneg at h,
    { ext i,
      replace h := h i (finset.mem_univ _),
      change x i = 0,
      rwa [mul_eq_zero_iff', or_self] at h },
    { exact λ i hi, mul_self_nonneg _ }
  end,
  add_left := begin
    intros x y z,
    unfold inner,
    convert finset.sum_add_distrib,
    conv_lhs {
      funext,
      rw [(show (x + y) i = x i + y i, by refl), right_distrib]
    }
  end,
  smul_left := begin
    intros x y r,
    unfold inner,
    rw finset.mul_sum,
    conv_lhs {
      funext,
      congr,
      skip,
      funext,
      rw [(show (r • x) i = r * x i, by refl), mul_assoc]
    }
  end }
instance standard_euclidean_affine_space_normed_group (n : ℕ) : normed_group (fin n → ℝ) :=
inner_product_space_is_normed_group
instance standard_euclidean_affine_space_metric_space (n : ℕ) : metric_space (fin n → ℝ) :=
normed_group.to_metric_space
instance standard_euclidean_affine_space (n : ℕ) :
  euclidean_affine_space (fin n → ℝ) (fin n → ℝ) :=
{ dist_eq_norm' := normed_group.dist_eq }
