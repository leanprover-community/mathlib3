/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import analysis.seminorm

/-!
# Seminorms and norms on rings

This file defines seminorms and norms on rings. These definitions are useful when one needs to
consider multiple (semi)norms on a given ring.

## Main declarations

For a ring `R`:
* `ring_seminorm`: A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes
  nonnegative values, is subadditive and submultiplicative and such that `f (-x) = f x` for all
  `x ∈ R`.
* `ring_norm`: A seminorm `f` is a norm if `f x = 0` if and only if `x = 0`.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags
ring_seminorm, ring_norm
-/

noncomputable theory

set_option old_structure_cmd true

open_locale nnreal

variables {R S : Type*} (x y : R) (r : ℝ)

/-- A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes nonnegative
  values, is subadditive and submultiplicative and such that `f (-x) = f x` for all `x ∈ R`. -/
structure ring_seminorm (R : Type*) [non_unital_ring R]
  extends add_group_seminorm R :=
(mul_le' : ∀ x y : R, to_fun (x * y) ≤ to_fun x * to_fun y)

attribute [nolint doc_blame] ring_seminorm.to_add_group_seminorm

namespace ring_seminorm

section non_unital_ring

variables [non_unital_ring R]

instance zero_hom_class : zero_hom_class (ring_seminorm R) R ℝ :=
 { coe := λ f, f.to_fun,
   coe_injective' := λ f g h, by cases f; cases g; congr',
   map_zero := λ f, f.map_zero' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (ring_seminorm R) (λ _, R → ℝ) := ⟨λ p, p.to_fun⟩

@[ext] lemma ext {p q : ring_seminorm R} (h : ∀ x, p x = q x) : p = q :=
fun_like.ext p q h

instance : has_zero (ring_seminorm R) :=
⟨{ mul_le' :=  λ _ _, eq.ge (zero_mul _),
  ..add_group_seminorm.has_zero.zero }⟩

instance : inhabited (ring_seminorm R) := ⟨0⟩

variables (p : ring_seminorm R)

protected lemma nonneg : 0 ≤ p x := p.nonneg' _
@[simp] protected lemma map_zero : p 0 = 0 := p.map_zero'
protected lemma add_le : p (x + y) ≤ p x + p y := p.add_le' _ _
@[simp] protected lemma neg : p (- x) = p x := p.neg' _
protected lemma mul_le : p (x * y) ≤ p x * p y := p.mul_le' _ _

end non_unital_ring

section ring

variables [ring R] (p : ring_seminorm R)

lemma pow_le : ∀ {n : ℕ}, 0 < n → p (x ^ n) ≤ (p x) ^ n
| 1 h := by simp only [pow_one]
| (n + 2) h :=
by simpa only [pow_succ _ (n + 1)] using le_trans (p.mul_le x _)
  (mul_le_mul_of_nonneg_left (pow_le n.succ_pos) (p.nonneg _))

lemma seminorm_one_eq_one_iff_nonzero (hp : p 1 ≤ 1) :
  p 1 = 1 ↔ ∃ x : R, p x ≠ 0 :=
begin
  refine ⟨λ h, ⟨1, by {rw h, exact one_ne_zero}⟩, λ h, _⟩,
  obtain ⟨x, hx⟩ := h,
  by_cases hp0 : p 1 = 0,
  { have hx' : p x ≤ 0,
    { rw ← mul_one x,
      apply le_trans (p.mul_le x 1) _,
      rw [hp0, mul_zero], },
    exact absurd (le_antisymm hx' (p.nonneg x) ) hx },
  { have h1 : p 1 * 1 ≤ p 1 * p 1,
    { conv_lhs { rw ← one_mul (1 : R) },
      convert p.mul_le 1 1,
      rw mul_one, },
    rw mul_le_mul_left (lt_of_le_of_ne (p.nonneg _) (ne.symm hp0)) at h1,
    exact le_antisymm hp h1, }
end

end ring

end ring_seminorm

/-- The norm of a `non_unital_semi_normed_ring` as a `ring_seminorm`. -/
def norm_ring_seminorm (R : Type*) [non_unital_semi_normed_ring R] :
  ring_seminorm R :=
{ to_fun    := norm,
  map_zero' := norm_zero,
  nonneg'   := norm_nonneg,
  add_le'   := norm_add_le,
  neg'      := norm_neg,
  mul_le'   := norm_mul_le }

/-- A function `f : R → ℝ` is a norm if it is a seminorm and `f x = 0` implies `x = 0`. -/
structure ring_norm (R : Type*) [non_unital_ring R] extends (ring_seminorm R) :=
(ne_zero : ∀ x, x ≠ 0 → 0 < to_fun x)

attribute [nolint doc_blame] ring_norm.to_ring_seminorm

namespace ring_norm

variable [non_unital_ring R]

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (ring_norm R) (λ _, R → ℝ) := ⟨λ p, p.to_fun⟩

instance zero_hom_class : zero_hom_class (ring_norm R) R ℝ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_zero := λ f, f.map_zero' }

@[ext] lemma ext {p q : ring_norm R} (h : ∀ x, p x = q x) : p = q :=
fun_like.ext p q h

variable (R)

/-- The trivial norm on a ring `R` is the `ring_norm` taking value `0` at `0` and `1` at every
  other element. -/
def trivial_norm [decidable_eq R] : ring_norm R :=
{ mul_le'   := λ x y,
  begin by_cases h : x * y = 0,
    { simp only [add_group_seminorm.trivial_norm, if_pos h], apply mul_nonneg;
      { split_ifs, exacts [le_refl _, zero_le_one] }},
    { simp only [add_group_seminorm.to_fun_eq_coe, add_group_seminorm.trivial_norm_of_ne_zero h,
        add_group_seminorm.trivial_norm_of_ne_zero (left_ne_zero_of_mul h),
        add_group_seminorm.trivial_norm_of_ne_zero (right_ne_zero_of_mul h), mul_one] }
  end,
  ne_zero   := λ x hx,
  by { simp only [add_group_seminorm.trivial_norm, if_neg hx], exact zero_lt_one },
  ..add_group_seminorm.trivial_norm R }

instance [decidable_eq R] : inhabited (ring_norm R) := ⟨trivial_norm R⟩

/-- A nonzero ring seminorm on a field `K` is a ring norm. -/
def of_ring_seminorm {K : Type*} [field K] (f : ring_seminorm K)
  (hnt : ∃ r : K, 0 ≠ f r) : ring_norm K :=
{ ne_zero := λ x hx, begin
    obtain ⟨c, hc⟩ := hnt,
    have hfx : 0 ≠ f x,
    { intro h0,
      have hc' : f c ≤ 0,
      { rw [← mul_one c, ← mul_inv_cancel hx, ← mul_assoc, mul_comm c, mul_assoc],
        refine le_trans (f.mul_le x _) _,
        rw [← h0, zero_mul] },
      exact hc (ge_antisymm hc' (f.nonneg _)), },
    exact lt_of_le_of_ne (f.nonneg _) hfx,
  end,
  ..f }

end ring_norm

/-- The norm of a normed_ring as a ring_norm. -/
@[simps] def norm_ring_norm (R : Type*) [non_unital_normed_ring R] : ring_norm R :=
{ ne_zero := λ x, norm_pos_iff.mpr,
  ..norm_ring_seminorm R }
