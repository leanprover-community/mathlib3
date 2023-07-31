/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Yaël Dillies
-/
import analysis.normed.field.basic

/-!
# Seminorms and norms on rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines seminorms and norms on rings. These definitions are useful when one needs to
consider multiple (semi)norms on a given ring.

## Main declarations

For a ring `R`:
* `ring_seminorm`: A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes
  nonnegative values, is subadditive and submultiplicative and such that `f (-x) = f x` for all
  `x ∈ R`.
* `ring_norm`: A seminorm `f` is a norm if `f x = 0` if and only if `x = 0`.
* `mul_ring_seminorm`: A multiplicative seminorm on a ring `R` is a ring seminorm that preserves
  multiplication.
* `mul_ring_norm`: A multiplicative norm on a ring `R` is a ring norm that preserves multiplication.

## Notes

The corresponding hom classes are defined in `analysis.order.hom.basic` to be used by absolute
values.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags
ring_seminorm, ring_norm
-/

set_option old_structure_cmd true

open_locale nnreal

variables {F R S : Type*} (x y : R) (r : ℝ)

/-- A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes nonnegative
  values, is subadditive and submultiplicative and such that `f (-x) = f x` for all `x ∈ R`. -/
structure ring_seminorm (R : Type*) [non_unital_non_assoc_ring R]
  extends add_group_seminorm R :=
(mul_le' : ∀ x y : R, to_fun (x * y) ≤ to_fun x * to_fun y)

/-- A function `f : R → ℝ` is a norm on a (nonunital) ring if it is a seminorm and `f x = 0`
  implies `x = 0`. -/
structure ring_norm (R : Type*) [non_unital_non_assoc_ring R]
  extends ring_seminorm R, add_group_norm R

/-- A multiplicative seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero and
multiplication, takes nonnegative values, is subadditive and such that `f (-x) = f x` for all `x`.
-/
structure mul_ring_seminorm (R : Type*) [non_assoc_ring R]
  extends add_group_seminorm R, monoid_with_zero_hom R ℝ

/-- A multiplicative norm on a ring `R` is a multiplicative ring seminorm such that `f x = 0`
implies `x = 0`. -/
structure mul_ring_norm (R : Type*) [non_assoc_ring R] extends mul_ring_seminorm R, add_group_norm R

attribute [nolint doc_blame] ring_seminorm.to_add_group_seminorm ring_norm.to_add_group_norm
  ring_norm.to_ring_seminorm mul_ring_seminorm.to_add_group_seminorm
  mul_ring_seminorm.to_monoid_with_zero_hom mul_ring_norm.to_add_group_norm
  mul_ring_norm.to_mul_ring_seminorm

namespace ring_seminorm

section non_unital_ring

variables [non_unital_ring R]

instance ring_seminorm_class : ring_seminorm_class (ring_seminorm R) R ℝ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_zero := λ f, f.map_zero',
  map_add_le_add := λ f, f.add_le',
  map_mul_le_mul := λ f, f.mul_le',
  map_neg_eq_map := λ f, f.neg' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (ring_seminorm R) (λ _, R → ℝ) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe (p : ring_seminorm R) : p.to_fun = p := rfl

@[ext] lemma ext {p q : ring_seminorm R} : (∀ x, p x = q x) → p = q := fun_like.ext p q

instance : has_zero (ring_seminorm R) :=
⟨{ mul_le' := λ _ _, (zero_mul _).ge,
  ..add_group_seminorm.has_zero.zero }⟩

lemma eq_zero_iff {p : ring_seminorm R} : p = 0 ↔ ∀ x, p x = 0 := fun_like.ext_iff
lemma ne_zero_iff {p : ring_seminorm R} : p ≠ 0 ↔ ∃ x, p x ≠ 0 := by simp [eq_zero_iff]

instance : inhabited (ring_seminorm R) := ⟨0⟩

/-- The trivial seminorm on a ring `R` is the `ring_seminorm` taking value `0` at `0` and `1` at
every other element. -/
instance [decidable_eq R] : has_one (ring_seminorm R) :=
⟨{ mul_le' := λ x y, begin
    by_cases h : x * y = 0,
    { refine (if_pos h).trans_le (mul_nonneg _ _);
      { change _ ≤ ite _ _ _,
        split_ifs,
        exacts [le_rfl, zero_le_one] } },
    { change ite _ _ _ ≤ ite _ _ _ * ite _ _ _,
      simp only [if_false, h, left_ne_zero_of_mul h, right_ne_zero_of_mul h, mul_one] }
  end,
  ..(1 : add_group_seminorm R) }⟩

@[simp] lemma apply_one [decidable_eq R] (x : R) :
  (1 : ring_seminorm R) x = if x = 0 then 0 else 1 := rfl

end non_unital_ring

section ring

variables [ring R] (p : ring_seminorm R)

lemma seminorm_one_eq_one_iff_ne_zero (hp : p 1 ≤ 1) :
  p 1 = 1 ↔ p ≠ 0 :=
begin
  refine ⟨λ h, ne_zero_iff.mpr ⟨1, by {rw h, exact one_ne_zero}⟩, λ h, _⟩,
  obtain hp0 | hp0 := (map_nonneg p (1 : R)).eq_or_gt,
  { cases h (ext $ λ x, (map_nonneg _ _).antisymm' _),
    simpa only [hp0, mul_one, mul_zero] using map_mul_le_mul p x 1},
  { refine hp.antisymm ((le_mul_iff_one_le_left hp0).1 _),
    simpa only [one_mul] using map_mul_le_mul p (1 : R) _ }
end

end ring

end ring_seminorm

/-- The norm of a `non_unital_semi_normed_ring` as a `ring_seminorm`. -/
def norm_ring_seminorm (R : Type*) [non_unital_semi_normed_ring R] :
  ring_seminorm R :=
{ to_fun    := norm,
  mul_le'   := norm_mul_le,
  ..(norm_add_group_seminorm R) }

namespace ring_norm

variable [non_unital_ring R]

instance ring_norm_class : ring_norm_class (ring_norm R) R ℝ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_zero := λ f, f.map_zero',
  map_add_le_add := λ f, f.add_le',
  map_mul_le_mul := λ f, f.mul_le',
  map_neg_eq_map := λ f, f.neg',
  eq_zero_of_map_eq_zero := λ f, f.eq_zero_of_map_eq_zero' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (ring_norm R) (λ _, R → ℝ) := ⟨λ p, p.to_fun⟩

@[simp] lemma to_fun_eq_coe (p : ring_norm R) : p.to_fun = p := rfl

@[ext] lemma ext {p q : ring_norm R} : (∀ x, p x = q x) → p = q := fun_like.ext p q

variable (R)

/-- The trivial norm on a ring `R` is the `ring_norm` taking value `0` at `0` and `1` at every
  other element. -/
instance [decidable_eq R] : has_one (ring_norm R) :=
⟨{ ..(1 : ring_seminorm R), ..(1 : add_group_norm R) }⟩

@[simp] lemma apply_one [decidable_eq R] (x : R) : (1 : ring_norm R) x = if x = 0 then 0 else 1 :=
rfl

instance [decidable_eq R] : inhabited (ring_norm R) := ⟨1⟩

end ring_norm

namespace mul_ring_seminorm
variables [non_assoc_ring R]

instance mul_ring_seminorm_class : mul_ring_seminorm_class (mul_ring_seminorm R) R ℝ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_zero := λ f, f.map_zero',
  map_one := λ f, f.map_one',
  map_add_le_add := λ f, f.add_le',
  map_mul := λ f, f.map_mul',
  map_neg_eq_map := λ f, f.neg' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (mul_ring_seminorm R) (λ _, R → ℝ) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe (p : mul_ring_seminorm R) : p.to_fun = p := rfl

@[ext] lemma ext {p q : mul_ring_seminorm R} : (∀ x, p x = q x) → p = q := fun_like.ext p q

variables [decidable_eq R] [no_zero_divisors R] [nontrivial R]

/-- The trivial seminorm on a ring `R` is the `mul_ring_seminorm` taking value `0` at `0` and `1` at
every other element. -/
instance : has_one (mul_ring_seminorm R) :=
⟨{ map_one' := if_neg one_ne_zero,
  map_mul' := λ x y, begin
    obtain rfl | hx := eq_or_ne x 0,
    { simp },
    obtain rfl | hy := eq_or_ne y 0,
    { simp },
    { simp [hx, hy] }
  end,
  ..(1 : add_group_seminorm R) }⟩

@[simp] lemma apply_one (x : R) : (1 : mul_ring_seminorm R) x = if x = 0 then 0 else 1 := rfl

instance : inhabited (mul_ring_seminorm R) := ⟨1⟩

end mul_ring_seminorm

namespace mul_ring_norm
variable [non_assoc_ring R]

instance mul_ring_norm_class : mul_ring_norm_class (mul_ring_norm R) R ℝ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_zero := λ f, f.map_zero',
  map_one := λ f, f.map_one',
  map_add_le_add := λ f, f.add_le',
  map_mul := λ f, f.map_mul',
  map_neg_eq_map := λ f, f.neg',
  eq_zero_of_map_eq_zero := λ f, f.eq_zero_of_map_eq_zero' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (mul_ring_norm R) (λ _, R → ℝ) := ⟨λ p, p.to_fun⟩

@[simp] lemma to_fun_eq_coe (p : mul_ring_norm R) : p.to_fun = p := rfl

@[ext] lemma ext {p q : mul_ring_norm R} : (∀ x, p x = q x) → p = q := fun_like.ext p q

variables (R) [decidable_eq R] [no_zero_divisors R] [nontrivial R]

/-- The trivial norm on a ring `R` is the `mul_ring_norm` taking value `0` at `0` and `1` at every
other element. -/
instance : has_one (mul_ring_norm R) :=
⟨{ ..(1 : mul_ring_seminorm R), ..(1 : add_group_norm R) }⟩

@[simp] lemma apply_one (x : R) : (1 : mul_ring_norm R) x = if x = 0 then 0 else 1 := rfl

instance : inhabited (mul_ring_norm R) := ⟨1⟩

end mul_ring_norm

/-- A nonzero ring seminorm on a field `K` is a ring norm. -/
def ring_seminorm.to_ring_norm {K : Type*} [field K] (f : ring_seminorm K) (hnt : f ≠ 0) :
  ring_norm K :=
{ eq_zero_of_map_eq_zero' := λ x hx,
  begin
    obtain ⟨c, hc⟩ := ring_seminorm.ne_zero_iff.mp hnt,
    by_contradiction hn0,
    have hc0 : f c = 0,
    { rw [← mul_one c, ← mul_inv_cancel hn0, ← mul_assoc, mul_comm c, mul_assoc],
      exact le_antisymm (le_trans (map_mul_le_mul f _ _)
        (by rw [← ring_seminorm.to_fun_eq_coe, hx, zero_mul])) (map_nonneg f _) },
    exact hc hc0,
  end,
  ..f }

/-- The norm of a normed_ring as a ring_norm. -/
@[simps] def norm_ring_norm (R : Type*) [non_unital_normed_ring R] : ring_norm R :=
{ ..norm_add_group_norm R, ..norm_ring_seminorm R }
