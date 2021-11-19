/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import algebra.algebra.basic
import tactic
/-!
# Spectrum of an element in an algebra
This file develops the basic theory of the spectrum of an element of an algebra.
This theory will serve as the foundation for spectral theory in Banach algebras.

## Main definitions

* `resolvent a`: has type `set R` is the resolvent set of an element `a : A` where
  `A` is an  `R`-algebra.
* `spectrum a`: has type `set R` is the spectrum of an element `a : A` where
  `A` is an  `R`-algebra.

## Main statements

* `unit_left_coset_spectrum`: units in the scalar ring commute (multplication) with the spectrum.
* `left_add_coset_spectrum`: elements of the scalar ring commute (addition) with the spectrum.
* `unit_mem_spectrum_mul_iff_swap_mul`: the units (of `R`) in `σ (a*b)` coincide
  with those in `σ (b*a)`.

## Notations

* `σ a` : `spectrum` of `a : A`

## TODO

* Prove the *spectral mapping theorem* for the polynomial functional calculus
-/

universes u v

variables {R : Type u} {A : Type v}
variables [comm_ring R] [ring A] [algebra R A]


-- definition and basic properties

/-- Given a commutative ring `R` and an `R`-algebra `A`, the *resolvent* of `a : A`
is the `set R` consisting of those `r : R` for which `r•1 - a` is a unit of the
algebra `A`.  -/
definition resolvent (a : A) : set R :=
{ r : R | is_unit (r • 1 - a) }


/-- Given a commutative ring `R` and an `R`-algebra `A`, the *spectrum* of `a : A`
is the `set R` consisting of those `r : R` for which `r•1 - a` is not a unit of the
algebra `A`.

The spectrum is simply the complement of the resolvent.  -/
definition spectrum (a : A) : set R :=
(resolvent a)ᶜ

local notation `σ` := spectrum

lemma mem_spectrum_iff_not_unit {r : R} {a : A} :
  r ∈ (σ a : set R) ↔ ¬ is_unit (r • 1 - a) :=
by { tidy }

lemma not_mem_spectrum_iff_unit {r : R} {a : A} :
  r ∉ (σ a : set R) ↔ is_unit (r • 1 - a) :=
by { apply not_iff_not.mp, simp [set.not_not_mem, mem_spectrum_iff_not_unit] }

lemma mem_resolvent_of_left_right_inverse {r : R} {a b c : A}
  (h₁ : (r • 1 - a) * b = 1) (h₂ : c * (r • 1 - a) = 1) :
  r ∈ (resolvent a : set R) :=
units.is_unit ⟨r•1 - a, b, h₁, by rwa ←left_inv_eq_right_inv h₂ h₁⟩

-- products of scalar units and algebra units

/-- Given a commutative ring `R` and an `R`-algebra `A`, and units `r : units R`
and `a : units A`, then `unit_mul_unit r a` constructs a `units A` with value `r•a`. -/
definition unit_mul_unit (r : units R) (a : units A) :
  units A :=
⟨r•↑a,
 r⁻¹•↑a⁻¹,
 by {simp [smul_mul_smul]},
 by {simp [smul_mul_smul]}⟩

lemma is_unit_smul_smul_sub_smul_iff {r : units R} {s : R} {a : A} :
  is_unit (r • s • 1 - r • a) ↔ is_unit (s • 1 - a) :=
begin
  split,
  { intro h',
    have inv_smul_eq : r⁻¹•(r•s•1 - r•a) = s•1 - a,
      by simp [smul_sub, smul_smul],
    rw ←inv_smul_eq,
    exact (unit_mul_unit r⁻¹ h'.unit).is_unit, },
  { intro h',
    rw ←smul_sub,
    exact (unit_mul_unit r h'.unit).is_unit, },
end

lemma is_unit_smul_smul_sub_iff_is_unit_smul_sub_smul {r : units R} {s : R} {a : A} :
  is_unit (r • s • 1 - a) ↔ is_unit (s • 1 - r⁻¹ • a) :=
by { have h_eq : r•s•1 - r•(r⁻¹•a) = r•s•1 - a, by simp,
     rw [←h_eq,is_unit_smul_smul_sub_smul_iff], }

lemma is_unit_smul_sub_iff_is_unit_sub_smul {r : units R} {a : A} :
  is_unit (r • 1 - a) ↔ is_unit (1 - r⁻¹ • a) :=
begin
  have with_smul_one : is_unit (r•(1 : R)•1 - a) ↔ is_unit ((1 : R)•1 - r⁻¹•a),
    by exact is_unit_smul_smul_sub_iff_is_unit_smul_sub_smul,
  simp at with_smul_one,
  exact with_smul_one,
end

lemma add_mem_spectrum {a : A} {r s : R} :
  r ∈ (σ a : set R) ↔ r + s ∈ (σ (s • 1 + a) : set R) :=
begin
  apply not_iff_not.mpr,
  change is_unit (r•1 - a) ↔ is_unit ((r+s)•1 - (s•1 + a)),
  have h_eq : (r+s)•1 - (s•1 + a) = r•1 - a,
    by { rw add_smul, noncomm_ring },
  simp [h_eq],
end

lemma mul_mem_spectrum_mul {a : A} {s : R} {r : units R} :
  r • s ∈ (σ (r • a) : set R) ↔ s ∈ (σ a : set R) :=
begin
  apply not_iff_not.mpr,
  change is_unit ((r•s)•1 - r•a) ↔ is_unit (s•1 - a),
  have h_eq : (r•s)•(1 : A) = r•s•1, by simp,
  rw h_eq,
  exact is_unit_smul_smul_sub_smul_iff,
end

theorem left_add_coset_spectrum (a : A) (r : R) :
  left_add_coset r (σ a) = (σ (r • 1 + a)) :=
by { ext, rw [mem_left_add_coset_iff, neg_add_eq_sub, add_mem_spectrum],
     nth_rewrite 1 ←sub_add_cancel x r, }

-- this one isn't quite as simple because `R` is not a `group` (but it is an `add_group`)
-- therefore we don't have access to `mem_left_add_coset_iff`
theorem unit_left_coset_spectrum (a : A) (r : units R) :
  left_coset ↑r (σ a : set R) = σ (r • a) :=
begin
  ext,
  split,
  { rintro ⟨y,y_mem,hy⟩,
    rw ←hy,
    exact mul_mem_spectrum_mul.mpr y_mem, },
  { intro hx,
    have self_inv : x = r•r⁻¹•x, by simp,
    rw self_inv at *,
    exact mem_left_coset ↑r (mul_mem_spectrum_mul.mp hx), },
end

-- general (noncommutative) ring results about units and the identity
lemma right_inv_of_right_inv_swap {a b c : A} (h : (1 - a * b) * c = 1) :
  (1 - b * a) * (1 + b * c * a) = 1 :=
calc (1 - b*a)*(1 + b*c*a) = 1 - b*a + b*((1 - a*b)*c)*a : by noncomm_ring
...                        = 1                           : by simp [h]

lemma left_inv_of_left_inv_swap {a b c : A} (h : c * (1 - a * b) = 1) :
  (1 + b * c * a) * (1 - b * a) = 1 :=
calc (1 + b*c*a)*(1 - b*a) = 1 - b*a + b*(c*(1 - a*b))*a : by noncomm_ring
...                        = 1                           : by simp [h]

lemma is_unit_one_sub_mul_of_swap {a b : A} (h : is_unit (1 - a * b)) :
  is_unit (1 - b * a) :=
by { let h₁ := right_inv_of_right_inv_swap h.unit.val_inv,
     let h₂ := left_inv_of_left_inv_swap h.unit.inv_val,
     exact ⟨⟨1-b*a,1+b*h.unit.inv*a,h₁,h₂⟩,rfl⟩, }

lemma is_unit_one_sub_mul_iff_swap {a b : A} :
  is_unit (1 - a * b) ↔ is_unit (1 - b * a) :=
by { split, repeat {apply is_unit_one_sub_mul_of_swap}, }

-- `r ∈ σ(a*b) ↔ r ∈ σ(b*a)` for any `r : units R`
theorem unit_mem_spectrum_mul_iff_swap_mul {a b : A} {r : units R} :
  ↑r ∈ (σ (a * b) : set R) ↔ ↑r ∈ (σ (b * a) : set R) :=
begin
  apply not_iff_not.mpr,
  change is_unit (r•1 - a*b) ↔ is_unit (r•1 - b*a),
  repeat {rw [is_unit_smul_sub_iff_is_unit_sub_smul]},
  rw [←smul_mul_assoc, ←mul_smul_comm r⁻¹ b a, is_unit_one_sub_mul_iff_swap],
end
