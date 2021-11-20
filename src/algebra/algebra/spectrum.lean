/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import algebra.algebra.basic
import tactic.noncomm_ring
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

* `σ a` : `spectrum R a` of `a : A`

## TODO

* Prove the *spectral mapping theorem* for the polynomial functional calculus
-/

universes u v

section defs

variables (R : Type u) {A : Type v}
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
(resolvent R a)ᶜ

end defs

variables {R : Type u} {A : Type v}
variables [comm_ring R] [ring A] [algebra R A]

local notation `σ` := spectrum R

lemma mem_spectrum_iff_not_unit {r : R} {a : A} :
  r ∈ σ a ↔ ¬ is_unit (r • 1 - a) :=
by { tidy }

lemma not_mem_spectrum_iff_unit {r : R} {a : A} :
  r ∉ σ a ↔ is_unit (r • 1 - a) :=
by { apply not_iff_not.mp, simp [set.not_not_mem, mem_spectrum_iff_not_unit] }

lemma mem_resolvent_of_left_right_inverse {r : R} {a b c : A}
  (h₁ : (r • 1 - a) * b = 1) (h₂ : c * (r • 1 - a) = 1) :
  r ∈ resolvent R a :=
units.is_unit ⟨r•1 - a, b, h₁, by rwa ←left_inv_eq_right_inv h₂ h₁⟩

-- products of scalar units and algebra units

/-- Given a commutative ring `R` and an `R`-algebra `A`, and units `r : units R`
and `a : units A`, then `unit_mul_unit r a` constructs a `units A` with value `r•a`. -/

lemma is_unit.smul_smul_sub_smul_iff {r : units R} {s : R} {a : A} :
  is_unit (r • s • 1 - r • a) ↔ is_unit (s • 1 - a) :=
begin
  split,
  { intro h',
    have inv_smul_eq : r⁻¹•(r•s•1 - r•a) = s•1 - a,
      by simp [smul_sub, smul_smul],
    rw ←inv_smul_eq,
    exact (r⁻¹ • h'.unit).is_unit, },
  { intro h',
    rw ←smul_sub,
    exact (r • h'.unit).is_unit, },
end

lemma is_unit.smul_smul_sub_iff_is_unit_smul_sub_smul {r : units R} {s : R} {a : A} :
  is_unit (r • s • 1 - a) ↔ is_unit (s • 1 - r⁻¹ • a) :=
by { have h_eq : r•s•1 - r•(r⁻¹•a) = r•s•1 - a, by simp,
     rw [←h_eq,is_unit.smul_smul_sub_smul_iff], }

lemma is_unit.smul_sub_iff_is_unit_sub_smul {r : units R} {a : A} :
  is_unit (r • 1 - a) ↔ is_unit (1 - r⁻¹ • a) :=
begin
  have with_smul_one : is_unit (r•(1 : R)•1 - a) ↔ is_unit ((1 : R)•1 - r⁻¹•a),
    by exact is_unit.smul_smul_sub_iff_is_unit_smul_sub_smul,
  simpa using with_smul_one,
end

lemma add_mem_spectrum {a : A} {r s : R} :
  r ∈ σ a ↔ r + s ∈ σ (s • 1 + a) :=
begin
  apply not_iff_not.mpr,
  change is_unit (r•1 - a) ↔ is_unit ((r+s)•1 - (s•1 + a)),
  have h_eq : (r+s)•1 - (s•1 + a) = r•1 - a,
    by { rw add_smul, noncomm_ring },
  simp [h_eq],
end

lemma mul_mem_spectrum_mul {a : A} {s : R} {r : units R} :
  r • s ∈ σ (r • a) ↔ s ∈ σ a :=
begin
  apply not_iff_not.mpr,
  change is_unit ((r•s)•1 - r•a) ↔ is_unit (s•1 - a),
  have h_eq : (r•s)•(1 : A) = r•s•1, by simp,
  rw h_eq,
  exact is_unit.smul_smul_sub_smul_iff,
end

theorem left_add_coset_spectrum (a : A) (r : R) :
  left_add_coset r (σ a) = σ (r • 1 + a) :=
by { ext, rw [mem_left_add_coset_iff, neg_add_eq_sub, add_mem_spectrum],
     nth_rewrite 1 ←sub_add_cancel x r, }

-- this one isn't quite as simple because `R` is not a `group` (but it is an `add_group`)
-- therefore we don't have access to `mem_left_add_coset_iff`
theorem unit_left_coset_spectrum (a : A) (r : units R) :
  left_coset ↑r (σ a) = σ (r • a) :=
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

-- `r ∈ σ(a*b) ↔ r ∈ σ(b*a)` for any `r : units R`
theorem unit_mem_spectrum_mul_iff_swap_mul {a b : A} {r : units R} :
  ↑r ∈ σ (a * b) ↔ ↑r ∈ σ (b * a) :=
begin
  apply not_iff_not.mpr,
  change is_unit (r•1 - a*b) ↔ is_unit (r•1 - b*a),
  simp only [is_unit.smul_sub_iff_is_unit_sub_smul],
  have right_inv_of_swap : ∀ {x y z : A} (h : (1 - x*y)*z = 1),
    (1 - y*x)*(1 + y*z*x) = 1, from λ x y z h,
      calc (1 - y*x)*(1 + y*z*x) = 1 - y*x + y*((1 - x*y)*z)*x : by noncomm_ring
      ...                        = 1                           : by simp [h],
  have left_inv_of_swap : ∀ {x y z : A} (h : z*(1 - x*y) = 1),
    (1 + y*z*x)*(1 - y*x) = 1, from λ x y z h,
      calc (1 + y*z*x)*(1 - y*x) = 1 - y*x + y*(z*(1 - x*y))*x : by noncomm_ring
      ...                        = 1                           : by simp [h],
  have is_unit_one_sub_mul_of_swap : ∀ {x y : A} (h : is_unit (1 - x*y)),
    is_unit (1 - y*x), from λ x y h, by
      { let h₁ := right_inv_of_swap h.unit.val_inv,
        let h₂ := left_inv_of_swap h.unit.inv_val,
        exact ⟨⟨1-y*x,1+y*h.unit.inv*x,h₁,h₂⟩,rfl⟩, },
  have is_unit_one_sub_mul_iff_swap : ∀ {x y : A},
    is_unit (1 - x*y) ↔ is_unit (1 - y*x), by
      { intros, split, repeat {apply is_unit_one_sub_mul_of_swap}, },
  rw [←smul_mul_assoc, ←mul_smul_comm r⁻¹ b a, is_unit_one_sub_mul_iff_swap],
end
