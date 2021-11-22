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
def resolvent (a : A) : set R :=
{ r : R | is_unit (r • 1 - a) }


/-- Given a commutative ring `R` and an `R`-algebra `A`, the *spectrum* of `a : A`
is the `set R` consisting of those `r : R` for which `r•1 - a` is not a unit of the
algebra `A`.

The spectrum is simply the complement of the resolvent.  -/
def spectrum (a : A) : set R :=
(resolvent R a)ᶜ

end defs

variables {R : Type u} {A : Type v}
variables [comm_ring R] [ring A] [algebra R A]

-- products of scalar units and algebra units

lemma is_unit.smul_iff {G : Type u} [group G] [mul_action G A]
  [smul_comm_class G A A] [is_scalar_tower G A A] {r : G} {a : A} :
  is_unit (r • a) ↔ is_unit a :=
begin
  split, swap,
    { exact λ h, (r•h.unit).is_unit, },
    { intro h, let a' : units A :=
        ⟨a,
         r•↑(h.unit)⁻¹,
         by rw [mul_smul_comm, ←smul_mul_assoc, is_unit.mul_coe_inv],
         by rw [smul_mul_assoc,←mul_smul_comm, is_unit.coe_inv_mul],⟩,
      exact ⟨a',rfl⟩, },
end

lemma is_unit.smul_sub_iff_sub_inv_smul {r : units R} {a : A} :
  is_unit (r • 1 - a) ↔ is_unit (1 - r⁻¹ • a) :=
begin
  have a_eq : a = r•r⁻¹•a, by simp,
  nth_rewrite 0 a_eq,
  rw [←smul_sub,is_unit.smul_iff],
end

namespace spectrum


local notation `σ` := spectrum R

lemma mem_iff {r : R} {a : A} :
  r ∈ σ a ↔ ¬ is_unit (r • 1 - a) :=
iff.rfl

lemma not_mem_iff {r : R} {a : A} :
  r ∉ σ a ↔ is_unit (r • 1 - a) :=
by { apply not_iff_not.mp, simp [set.not_not_mem, mem_iff] }

lemma mem_resolvent_of_left_right_inverse {r : R} {a b c : A}
  (h₁ : (r • 1 - a) * b = 1) (h₂ : c * (r • 1 - a) = 1) :
  r ∈ resolvent R a :=
units.is_unit ⟨r•1 - a, b, h₁, by rwa ←left_inv_eq_right_inv h₂ h₁⟩

lemma mem_resolvent_iff {r : R} {a : A} :
  r ∈ resolvent R a ↔ is_unit (r•1 - a) :=
iff.rfl

lemma add_mem_iff {a : A} {r s : R} :
  r ∈ σ a ↔ r + s ∈ σ (s • 1 + a) :=
begin
  apply not_iff_not.mpr,
  simp only [mem_resolvent_iff],
  have h_eq : (r+s)•1 - (s•1 + a) = r•1 - a,
    { rw add_smul, noncomm_ring },
  simp [h_eq],
end

lemma smul_mem_smul_iff {a : A} {s : R} {r : units R} :
  r • s ∈ σ (r • a) ↔ s ∈ σ a :=
begin
  apply not_iff_not.mpr,
  simp only [mem_resolvent_iff],
  have h_eq : (r•s)•(1 : A) = r•s•1, by simp,
  rw [h_eq,←smul_sub,is_unit.smul_iff],
end

open_locale pointwise

theorem smul_eq_smul (a : A) (r : units R) :
  σ (r • a) = r • σ a :=
begin
  ext,
  have x_eq : x = r•r⁻¹•x, by simp,
  nth_rewrite 0 x_eq,
  rw smul_mem_smul_iff,
  split,
    { exact λ h, ⟨r⁻¹•x,⟨h,by simp⟩⟩},
    { rintros ⟨_,_,x'_eq⟩, simpa [←x'_eq],}
end

theorem left_add_coset_eq (a : A) (r : R) :
  left_add_coset r (σ a) = σ (r • 1 + a) :=
by { ext, rw [mem_left_add_coset_iff, neg_add_eq_sub, add_mem_iff],
     nth_rewrite 1 ←sub_add_cancel x r, }

-- `r ∈ σ(a*b) ↔ r ∈ σ(b*a)` for any `r : units R`
theorem unit_mem_mul_iff_mem_swap_mul {a b : A} {r : units R} :
  ↑r ∈ σ (a * b) ↔ ↑r ∈ σ (b * a) :=
begin
  apply not_iff_not.mpr,
  simp only [mem_resolvent_iff],
  have coe_smul_eq : ↑r•1 = r•(1 : A), from rfl,
  rw coe_smul_eq,
  simp only [is_unit.smul_sub_iff_sub_inv_smul],
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

theorem preimage_units_mul_eq_swap_mul {a b : A} :
  (coe : units R → R) ⁻¹' σ (a * b) = coe ⁻¹'  σ (b * a) :=
by { ext, exact unit_mem_mul_iff_mem_swap_mul, }

end spectrum
