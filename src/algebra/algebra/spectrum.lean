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

* `resolvent_set a : set R`: the resolvent set of an element `a : A` where
  `A` is an  `R`-algebra.
* `spectrum a : set R`: the spectrum of an element `a : A` where
  `A` is an  `R`-algebra.
* `resolvent : R → A`: the resolvent function is `λ r, ring.inverse (↑ₐr - a)`, and hence
  when `r ∈ resolvent R A`, it is actually the inverse of the unit `(↑ₐr - a)`.

## Main statements

* `smul_eq_smul`: units in the scalar ring commute (multiplication) with the spectrum.
* `left_add_coset_eq`: elements of the scalar ring commute (addition) with the spectrum.
* `units_mem_mul_iff_mem_swap_mul` and `preimage_units_mul_eq_swap_mul`: the units
  (of `R`) in `σ (a*b)` coincide with those in `σ (b*a)`.

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

/-- Given a commutative ring `R` and an `R`-algebra `A`, the *resolvent set* of `a : A`
is the `set R` consisting of those `r : R` for which `r•1 - a` is a unit of the
algebra `A`.  -/
def resolvent_set (a : A) : set R :=
{ r : R | is_unit (algebra_map R A r - a) }


/-- Given a commutative ring `R` and an `R`-algebra `A`, the *spectrum* of `a : A`
is the `set R` consisting of those `r : R` for which `r•1 - a` is not a unit of the
algebra `A`.

The spectrum is simply the complement of the resolvent set.  -/
def spectrum (a : A) : set R :=
(resolvent_set R a)ᶜ

variable {R}
/-- Given an `a : A` where `A` is an `R`-algebra, the *resolvent* is
    a map `R → A` which sends `r : R` to `(algebra_map R A r - a)⁻¹` when
    `r ∈ resolvent R A` and `0` when `r ∈ spectrum R A`. -/
noncomputable def resolvent (a : A) (r : R) : A :=
ring.inverse (algebra_map R A r - a)

end defs

variables {R : Type u} {A : Type v}
variables [comm_ring R] [ring A] [algebra R A]

-- products of scalar units and algebra units


lemma is_unit.smul_sub_iff_sub_inv_smul {r : units R} {a : A} :
  is_unit (r • 1 - a) ↔ is_unit (1 - r⁻¹ • a) :=
begin
  have a_eq : a = r•r⁻¹•a, by simp,
  nth_rewrite 0 a_eq,
  rw [←smul_sub,is_unit_smul_iff],
end

namespace spectrum


local notation `σ` := spectrum R
local notation `↑ₐ` := algebra_map R A

lemma mem_iff {r : R} {a : A} :
  r ∈ σ a ↔ ¬ is_unit (↑ₐr - a) :=
iff.rfl

lemma not_mem_iff {r : R} {a : A} :
  r ∉ σ a ↔ is_unit (↑ₐr - a) :=
by { apply not_iff_not.mp, simp [set.not_not_mem, mem_iff] }

lemma mem_resolvent_set_of_left_right_inverse {r : R} {a b c : A}
  (h₁ : (↑ₐr - a) * b = 1) (h₂ : c * (↑ₐr - a) = 1) :
  r ∈ resolvent_set R a :=
units.is_unit ⟨↑ₐr - a, b, h₁, by rwa ←left_inv_eq_right_inv h₂ h₁⟩

lemma mem_resolvent_set_iff {r : R} {a : A} :
  r ∈ resolvent_set R a ↔ is_unit (↑ₐr - a) :=
iff.rfl

lemma resolvent_eq {a : A} {r : R} (h : r ∈ resolvent_set R a) :
  resolvent a r = ↑h.unit⁻¹ :=
ring.inverse_unit h.unit

lemma add_mem_iff {a : A} {r s : R} :
  r ∈ σ a ↔ r + s ∈ σ (↑ₐs + a) :=
begin
  apply not_iff_not.mpr,
  simp only [mem_resolvent_set_iff],
  have h_eq : ↑ₐ(r+s) - (↑ₐs + a) = ↑ₐr - a,
    { simp, noncomm_ring },
  rw h_eq,
end

lemma smul_mem_smul_iff {a : A} {s : R} {r : units R} :
  r • s ∈ σ (r • a) ↔ s ∈ σ a :=
begin
  apply not_iff_not.mpr,
  simp only [mem_resolvent_set_iff, algebra.algebra_map_eq_smul_one],
  have h_eq : (r•s)•(1 : A) = r•s•1, by simp,
  rw [h_eq,←smul_sub,is_unit_smul_iff],
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
  left_add_coset r (σ a) = σ (↑ₐr + a) :=
by { ext, rw [mem_left_add_coset_iff, neg_add_eq_sub, add_mem_iff],
     nth_rewrite 1 ←sub_add_cancel x r, }

-- `r ∈ σ(a*b) ↔ r ∈ σ(b*a)` for any `r : units R`
theorem unit_mem_mul_iff_mem_swap_mul {a b : A} {r : units R} :
  ↑r ∈ σ (a * b) ↔ ↑r ∈ σ (b * a) :=
begin
  apply not_iff_not.mpr,
  simp only [mem_resolvent_set_iff, algebra.algebra_map_eq_smul_one],
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
