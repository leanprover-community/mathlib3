/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.ideal_operations
import ring_theory.polynomial
import ring_theory.principal_ideal_domain
import tactic

/-!
# Henselian local rings


## References

https://stacks.math.columbia.edu/tag/04GE
-/

universe variables u v

open local_ring (residue_field residue)
open polynomial (X C)
open function

class henselian_local_ring (R : Type u) extends local_ring R :=
(lift_root : ∀ (f : polynomial R) (hf : f.monic)
               (a₀ : residue_field R) (h₁ : (f.map (residue R)).is_root a₀)
               (h₂ : (f.derivative.map (residue R)).eval a₀ ≠ 0),
               ∃ a : R,  f.is_root a ∧ (residue R a = a₀))
.

-- move this
namespace polynomial

/-- The formal derivative of polynomials, as additive homomorphism. -/
noncomputable def derivative_hom (R : Type*) [comm_semiring R] : polynomial R →+ polynomial R :=
{ to_fun := derivative,
  map_zero' := derivative_zero,
  map_add' := λ p q, derivative_add }

@[simp] lemma derivative_neg {R : Type*} [comm_ring R] (f : polynomial R) :
  derivative (-f) = -derivative f :=
(derivative_hom R).map_neg f

@[simp] lemma derivative_sub {R : Type*} [comm_ring R] (f g : polynomial R) :
  derivative (f - g) = derivative f - derivative g :=
(derivative_hom R).map_sub f g

lemma is_coprime_of_is_root_of_eval_derivative_ne_zero {R : Type*} [field R]
  (f : polynomial R) (r : R) (hf : f.is_root r) (hf' : f.derivative.eval r ≠ 0) :
  ideal.is_coprime (X - C r : polynomial R) (f /ₘ (X - C r)) :=
begin
  rw ← mul_div_by_monic_eq_iff_is_root at hf,
  rw ← hf at hf',
  simp only [eval_C, eval_X, add_zero, derivative_X, derivative_mul, one_mul, zero_mul,
    eval_sub, sub_zero, ne.def, derivative_sub, eval_add, eval_mul, derivative_C, sub_self] at hf',
  apply is_coprime_of_dvd,
  { push_neg, left, assume eqz,
    apply_fun polynomial.degree at eqz,
    rw polynomial.degree_X_sub_C at eqz,
    exact option.no_confusion eqz },
  { rintros a h1 h2 ⟨b, hab⟩ H,
    have : irreducible (X - C r),
    { apply polynomial.irreducible_of_degree_eq_one, exact polynomial.degree_X_sub_C _ },
    rcases (this.is_unit_or_is_unit hab) with ha|⟨b,rfl⟩,
    { exact h1 ha },
    apply hf',
    show is_root _ _,
    rw ← dvd_iff_is_root,
    refine dvd_trans ⟨↑b⁻¹, _⟩ H,
    rw [hab, units.mul_inv_cancel_right] }
end

end polynomial

lemma henselian.tfae (R : Type u) [local_ring R] :
  tfae [
    (∀ (f : polynomial R) (hf : f.monic) (a₀ : residue_field R) (h₁ : (f.map (residue R)).is_root a₀)
      (h₂ : (f.map (residue R)).derivative.eval a₀ ≠ 0),
      ∃ a : R, f.is_root a ∧ (residue R a = a₀)),
    (∀ (f : polynomial R) (a₀ : residue_field R) (h₁ : (f.map (residue R)).is_root a₀)
      (h₂ : (f.map (residue R)).derivative.eval a₀ ≠ 0),
      ∃ a : R, f.is_root a ∧ (residue R a = a₀)),
    (∀ (κ : Type u) [field κ], by exactI ∀ (φ : R →+* κ) (hφ : surjective φ) (f : polynomial R)
      (a₀ : κ) (h₁ : (f.map φ).is_root a₀) (h₂ : (f.map φ).derivative.eval a₀ ≠ 0),
      ∃ a : R, f.is_root a ∧ (φ a = a₀)),
    (∀ (κ : Type u) [field κ], by exactI ∀ (φ : R →+* κ) (hφ : surjective φ) (f : polynomial R)
      (g₀ h₀ : polynomial κ) (hc : ideal.is_coprime g₀ h₀) (H : (f.map φ) = g₀ * h₀),
      ∃ (g h : polynomial R), (f = g * h) ∧ (g.map φ = h₀) ∧ (h.map φ = h₀) ∧ (g.degree = g₀.degree))
  ] :=
begin
  tfae_have : 2 → 1, { intros, solve_by_elim },
  tfae_have : 3 → 2,
  { intros H,
    apply H (residue_field R) (residue R),
    rintro ⟨a⟩, exact ⟨a, rfl⟩, },
  tfae_have : 4 → 3,
  { introsI H κ _inst φ hφ f a₀ h₁ h₂,
    have := polynomial.mul_div_by_monic_eq_iff_is_root.mpr h₁,
    specialize H κ φ hφ f (X - C a₀) ((f.map φ) /ₘ (X - C a₀))
      (polynomial.is_coprime_of_is_root_of_eval_derivative_ne_zero _ _ h₁ h₂) this.symm,
    rcases H with ⟨g, h, rfl, hg, hh, H⟩,
    rw polynomial.degree_X_sub_C at H,
    have : is_unit g.leading_coeff,
    have := polynomial.leading_coeff_map,
    -- by_contradiction oops,
    -- have := polynomial.eq_X_add_C_of_degree_eq_one H,
     },
  tfae_have : 1 → 4,
  { sorry },
  tfae_finish
end

#print is_local_ring

#print local_ring
