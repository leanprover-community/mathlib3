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
  have key : (X - C r) * (f /ₘ (X - C r)) = f - (f %ₘ (X - C r)),
  { rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', mod_by_monic_eq_sub_mul_div],
    exact monic_X_sub_C r },
  apply_fun derivative at key,
  simp only [derivative_X, derivative_mul, one_mul, sub_zero, derivative_sub,
    mod_by_monic_X_sub_C_eq_C_eval, derivative_C] at key,
  refine or.resolve_left (dvd_or_coprime (X - C r) (f /ₘ (X - C r))
    (irreducible_of_degree_eq_one (polynomial.degree_X_sub_C r))) _,
  intro,
  apply hf',
  have : (X - C r) ∣ derivative f := key ▸ (dvd_add a (dvd.intro (derivative (f /ₘ (X - C r))) rfl)),
  rw [← dvd_iff_mod_by_monic_eq_zero (monic_X_sub_C _), mod_by_monic_X_sub_C_eq_C_eval] at this,
  apply_fun coeff at this,
  convert congr_fun this 0,
  rw [coeff_C_zero],
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
