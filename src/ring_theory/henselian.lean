/-
Copyright (c) 2020 Ashwin Iyengar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashwin Iyengar
-/

import ring_theory.ideals
import ring_theory.polynomial

universe u

namespace nonzero_comm_ring

variables (R : Type u)
variables [nonzero_comm_ring R]

lemma bot_maps_to_zero : ∀ (a : R), a ∈ (⊥ : ideal R) → ring_hom.id R a = 0 := by simp

/-def quo_by_zero_ideal_bij : R ≃+* (⊥: ideal R).quotient := linear_algebra-/
/-{ inv_fun   := ideal.quotient.lift ⊥ (ring_hom.id R) (bot_maps_to_zero R),
  left_inv  :=
    begin
      intro x,
      unfold ideal.quotient.mk_hom,
      simp,
    end,
  right_inv :=
    begin
      intro x,
      unfold ideal.quotient.mk_hom,
      unfold ring_hom.id,
      cases quot.exists_rep x,
      rw ←h,
      simp,
      unfold ideal.quotient.mk,
      rw submodule.quotient.eq,
      unfold ideal.quotient.lift,
      simp,
      unfold quotient.lift_on',

    end,
  ..ideal.quotient.mk_hom (⊥ : ideal R) }-/

end nonzero_comm_ring

open polynomial
open local_ring

namespace field

variables (R : Type u) [field R]

theorem no_nonzero_units : local_ring.nonunits_ideal R = ⊥ :=
or.resolve_right (ideal.eq_bot_or_top (nonunits_ideal R))
begin
  rw ideal.eq_top_iff_one,
  have c : is_unit (1 : R) := is_unit_one,
  contradiction,
end

theorem residue_map_is_bijection : function.bijective (residue R) :=
begin
  split,
  { intros x y h,
    rw [←sub_eq_zero, ←ring_hom.map_sub, ideal.quotient.eq_zero_iff_mem] at h,

    }
end

end field

-- class henselian_pair (R : Type u) extends nonzero_comm_ring R := (hensel_ideal : ideal R) (is_henselian : ∀ f : polynomial R, ∀ g₀ h₀ : polynomial (ideal.quotient hensel_ideal), monic f ∧ monic g₀ ∧ monic h₀ ∧ map (ideal.quotient.mk_hom hensel_ideal) f = g₀ * h₀ ∧ is_unit g₀ ∧ is_unit h₀ → ∃ g h : polynomial R, f = g * h ∧ map (ideal.quotient.mk_hom hensel_ideal) g = g₀ ∧ map (ideal.quotient.mk_hom hensel_ideal) h = h₀)

variables (R : Type u)

class henselian extends local_ring R :=
(is_henselian : ∀ p : polynomial R, ∀ a₀ : residue_field R,
  monic p ∧
  is_root (map (residue R) p) a₀ ∧
  ¬is_root(derivative (map (residue R) p)) a₀
    → ∃ a : R, is_root p a ∧ residue R a = a₀)

lemma henselian_of_field [field R] : henselian R :=
{ is_henselian :=
    begin
      intros p a₀ hyp,
      obtain ⟨m,root,deriv_not_root⟩ := hyp,

    end}
