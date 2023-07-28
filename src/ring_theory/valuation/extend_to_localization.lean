/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import ring_theory.localization.at_prime
import ring_theory.valuation.basic

/-!

# Extending valuations to a localization

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show that, given a valuation `v` taking values in a linearly ordered commutative *group*
with zero `Γ`, and a submonoid `S` of `v.supp.prime_compl`, the valuation `v` can be naturally
extended to the localization `S⁻¹A`.

-/

variables
  {A : Type*} [comm_ring A]
  {Γ : Type*} [linear_ordered_comm_group_with_zero Γ] (v : valuation A Γ)
  {S : submonoid A} (hS : S ≤ v.supp.prime_compl)
  (B : Type*) [comm_ring B] [algebra A B] [is_localization S B]

/-- We can extend a valuation `v` on a ring to a localization at a submonoid of
the complement of `v.supp`. -/
noncomputable
def valuation.extend_to_localization : valuation B Γ :=
let f := is_localization.to_localization_map S B,
    h : ∀ s : S, is_unit (v.1.to_monoid_hom s) := λ s, is_unit_iff_ne_zero.2 (hS s.2) in
{ map_zero' := by convert f.lift_eq _ 0; simp,
  map_add_le_max' := λ x y, begin
    obtain ⟨a,b,s,rfl,rfl⟩ : ∃ (a b : A) (s : S), f.mk' a s = x ∧ f.mk' b s = y,
    { obtain ⟨a,s,rfl⟩ := f.mk'_surjective x,
      obtain ⟨b,t,rfl⟩ := f.mk'_surjective y,
      use [a * t, b * s, s * t], split;
      { rw [f.mk'_eq_iff_eq, submonoid.coe_mul], ring_nf } },
    convert_to f.lift h (f.mk' (a+b) s) ≤ max (f.lift h _) (f.lift h _),
    { refine congr_arg (f.lift h) (is_localization.eq_mk'_iff_mul_eq.2 _),
      rw [add_mul, map_add], iterate 2 { erw is_localization.mk'_spec } },
    iterate 3 { rw f.lift_mk' }, rw max_mul_mul_right,
    apply mul_le_mul_right' (v.map_add a b),
  end,
..f.lift h }

@[simp]
lemma valuation.extend_to_localization_apply_map_apply (a : A) :
  v.extend_to_localization hS B (algebra_map A B a) = v a :=
submonoid.localization_map.lift_eq _ _ a
