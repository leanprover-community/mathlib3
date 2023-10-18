/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.units
import algebra.algebra.spectrum
import topology.continuous_function.algebra

/-!
# Units of continuous functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file concerns itself with `C(X, M)ˣ` and `C(X, Mˣ)` when `X` is a topological space
and `M` has some monoid structure compatible with its topology.
-/

variables {X M R 𝕜 : Type*} [topological_space X]

namespace continuous_map

section monoid

variables [monoid M] [topological_space M] [has_continuous_mul M]

/-- Equivalence between continuous maps into the units of a monoid with continuous multiplication
and the units of the monoid of continuous maps. -/
@[to_additive "Equivalence between continuous maps into the additive units of an additive monoid
with continuous addition and the additive units of the additive monoid of continuous maps.", simps]
def units_lift : C(X, Mˣ) ≃ C(X, M)ˣ :=
{ to_fun := λ f,
  { val := ⟨λ x, f x, units.continuous_coe.comp f.continuous⟩,
    inv := ⟨λ x, ↑(f x)⁻¹, units.continuous_coe.comp (continuous_inv.comp f.continuous)⟩,
    val_inv := ext $ λ x, units.mul_inv _,
    inv_val := ext $ λ x, units.inv_mul _ },
  inv_fun := λ f,
  { to_fun := λ x, ⟨f x, f⁻¹ x, continuous_map.congr_fun f.mul_inv x,
                                continuous_map.congr_fun f.inv_mul x⟩,
    continuous_to_fun := continuous_induced_rng.2 $ continuous.prod_mk (f : C(X, M)).continuous
      $ mul_opposite.continuous_op.comp (↑f⁻¹ : C(X, M)).continuous },
  left_inv := λ f, by { ext, refl },
  right_inv := λ f, by { ext, refl } }

end monoid

section normed_ring

variables [normed_ring R] [complete_space R]

lemma _root_.normed_ring.is_unit_unit_continuous {f : C(X, R)} (h : ∀ x, is_unit (f x)) :
  continuous (λ x, (h x).unit) :=
begin
  refine continuous_induced_rng.2 (continuous.prod_mk f.continuous
    (mul_opposite.continuous_op.comp (continuous_iff_continuous_at.mpr (λ x, _)))),
  have := normed_ring.inverse_continuous_at (h x).unit,
  simp only [←ring.inverse_unit, is_unit.unit_spec, ←function.comp_apply] at this ⊢,
  exact this.comp (f.continuous_at x),
end

/-- Construct a continuous map into the group of units of a normed ring from a function into the
normed ring and a proof that every element of the range is a unit. -/
@[simps]
noncomputable def units_of_forall_is_unit {f : C(X, R)} (h : ∀ x, is_unit (f x)) : C(X, Rˣ) :=
{ to_fun := λ x, (h x).unit,
  continuous_to_fun :=  normed_ring.is_unit_unit_continuous h }

instance can_lift : can_lift C(X, R) C(X, Rˣ)
  (λ f, ⟨λ x, f x, units.continuous_coe.comp f.continuous⟩) (λ f, ∀ x, is_unit (f x)) :=
{ prf := λ f h, ⟨units_of_forall_is_unit h, by { ext, refl }⟩ }

lemma is_unit_iff_forall_is_unit (f : C(X, R)) :
  is_unit f ↔ ∀ x, is_unit (f x) :=
iff.intro (λ h, λ x, ⟨units_lift.symm h.unit x, rfl⟩)
  (λ h, ⟨(units_of_forall_is_unit h).units_lift, by { ext, refl }⟩)

end normed_ring

section normed_field

variables [normed_field 𝕜] [complete_space 𝕜]

lemma is_unit_iff_forall_ne_zero (f : C(X, 𝕜)) :
  is_unit f ↔ ∀ x, f x ≠ 0 :=
by simp_rw [f.is_unit_iff_forall_is_unit, is_unit_iff_ne_zero]

lemma spectrum_eq_range (f : C(X, 𝕜)) :
  spectrum 𝕜 f = set.range f :=
begin
  ext,
  simp only [spectrum.mem_iff, is_unit_iff_forall_ne_zero, not_forall, coe_sub,
    pi.sub_apply, algebra_map_apply, algebra.id.smul_eq_mul, mul_one, not_not, set.mem_range,
    sub_eq_zero, @eq_comm _ x _]
end

end normed_field

end continuous_map
