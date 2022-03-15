/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import topology.continuous_function.compact
import analysis.normed_space.units
import algebra.algebra.spectrum

/-!
# Units of continuous functions

This file concerns itself with `C(α, β)ˣ` and `C(α, βˣ)` when `α` is a topological space
and `β` has an appropriate algebraic and topological structure.
-/

variables {α β : Type*} [topological_space α]

namespace continuous_map

section monoid

variables [monoid β] [topological_space β] [has_continuous_mul β]

/-- Equivalence between continuous maps into the units of a monoid with continuous multiplication
and the units of the monoid of continuous maps. -/
@[to_additive, simps]
def units_lift : C(α, βˣ) ≃ C(α, β)ˣ :=
{ to_fun := λ f,
  { val := ⟨λ x, f x, units.continuous_coe.comp f.continuous⟩,
    inv := ⟨λ x, ↑(f x)⁻¹, units.continuous_coe.comp (continuous_inv.comp f.continuous)⟩,
    val_inv := ext $ λ x, units.mul_inv _,
    inv_val := ext $ λ x, units.inv_mul _ },
  inv_fun := λ f,
  { to_fun := λ x, ⟨f x, f⁻¹ x, continuous_map.congr_fun f.mul_inv x,
                                continuous_map.congr_fun f.inv_mul x⟩,
    continuous_to_fun := continuous_induced_rng $ continuous.prod_mk (f : C(α, β)).continuous
      $ mul_opposite.continuous_op.comp (↑f⁻¹ : C(α, β)).continuous },
  left_inv := λ f, by { ext, refl },
  right_inv := λ f, by { ext, refl } }

end monoid

section normed_ring

variables [normed_ring β] [complete_space β]

/-- Construct a continuous map into the group of units of a normed ring from a function into the
normed ring and a proof that every element of the range is a unit. -/
@[simps]
noncomputable def units_of_forall_is_unit {f : C(α, β)} (h : ∀ x, is_unit (f x)) : C(α, βˣ) :=
{ to_fun := λ x, (h x).unit,
  continuous_to_fun :=
  begin
    refine continuous_induced_rng (continuous.prod_mk f.continuous
      (mul_opposite.continuous_op.comp (continuous_iff_continuous_at.mpr (λ x, _)))),
    have := normed_ring.inverse_continuous_at (h x).unit,
    simp only [←ring.inverse_unit, is_unit.unit_spec, ←function.comp_apply] at this ⊢,
    exact this.comp (f.continuous_at x),
  end }

instance : can_lift C(α, β) C(α, βˣ) :=
{ coe := λ f, ⟨λ x, f x, units.continuous_coe.comp f.continuous⟩,
  cond := λ f, ∀ x, is_unit (f x),
  prf := λ f h, ⟨units_of_forall_is_unit h, by { ext, refl }⟩ }

lemma is_unit_iff_forall_is_unit (f : C(α, β)) :
  is_unit f ↔ ∀ x, is_unit (f x) :=
iff.intro (λ h, λ x, ⟨units_lift.symm h.unit x, rfl⟩)
  (λ h, ⟨(units_of_forall_is_unit h).units_lift, by { ext, refl }⟩)

end normed_ring

section normed_field

variables {𝕜 : Type*} [normed_field 𝕜] [complete_space 𝕜]

lemma is_unit_iff_forall_ne_zero (f : C(α, 𝕜)) :
  is_unit f ↔ ∀ x, f x ≠ 0 :=
by simp_rw [f.is_unit_iff_forall_is_unit, is_unit_iff_ne_zero]

lemma spectrum_eq_range (f : C(α, 𝕜)) :
  spectrum 𝕜 f = set.range f :=
by { ext, simp only [spectrum.mem_iff, is_unit_iff_forall_ne_zero, not_forall, coe_sub,
       pi.sub_apply, algebra_map_apply, algebra.id.smul_eq_mul, mul_one, not_not, set.mem_range,
       sub_eq_zero, @eq_comm _ x _] }

end normed_field

end continuous_map
