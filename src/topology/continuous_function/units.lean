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
and `β` is a normed ring.
-/

section units

section normed_ring

variables {α : Type*} [topological_space α] {β : Type*} [normed_ring β]

/-- Equivalence between continuous maps into the units of a normed ring the
the units of the ring of continuous functions. -/
@[simps]
def continuous_map.units_lift : C(α, βˣ) ≃ C(α, β)ˣ :=
{ to_fun := λ f,
  { val := ⟨coe ∘ f, units.continuous_coe.comp f.continuous⟩,
    inv := ⟨λ x, ↑(f x)⁻¹, units.continuous_coe.comp (continuous_inv.comp f.continuous)⟩,
    val_inv := by { ext, simp only [continuous_map.coe_mul, continuous_map.coe_mk, pi.mul_apply,
      units.mul_inv, continuous_map.coe_one, pi.one_apply] },
    inv_val := by { ext, simp only [continuous_map.coe_mul, continuous_map.coe_mk, pi.mul_apply,
      units.inv_mul, continuous_map.coe_one, pi.one_apply]} },
  inv_fun := λ f,
  { to_fun := λ x, ⟨f x, f⁻¹ x, (f.val.coe_mul f.inv ▸ continuous_map.congr_fun f.val_inv x),
                                (f.inv.coe_mul f.val ▸ continuous_map.congr_fun f.inv_val x)⟩,
    continuous_to_fun := continuous_induced_rng (continuous.prod_mk (f : C(α, β)).continuous
      $ mul_opposite.continuous_op.comp (continuous_map.continuous (f⁻¹ : C(α, β)ˣ))) },
  left_inv := λ f, by { ext, refl },
  right_inv := λ f, by { ext, refl } }

/-- Construct a continuous map into the group of units of a normed ring from a function into the
normed ring and a proof that every element of the range is a unit. -/
@[simps]
noncomputable def continuous_map.units_of_forall_is_unit [complete_space β] {f : C(α, β)}
  (h : ∀ x, is_unit (f x)) : C(α, βˣ) :=
{ to_fun := λ x, (h x).unit,
  continuous_to_fun :=
  begin
    refine continuous_induced_rng (continuous.prod_mk f.continuous
      (mul_opposite.continuous_op.comp (continuous_iff_continuous_at.mpr (λ x, _)))),
    have := normed_ring.inverse_continuous_at (h x).unit,
    simp only [←ring.inverse_unit, is_unit.unit_spec, ←function.comp_apply] at this ⊢,
    exact this.comp (f.continuous_at x),
  end }

instance [complete_space β] : can_lift C(α, β) C(α, βˣ) :=
{ coe := λ f, ⟨coe ∘ f, units.continuous_coe.comp f.continuous⟩,
  cond := λ f, ∀ x, is_unit (f x),
  prf := λ f h, ⟨continuous_map.units_of_forall_is_unit h, by { ext, refl }⟩ }

lemma continuous_map.is_unit_iff_forall_is_unit [complete_space β] (f : C(α, β)) :
  is_unit f ↔ ∀ x, is_unit (f x) :=
begin
  refine iff.intro (λ h, _) (λ h, _),
  { lift f to C(α, β)ˣ using h,
    exact λ x, ⟨⟨f x, f⁻¹ x, (f.val.coe_mul f.inv ▸ continuous_map.congr_fun f.val_inv x),
                             (f.inv.coe_mul f.val ▸ continuous_map.congr_fun f.inv_val x)⟩, rfl⟩ },
  { refine ⟨(continuous_map.units_of_forall_is_unit h).units_lift, by { ext, refl }⟩ }
end

end normed_ring

section normed_field

variables {α : Type*} [topological_space α] {𝕜 : Type*} [normed_field 𝕜] [complete_space 𝕜]

lemma continuous_map.is_unit_iff_forall_ne_zero (f : C(α, 𝕜)) :
  is_unit f ↔ ∀ x, f x ≠ 0 :=
by simp_rw [f.is_unit_iff_forall_is_unit, is_unit_iff_ne_zero]

lemma continuous_map.spectrum_eq_range (f : C(α, 𝕜)) :
  spectrum 𝕜 f = set.range f :=
by { ext, simp only [spectrum.mem_iff, continuous_map.is_unit_iff_forall_ne_zero, not_forall,
       continuous_map.coe_sub, pi.sub_apply, algebra_map_apply, algebra.id.smul_eq_mul,
       mul_one, not_not, set.mem_range, sub_eq_zero, @eq_comm _ x _] }

end normed_field

end units
