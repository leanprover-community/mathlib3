/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.Group.epi_mono
import algebra.category.Module.epi_mono
import algebra.module.injective
import category_theory.preadditive.injective
import group_theory.divisible
import ring_theory.principal_ideal_domain

/-!
# Injective objects in the category of abelian groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that divisible groups are injective object in category of (additive) abelian
groups.

-/

open category_theory
open_locale pointwise

universe u

variables (A : Type u) [add_comm_group A]

namespace AddCommGroup

lemma injective_of_injective_as_module [injective (⟨A⟩ : Module ℤ)] :
  category_theory.injective (⟨A⟩ : AddCommGroup) :=
{ factors := λ X Y g f m,
  begin
    resetI,
    let G : (⟨X⟩ : Module ℤ) ⟶ ⟨A⟩ :=
      { map_smul' := by { intros, rw [ring_hom.id_apply, g.to_fun_eq_coe, map_zsmul], }, ..g },
    let F : (⟨X⟩ : Module ℤ) ⟶ ⟨Y⟩ :=
      { map_smul' := by { intros, rw [ring_hom.id_apply, f.to_fun_eq_coe, map_zsmul], }, ..f },
    haveI : mono F,
    { refine ⟨λ Z α β eq1, _⟩,
      let α' : AddCommGroup.of Z ⟶ X := α.to_add_monoid_hom,
      let β' : AddCommGroup.of Z ⟶ X := β.to_add_monoid_hom,
      have eq2 : α' ≫ f = β' ≫ f,
      { ext,
        simp only [category_theory.comp_apply, linear_map.to_add_monoid_hom_coe],
        simpa only [Module.coe_comp, linear_map.coe_mk,
          function.comp_app] using fun_like.congr_fun eq1 x },
      rw cancel_mono at eq2,
      ext, simpa only using fun_like.congr_fun eq2 x, },
    refine ⟨(injective.factor_thru G F).to_add_monoid_hom, _⟩,
    ext, convert fun_like.congr_fun (injective.comp_factor_thru G F) x,
  end }

lemma injective_as_module_of_injective_as_Ab [injective (⟨A⟩ : AddCommGroup)] :
  injective (⟨A⟩ : Module ℤ) :=
{ factors := λ X Y g f m,
  begin
    resetI,
    let G : (⟨X⟩ : AddCommGroup) ⟶ ⟨A⟩ := g.to_add_monoid_hom,
    let F : (⟨X⟩ : AddCommGroup) ⟶ ⟨Y⟩ := f.to_add_monoid_hom,
    haveI : mono F,
    { rw mono_iff_injective, intros _ _ h, exact ((Module.mono_iff_injective f).mp m) h, },
    refine ⟨{map_smul' := _, ..injective.factor_thru G F}, _⟩,
    { intros m x, rw [add_monoid_hom.to_fun_eq_coe, ring_hom.id_apply],
      induction m using int.induction_on with n hn n hn,
      { rw [zero_smul],
        convert map_zero _,
        convert zero_smul _ x, },
      { simp only [add_smul, map_add, hn, one_smul], },
      { simp only [sub_smul, map_sub, hn, one_smul] }, },
    ext, convert fun_like.congr_fun (injective.comp_factor_thru G F) x,
  end }

instance injective_of_divisible [divisible_by A ℤ] :
  category_theory.injective (⟨A⟩ : AddCommGroup) :=
@@injective_of_injective_as_module A _ $
@@module.injective_object_of_injective_module ℤ _ A _ _ $
module.Baer.injective $
λ I g, begin
  rcases is_principal_ideal_ring.principal I with ⟨m, rfl⟩,
  by_cases m_eq_zero : m = 0,
  { subst m_eq_zero,
    refine ⟨{ to_fun := _, map_add' := _, map_smul' := _ }, λ n hn, _⟩,
    { intros n, exact g 0, },
    { intros n1 n2,
      simp only [map_zero, add_zero] },
    { intros n1 n2,
      simp only [map_zero, smul_zero], },
    { rw [submodule.span_singleton_eq_bot.mpr rfl, submodule.mem_bot] at hn,
      simp only [hn, map_zero],
      symmetry,
      convert map_zero _, }, },
  { set gₘ := g ⟨m, submodule.subset_span (set.mem_singleton _)⟩ with gm_eq,
    refine ⟨{ to_fun := _, map_add' := _, map_smul' := _ }, λ n hn, _⟩,
    { intros n,
      exact n • divisible_by.div gₘ m, },
    { intros n1 n2, simp only [add_smul], },
    { intros n1 n2,
      rw [ring_hom.id_apply, smul_eq_mul, mul_smul], },
    { rw submodule.mem_span_singleton at hn,
      rcases hn with ⟨n, rfl⟩,
      simp only [gm_eq, algebra.id.smul_eq_mul, linear_map.coe_mk],
      rw [mul_smul, divisible_by.div_cancel (g ⟨m, _⟩) m_eq_zero, ←linear_map.map_smul],
      congr, }, },
end

end AddCommGroup
