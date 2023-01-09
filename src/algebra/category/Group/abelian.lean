/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.category.Group.Z_Module_equivalence
import algebra.category.Group.limits
import algebra.category.Group.colimits
import algebra.category.Module.abelian
import category_theory.abelian.functor_category
import category_theory.abelian.ab5

/-!
# The category of abelian groups is abelian
-/

open category_theory
open category_theory.limits

universe u

noncomputable theory

namespace AddCommGroup

section
variables {X Y : AddCommGroup.{u}} (f : X ⟶ Y)

/-- In the category of abelian groups, every monomorphism is normal. -/
def normal_mono (hf : mono f) : normal_mono f :=
equivalence_reflects_normal_mono (forget₂ (Module.{u} ℤ) AddCommGroup.{u}).inv $
  Module.normal_mono _ infer_instance

/-- In the category of abelian groups, every epimorphism is normal. -/
def normal_epi (hf : epi f) : normal_epi f :=
equivalence_reflects_normal_epi (forget₂ (Module.{u} ℤ) AddCommGroup.{u}).inv $
  Module.normal_epi _ infer_instance

end

/-- The category of abelian groups is abelian. -/
instance : abelian AddCommGroup.{u} :=
{ has_finite_products := ⟨by apply_instance⟩,
  normal_mono_of_mono := λ X Y, normal_mono,
  normal_epi_of_epi := λ X Y, normal_epi,
  add_comp' := by { intros, simp only [preadditive.add_comp] },
  comp_add' := by { intros, simp only [preadditive.comp_add] } }

theorem exact_colim_of_exact_of_is_filtered {J : Type u} [small_category J] [is_filtered J]
  (F G H : J ⥤ AddCommGroup.{u}) (η : F ⟶ G) (γ : G ⟶ H) :
  (∀ j, exact (η.app j) (γ.app j)) → exact (limits.colim_map η) (limits.colim_map γ) :=
begin
  /-intros h,
  rw AddCommGroup.exact_iff', split,
  { ext1 j, simp [reassoc_of (h j).1] },
  { rintros x (hx : _ = _),
    obtain ⟨j,y,rfl⟩ := limits.concrete.colimit_exists_rep _ x,
    erw [← comp_apply, limits.colimit.ι_desc] at hx, dsimp at hx,
    rw comp_apply at hx,
    have : (0 : limits.colimit H) = limits.colimit.ι H j 0, by simp, rw this at hx, clear this,
    obtain ⟨k,e₁,e₂,hk⟩ := limits.concrete.colimit_exists_of_rep_eq _ _ _ hx,
    simp only [map_zero, ← comp_apply, ← nat_trans.naturality] at hk, rw comp_apply at hk,
    obtain ⟨t,ht⟩ := ((AddCommGroup.exact_iff' _ _).1 (h k)).2 hk,
    use limits.colimit.ι F k t,
    erw [← comp_apply, limits.colimit.ι_map, comp_apply, ht, ← comp_apply],
    congr' 1, simp }-/
  sorry
end

instance : ab5 AddCommGroup.{u} :=
{ has_colimits := infer_instance,
  preserves_finite_limits_colim :=
  begin
    introsI J sJ fJ,
    apply functor.preserves_finite_limits_of_map_exact,
    intros X Y Z f g h,
    apply exact_colim_of_exact_of_is_filtered,
    exact (abelian.nat_trans.exact_iff_forall.{u (u+1) u u} f g).1 h
  end }

end AddCommGroup
