/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Johan Commelin
-/
import group_theory.quotient_group
import group_theory.subgroup.basic
import algebra.category.Group.basic
import category_theory.epi_mono

/-!
# Monomorphisms in `AddCommGroup`

This file shows that a homomorphism of abelian groups is a monomorphism in the category abelian
groups if and only if it is injective, and similarly an epimorphism if and only if it is surjective.
-/

universe u

open category_theory category_theory.preadditive AddCommGroup

namespace AddCommGroup

variables {X Y : AddCommGroup.{u}} (f : X ⟶ Y)

lemma ker_eq_bot_of_mono [mono f] : f.ker = ⊥ :=
begin
  have aux : f.comp f.ker.subtype = f.comp 0,
  { ext x,
    simpa only [add_monoid_hom.coe_comp, add_subgroup.coe_subtype, function.comp_app,
      add_monoid_hom.comp_zero, add_monoid_hom.zero_apply] using x.2 },
  have := (@cancel_mono AddCommGroup _ _ _ (AddCommGroup.of f.ker) f _ f.ker.subtype _).mp aux,
  exact eq_bot_iff.2 (λ x hx, add_monoid_hom.congr_fun this ⟨x, hx⟩)
end

lemma range_eq_top_of_epi [epi f] : f.range = ⊤ :=
begin
  let g : Y →+ Y ⧸ f.range := quotient_add_group.mk' f.range,
  have aux : g.comp f = add_monoid_hom.comp 0 f,
  { ext x,
    simp only [add_monoid_hom.coe_comp, quotient_add_group.coe_mk', add_monoid_hom.zero_comp,
      add_monoid_hom.zero_apply, quotient_add_group.eq_zero_iff, add_monoid_hom.mem_range,
      exists_apply_eq_apply] },
  have := (@cancel_epi AddCommGroup _ _ _ (AddCommGroup.of $ Y ⧸ f.range) f _ g _).mp aux,
  refine eq_top_iff.2 (λ x hx, (quotient_add_group.eq_zero_iff _).1 _),
  exact add_monoid_hom.congr_fun this x,
end

lemma mono_iff_ker_eq_bot : mono f ↔ f.ker = ⊥ :=
⟨λ hf, by exactI ker_eq_bot_of_mono _,
 λ hf, concrete_category.mono_of_injective _ $ (add_monoid_hom.ker_eq_bot_iff _).1 hf⟩

lemma mono_iff_injective : mono f ↔ function.injective f :=
by rw [mono_iff_ker_eq_bot, add_monoid_hom.ker_eq_bot_iff]

lemma epi_iff_range_eq_top : epi f ↔ f.range = ⊤ :=
⟨λ hf, by exactI range_eq_top_of_epi _,
 λ hf, concrete_category.epi_of_surjective _ $ add_monoid_hom.range_top_iff_surjective.1 hf⟩

lemma epi_iff_surjective : epi f ↔ function.surjective f :=
by rw [epi_iff_range_eq_top, add_monoid_hom.range_top_iff_surjective]

end AddCommGroup
