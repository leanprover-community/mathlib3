/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

Facts about epimorphisms and monomorphisms.

The definitions of `epi` and `mono` are in `category_theory.category`,
since they are used by some lemmas for `iso`, which is used everywhere.
-/

import category_theory.adjunction.basic
import category_theory.fully_faithful

universes v₁ v₂ u₁ u₂

namespace category_theory

variables {C : Sort u₁} [𝒞 : category.{v₁} C] {D : Sort u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

lemma left_adjoint_preserves_epi {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  {X Y : C} {f : X ⟶ Y} (hf : epi f) : epi (F.map f) :=
begin
  constructor,
  intros Z g h H,
  replace H := congr_arg (adj.hom_equiv X Z) H,
  rwa [adj.hom_equiv_naturality_left, adj.hom_equiv_naturality_left,
    cancel_epi, equiv.apply_eq_iff_eq] at H
end

lemma right_adjoint_preserves_mono {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  {X Y : D} {f : X ⟶ Y} (hf : mono f) : mono (G.map f) :=
begin
  constructor,
  intros Z g h H,
  replace H := congr_arg (adj.hom_equiv Z Y).symm H,
  rwa [adj.hom_equiv_naturality_right_symm, adj.hom_equiv_naturality_right_symm,
    cancel_mono, equiv.apply_eq_iff_eq] at H
end

lemma faithful_reflects_epi (F : C ⥤ D) [faithful F] {X Y : C} {f : X ⟶ Y}
  (hf : epi (F.map f)) : epi f :=
⟨λ Z g h H, F.injectivity $
  by rw [←cancel_epi (F.map f), ←F.map_comp, ←F.map_comp, H]⟩

lemma faithful_reflects_mono (F : C ⥤ D) [faithful F] {X Y : C} {f : X ⟶ Y}
  (hf : mono (F.map f)) : mono f :=
⟨λ Z g h H, F.injectivity $
  by rw [←cancel_mono (F.map f), ←F.map_comp, ←F.map_comp, H]⟩

end category_theory
