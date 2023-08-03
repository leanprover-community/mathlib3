/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import category_theory.limits.shapes.products
import category_theory.functor.epi_mono

/-!

# Adjunctions involving evaluation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show that evaluation of functors have adjoints, given the existence of (co)products.

-/

namespace category_theory

open category_theory.limits

universes v₁ v₂ u₁ u₂
variables {C : Type u₁} [category.{v₁} C] (D : Type u₂) [category.{v₂} D]

noncomputable theory

section

variables [∀ (a b : C), has_coproducts_of_shape (a ⟶ b) D]

/-- The left adjoint of evaluation. -/
@[simps]
def evaluation_left_adjoint (c : C) : D ⥤ C ⥤ D :=
{ obj := λ d,
  { obj := λ t, ∐ (λ i : c ⟶ t, d),
    map := λ u v f, sigma.desc $ λ g, sigma.ι (λ _, d) $ g ≫ f,
    map_id' := begin
      intros, ext ⟨j⟩, simp only [cofan.mk_ι_app, colimit.ι_desc, category.comp_id],
      congr' 1, rw category.comp_id,
    end,
    map_comp' := begin
      intros, ext, simp only [cofan.mk_ι_app, colimit.ι_desc_assoc, colimit.ι_desc],
      congr' 1, rw category.assoc,
    end },
  map := λ d₁ d₂ f,
  { app := λ e, sigma.desc $ λ h, f ≫ sigma.ι (λ _, d₂) h,
    naturality' := by { intros, ext, dsimp, simp } },
  map_id' := by { intros, ext x ⟨j⟩, dsimp, simp },
  map_comp' := by { intros, ext, dsimp, simp } }

/-- The adjunction showing that evaluation is a right adjoint. -/
@[simps unit_app counit_app_app]
def evaluation_adjunction_right (c : C) :
  evaluation_left_adjoint D c ⊣ (evaluation _ _).obj c :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ d F,
  { to_fun := λ f, sigma.ι (λ _, d) (𝟙 _) ≫ f.app c,
    inv_fun := λ f,
    { app := λ e, sigma.desc $ λ h, f ≫ F.map h,
      naturality' := by { intros, ext, dsimp, simp } },
    left_inv := begin
      intros f,
      ext x ⟨g⟩,
      dsimp,
      simp only [colimit.ι_desc, limits.cofan.mk_ι_app, category.assoc, ← f.naturality,
        evaluation_left_adjoint_obj_map, colimit.ι_desc_assoc, cofan.mk_ι_app],
      congr' 2,
      rw category.id_comp
    end,
    right_inv := λ f, by { dsimp, simp } },
  hom_equiv_naturality_left_symm' := by { intros, ext, dsimp, simp },
  hom_equiv_naturality_right' := by { intros, dsimp, simp } }

instance evaluation_is_right_adjoint (c : C) :
  is_right_adjoint ((evaluation _ D).obj c) :=
⟨_, evaluation_adjunction_right _ _⟩

lemma nat_trans.mono_iff_mono_app {F G : C ⥤ D} (η : F ⟶ G) :
  mono η ↔ (∀ c, mono (η.app c)) :=
begin
  split,
  { introsI h c,
    exact (infer_instance : mono (((evaluation _ _).obj c).map η)) },
  { introsI _,
    apply nat_trans.mono_of_mono_app }
end

end

section

variables [∀ (a b : C), has_products_of_shape (a ⟶ b) D]

/-- The right adjoint of evaluation. -/
@[simps]
def evaluation_right_adjoint (c : C) : D ⥤ C ⥤ D :=
{ obj := λ d,
  { obj := λ t, ∏ (λ i : t ⟶ c, d),
    map := λ u v f, pi.lift $ λ g, pi.π _ $ f ≫ g,
    map_id' := begin
      intros, ext ⟨j⟩, dsimp,
      simp only [limit.lift_π, category.id_comp, fan.mk_π_app],
      congr, simp,
    end,
    map_comp' := begin
      intros, ext ⟨j⟩, dsimp,
      simp only [limit.lift_π, fan.mk_π_app, category.assoc],
      congr' 1, simp,
    end },
  map := λ d₁ d₂ f,
  { app := λ t, pi.lift $ λ g, pi.π _ g ≫ f,
    naturality' := by { intros, ext, dsimp, simp } },
  map_id' := by { intros, ext x ⟨j⟩, dsimp, simp },
  map_comp' := by { intros, ext, dsimp, simp } }

/-- The adjunction showing that evaluation is a left adjoint. -/
@[simps unit_app_app counit_app]
def evaluation_adjunction_left (c : C) :
  (evaluation _ _).obj c ⊣ evaluation_right_adjoint D c :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ F d,
  { to_fun := λ f,
    { app := λ t, pi.lift $ λ g, F.map g ≫ f,
      naturality' := by { intros, ext, dsimp, simp } },
    inv_fun := λ f, f.app _ ≫ pi.π _ (𝟙 _),
    left_inv := λ f, by { dsimp, simp },
    right_inv := begin
      intros f,
      ext x ⟨g⟩,
      dsimp,
      simp only [limit.lift_π, evaluation_right_adjoint_obj_map,
        nat_trans.naturality_assoc, fan.mk_π_app],
      congr,
      rw category.comp_id
    end },
  hom_equiv_naturality_left_symm' := by { intros, dsimp, simp },
  hom_equiv_naturality_right' := by { intros, ext, dsimp, simp } }

instance evaluation_is_left_adjoint (c : C) :
  is_left_adjoint ((evaluation _ D).obj c) :=
⟨_, evaluation_adjunction_left _ _⟩

lemma nat_trans.epi_iff_epi_app {F G : C ⥤ D} (η : F ⟶ G) :
  epi η ↔ (∀ c, epi (η.app c)) :=
begin
  split,
  { introsI h c,
    exact (infer_instance : epi (((evaluation _ _).obj c).map η)) },
  { introsI,
    apply nat_trans.epi_of_epi_app }
end

end

end category_theory
