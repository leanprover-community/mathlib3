/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.idempotents.karoubi

/-!
# Extension of functors to the idempotent completion

In this file, we construct an extension `functor_extension₁`
of functors `C ⥤ karoubi D` to functors `karoubi C ⥤ karoubi D`. This results in an
equivalence `karoubi_universal₁ C D : (C ⥤ karoubi D) ≌ (karoubi C ⥤ karoubi D)`.

We also construct an extension `functor_extension₂` of functors
`(C ⥤ D) ⥤ (karoubi C ⥤ karoubi D)`. Moreover,
when `D` is idempotent complete, we get equivalences
`karoubi_universal₂ C D : C ⥤ D ≌ karoubi C ⥤ karoubi D`
and `karoubi_universal C D : C ⥤ D ≌ karoubi C ⥤ D`.

We occasionally state and use equalities of functors because it is
sometimes convenient to use rewrites when proving properties of
functors obtained using the constructions in this file. Users are
encouraged to use the corresponding natural isomorphism
whenever possible.

-/

open category_theory.category
open category_theory.idempotents.karoubi

namespace category_theory

namespace idempotents

variables {C D E : Type*} [category C] [category D] [category E]

/-- A natural transformation between functors `karoubi C ⥤ D` is determined
by its value on objects coming from `C`. -/
lemma nat_trans_eq {F G : karoubi C ⥤ D} (φ : F ⟶ G) (P : karoubi C) :
  φ.app P = F.map (decomp_id_i P) ≫ φ.app P.X ≫ G.map (decomp_id_p P) :=
begin
  rw [← φ.naturality, ← assoc, ← F.map_comp],
  conv { to_lhs, rw [← id_comp (φ.app P), ← F.map_id], },
  congr,
  apply decomp_id,
end

namespace functor_extension₁

/-- The canonical extension of a functor `C ⥤ karoubi D` to a functor
`karoubi C ⥤ karoubi D` -/
@[simps]
def obj (F : C ⥤ karoubi D) : karoubi C ⥤ karoubi D :=
{ obj := λ P, ⟨(F.obj P.X).X, (F.map P.p).f,
    by simpa only [F.map_comp, hom_ext] using F.congr_map P.idem⟩,
  map := λ P Q f, ⟨(F.map f.f).f,
    by simpa only [F.map_comp, hom_ext] using F.congr_map f.comm⟩, }

/-- Extension of a natural transformation `φ` between functors
`C ⥤ karoubi D` to a natural transformation between the
extension of these functors to `karoubi C ⥤ karoubi D` -/
@[simps]
def map {F G : C ⥤ karoubi D} (φ : F ⟶ G) : obj F ⟶ obj G :=
{ app := λ P,
  { f := (F.map P.p).f ≫ (φ.app P.X).f,
    comm := begin
      have h := φ.naturality P.p,
      have h' := F.congr_map P.idem,
      simp only [hom_ext, karoubi.comp_f, F.map_comp] at h h',
      simp only [obj_obj_p, assoc, ← h],
      slice_rhs 1 3 { rw [h', h'], },
    end, },
  naturality' := λ P Q f, begin
    ext,
    dsimp [obj],
    have h := φ.naturality f.f,
    have h' := F.congr_map (comp_p f),
    have h'' := F.congr_map (p_comp f),
    simp only [hom_ext, functor.map_comp, comp_f] at ⊢ h h' h'',
    slice_rhs 2 3 { rw ← h, },
    slice_lhs 1 2 { rw h', },
    slice_rhs 1 2 { rw h'', },
  end }

end functor_extension₁

variables (C D E)

/-- The canonical functor `(C ⥤ karoubi D) ⥤ (karoubi C ⥤ karoubi D)` -/
@[simps]
def functor_extension₁ : (C ⥤ karoubi D) ⥤ (karoubi C ⥤ karoubi D) :=
{ obj := functor_extension₁.obj,
  map := λ F G, functor_extension₁.map,
  map_id' := λ F, by { ext P, exact comp_p (F.map P.p), },
  map_comp' := λ F G H φ φ', begin
    ext P,
    simp only [comp_f, functor_extension₁.map_app_f, nat_trans.comp_app, assoc],
    have h := φ.naturality P.p,
    have h' := F.congr_map P.idem,
    simp only [hom_ext, comp_f, F.map_comp] at h h',
    slice_rhs 2 3 { rw ← h, },
    slice_rhs 1 2 { rw h', },
    simp only [assoc],
  end, }

lemma functor_extension₁_comp_whiskering_left_to_karoubi :
  functor_extension₁ C D ⋙
    (whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C) = 𝟭 _ :=
begin
  refine functor.ext _ _,
  { intro F,
    refine functor.ext _ _,
    { intro X,
      ext,
      { dsimp,
        rw [id_comp, comp_id, F.map_id, id_eq], },
      { refl, }, },
    { intros X Y f,
      ext,
      dsimp,
      simp only [comp_id, eq_to_hom_f, eq_to_hom_refl, comp_p, functor_extension₁.obj_obj_p,
        to_karoubi_obj_p, comp_f],
      dsimp,
      simp only [functor.map_id, id_eq, p_comp], }, },
  { intros F G φ,
    ext X,
    dsimp,
    simp only [eq_to_hom_app, F.map_id, comp_f, eq_to_hom_f, id_eq, p_comp,
      eq_to_hom_refl, comp_id, comp_p, functor_extension₁.obj_obj_p,
      to_karoubi_obj_p, F.map_id X], },
end

/-- The natural isomorphism expressing that functors `karoubi C ⥤ karoubi D` obtained
using `functor_extension₁` actually extends the original functors `C ⥤ karoubi D`. -/
@[simps]
def functor_extension₁_comp_whiskering_left_to_karoubi_iso :
  functor_extension₁ C D ⋙
    (whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C) ≅ 𝟭 _ :=
eq_to_iso (functor_extension₁_comp_whiskering_left_to_karoubi C D)

/-- The counit isomorphism of the equivalence `(C ⥤ karoubi D) ≌ (karoubi C ⥤ karoubi D)`. -/
@[simps]
def karoubi_universal₁.counit_iso :
  (whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C) ⋙
    functor_extension₁ C D ≅ 𝟭 _ :=
nat_iso.of_components (λ G,
  { hom :=
    { app := λ P,
      { f := (G.map (decomp_id_p P)).f,
        comm := by simpa only [hom_ext, G.map_comp, G.map_id] using G.congr_map
          (show P.decomp_id_p = (to_karoubi C).map P.p ≫ P.decomp_id_p ≫ 𝟙 _, by simp), },
      naturality' := λ P Q f,
        by simpa only [hom_ext, G.map_comp] using (G.congr_map (decomp_id_p_naturality f)).symm, },
    inv :=
    { app := λ P,
      { f := (G.map (decomp_id_i P)).f,
        comm := by simpa only [hom_ext, G.map_comp, G.map_id] using G.congr_map
          (show P.decomp_id_i = 𝟙 _ ≫ P.decomp_id_i ≫ (to_karoubi C).map P.p, by simp), },
      naturality' := λ P Q f,
        by simpa only [hom_ext, G.map_comp] using G.congr_map (decomp_id_i_naturality f), },
    hom_inv_id' := begin
      ext P,
      simpa only [hom_ext, G.map_comp, G.map_id] using G.congr_map P.decomp_p.symm,
    end,
    inv_hom_id' := begin
      ext P,
      simpa only [hom_ext, G.map_comp, G.map_id] using G.congr_map P.decomp_id.symm,
    end, })
(λ G₁ G₂ φ, begin
  ext P,
  dsimp,
  simpa only [nat_trans_eq φ P, comp_f, functor_extension₁.map_app_f,
    functor.comp_map, whisker_left_app, assoc, P.decomp_p, G₁.map_comp],
end)

/-- The equivalence of categories `(C ⥤ karoubi D) ≌ (karoubi C ⥤ karoubi D)`. -/
@[simps]
def karoubi_universal₁ : (C ⥤ karoubi D) ≌ (karoubi C ⥤ karoubi D) :=
{ functor := functor_extension₁ C D,
  inverse := (whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C),
  unit_iso := (functor_extension₁_comp_whiskering_left_to_karoubi_iso C D).symm,
  counit_iso := karoubi_universal₁.counit_iso C D,
  functor_unit_iso_comp' := λ F, begin
    ext P,
    dsimp [functor_extension₁.map, karoubi_universal₁.counit_iso],
    simpa only [comp_f, eq_to_hom_app, eq_to_hom_f, eq_to_hom_refl, comp_id,
      hom_ext, F.map_comp, comp_p] using F.congr_map P.idem,
  end, }

lemma functor_extension₁_comp (F : C ⥤ karoubi D) (G : D ⥤ karoubi E) :
  (functor_extension₁ C E).obj (F ⋙ (functor_extension₁ D E).obj G) =
    (functor_extension₁ C D).obj F ⋙ (functor_extension₁ D E).obj G :=
functor.ext (by tidy) (λ X Y f, by { dsimp, simpa only [id_comp, comp_id], })

/-- The canonical functor `(C ⥤ D) ⥤ (karoubi C ⥤ karoubi D)` -/
@[simps]
def functor_extension₂ : (C ⥤ D) ⥤ (karoubi C ⥤ karoubi D) :=
(whiskering_right C D (karoubi D)).obj (to_karoubi D) ⋙ functor_extension₁ C D

lemma functor_extension₂_comp_whiskering_left_to_karoubi :
  functor_extension₂ C D ⋙ (whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C) =
  (whiskering_right C D (karoubi D)).obj (to_karoubi D) :=
by simp only [functor_extension₂, functor.assoc,
  functor_extension₁_comp_whiskering_left_to_karoubi, functor.comp_id]

/-- The natural isomorphism expressing that functors `karoubi C ⥤ karoubi D` obtained
using `functor_extension₂` actually extends the original functors `C ⥤ D`. -/
@[simps]
def functor_extension₂_comp_whiskering_left_to_karoubi_iso :
  functor_extension₂ C D ⋙ (whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C) ≅
  (whiskering_right C D (karoubi D)).obj (to_karoubi D) :=
eq_to_iso (functor_extension₂_comp_whiskering_left_to_karoubi C D)

section is_idempotent_complete

variable [is_idempotent_complete D]

noncomputable instance : is_equivalence (to_karoubi D) := to_karoubi_is_equivalence D

/-- The equivalence of categories `(C ⥤ D) ≌ (karoubi C ⥤ karoubi D)` when `D`
is idempotent complete. -/
@[simps]
noncomputable def karoubi_universal₂ : (C ⥤ D) ≌ (karoubi C ⥤ karoubi D) :=
(equivalence.congr_right (to_karoubi D).as_equivalence).trans
    (karoubi_universal₁ C D)

lemma karoubi_universal₂_functor_eq :
  (karoubi_universal₂ C D).functor = functor_extension₂ C D := rfl

noncomputable instance : is_equivalence (functor_extension₂ C D) :=
by { rw ← karoubi_universal₂_functor_eq, apply_instance, }

/-- The extension of functors functor `(C ⥤ D) ⥤ (karoubi C ⥤ D)`
when `D` is idempotent compltete. -/
@[simps]
noncomputable def functor_extension : (C ⥤ D) ⥤ (karoubi C ⥤ D) :=
functor_extension₂ C D ⋙ (whiskering_right (karoubi C) (karoubi D) D).obj
    (to_karoubi_is_equivalence D).inverse

/-- The equivalence `(C ⥤ D) ≌ (karoubi C ⥤ D)` when `D` is idempotent complete. -/
@[simps]
noncomputable def karoubi_universal : (C ⥤ D) ≌ (karoubi C ⥤ D) :=
(karoubi_universal₂ C D).trans (equivalence.congr_right (to_karoubi D).as_equivalence.symm)

lemma karoubi_universal_functor_eq :
  (karoubi_universal C D).functor = functor_extension C D := rfl

noncomputable instance : is_equivalence (functor_extension C D) :=
by { rw ← karoubi_universal_functor_eq, apply_instance, }

noncomputable instance : is_equivalence ((whiskering_left C (karoubi C) D).obj (to_karoubi C)) :=
is_equivalence.cancel_comp_right _ ((whiskering_right C _ _).obj (to_karoubi D) ⋙
    (whiskering_right C _ _).obj (to_karoubi D).inv)
  (is_equivalence.of_equivalence (@equivalence.congr_right _ _ _ _ C _
      ((to_karoubi D).as_equivalence.trans (to_karoubi D).as_equivalence.symm)))
  (by { change is_equivalence (karoubi_universal C D).inverse, apply_instance, })

variables {C D}

lemma whiskering_left_obj_preimage_app {F G : karoubi C ⥤ D}
  (τ : to_karoubi _ ⋙ F ⟶ to_karoubi _ ⋙ G) (P : karoubi C) :
  (((whiskering_left _ _ _).obj (to_karoubi _)).preimage τ).app P =
    F.map P.decomp_id_i ≫ τ.app P.X ≫ G.map P.decomp_id_p :=
begin
  rw nat_trans_eq,
  congr' 2,
  exact congr_app (((whiskering_left _ _ _).obj (to_karoubi _)).image_preimage τ) P.X,
end

end is_idempotent_complete

end idempotents

end category_theory
