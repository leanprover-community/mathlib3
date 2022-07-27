/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.idempotents.karoubi

/-!
# Idempotent completeness and functor categories

In this file we define an instance `functor_category_is_idempotent_complete` expressing
that a functor category `J ⥤ C` is idempotent complete when the target category `C` is.

We also provide a fully faithful functor
`karoubi_functor_category_embedding : karoubi (J ⥤ C)) : J ⥤ karoubi C` for all categories
`J` and `C`.

-/

open category_theory
open category_theory.category
open category_theory.idempotents.karoubi
open category_theory.limits

namespace category_theory

namespace idempotents

variables (J C : Type*) [category J] [category C]

instance functor_category_is_idempotent_complete [is_idempotent_complete C] :
  is_idempotent_complete (J ⥤ C) :=
begin
  refine ⟨_⟩,
  intros F p hp,
  have hC := (is_idempotent_complete_iff_has_equalizer_of_id_and_idempotent C).mp infer_instance,
  haveI : ∀ (j : J), has_equalizer (𝟙 _) (p.app j) := λ j, hC _ _ (congr_app hp j),
  /- We construct the direct factor `Y` associated to `p : F ⟶ F` by computing
    the equalizer of the identity and `p.app j` on each object `(j : J)`.  -/
  let Y : J ⥤ C :=
  { obj := λ j, limits.equalizer (𝟙 _) (p.app j),
    map := λ j j' φ, equalizer.lift (limits.equalizer.ι (𝟙 _) (p.app j) ≫ F.map φ)
      (by rw [comp_id, assoc, p.naturality φ, ← assoc, ← limits.equalizer.condition, comp_id]),
    map_id' := λ j, by { ext, simp only [comp_id, functor.map_id, equalizer.lift_ι, id_comp], },
    map_comp' := λ j j' j'' φ φ', begin
      ext,
      simp only [assoc, functor.map_comp, equalizer.lift_ι, equalizer.lift_ι_assoc],
    end },
  let i : Y ⟶ F :=
  { app := λ j, equalizer.ι _ _,
    naturality' := λ j j' φ, by rw [equalizer.lift_ι],  },
  let e : F ⟶ Y :=
  { app := λ j, equalizer.lift (p.app j)
      (by { rw comp_id, exact (congr_app hp j).symm, }),
    naturality' := λ j j' φ, begin
      ext,
      simp only [assoc, equalizer.lift_ι, nat_trans.naturality, equalizer.lift_ι_assoc],
    end },
  use [Y, i, e],
  split; ext j,
  { simp only [nat_trans.comp_app, assoc, equalizer.lift_ι, nat_trans.id_app, id_comp,
      ← equalizer.condition, comp_id], },
  { simp only [nat_trans.comp_app, equalizer.lift_ι], },
end

namespace karoubi_functor_category_embedding

variables {J C}

/-- On objects, the functor which sends a formal direct factor `P` of a
functor `F : J ⥤ C` to the functor `J ⥤ karoubi C` which sends `(j : J)` to
the corresponding direct factor of `F.obj j`. -/
@[simps]
def obj (P : karoubi (J ⥤ C)) : J ⥤ karoubi C :=
{ obj := λ j, ⟨P.X.obj j, P.p.app j, congr_app P.idem j⟩,
  map := λ j j' φ,
  { f := P.p.app j ≫ P.X.map φ,
    comm := begin
      simp only [nat_trans.naturality, assoc],
      have h := congr_app P.idem j,
      rw [nat_trans.comp_app] at h,
      slice_rhs 1 3 { erw [h, h], },
    end },
  map_id' := λ j, by { ext, simp only [functor.map_id, comp_id, id_eq], },
  map_comp' := λ j j' j'' φ φ', begin
    ext,
    have h := congr_app P.idem j,
    rw [nat_trans.comp_app] at h,
    simp only [assoc, nat_trans.naturality_assoc, functor.map_comp, comp],
    slice_rhs 1 2 { rw h, },
    rw [assoc],
  end }

/-- Tautological action on maps of the functor `karoubi (J ⥤ C) ⥤ (J ⥤ karoubi C)`. -/
@[simps]
def map {P Q : karoubi (J ⥤ C)} (f : P ⟶ Q) : obj P ⟶ obj Q :=
{ app := λ j, ⟨f.f.app j, congr_app f.comm j⟩,
  naturality' := λ j j' φ, begin
    ext,
    simp only [comp],
    have h := congr_app (comp_p f) j,
    have h' := congr_app (p_comp f) j',
    dsimp at h h' ⊢,
    slice_rhs 1 2 { erw h, },
    rw ← P.p.naturality,
    slice_lhs 2 3 { erw h', },
    rw f.f.naturality,
  end }

end karoubi_functor_category_embedding

variables (J C)

/-- The tautological fully faithful functor `karoubi (J ⥤ C) ⥤ (J ⥤ karoubi C)`. -/
@[simps]
def karoubi_functor_category_embedding :
  karoubi (J ⥤ C) ⥤ (J ⥤ karoubi C) :=
{ obj := karoubi_functor_category_embedding.obj,
  map := λ P Q, karoubi_functor_category_embedding.map,
  map_id' := λ P, rfl,
  map_comp' := λ P Q R f g, rfl, }

instance : full (karoubi_functor_category_embedding J C) :=
{ preimage := λ P Q f,
  { f :=
    { app := λ j, (f.app j).f,
      naturality' := λ j j' φ, begin
        slice_rhs 1 1 { rw ← karoubi.comp_p, },
        have h := hom_ext.mp (f.naturality φ),
        simp only [comp] at h,
        dsimp [karoubi_functor_category_embedding] at h ⊢,
        erw [assoc, ← h, ← P.p.naturality φ, assoc, p_comp (f.app j')],
      end },
    comm := by { ext j, exact (f.app j).comm, } },
  witness' := λ P Q f, by { ext j, refl, }, }

instance : faithful (karoubi_functor_category_embedding J C) :=
{ map_injective' := λ P Q f f' h, by { ext j, exact hom_ext.mp (congr_app h j), }, }

/-- The composition of `(J ⥤ C) ⥤ karoubi (J ⥤ C)` and `karoubi (J ⥤ C) ⥤ (J ⥤ karoubi C)`
equals the functor `(J ⥤ C) ⥤ (J ⥤ karoubi C)` given by the composition with
`to_karoubi C : C ⥤ karoubi C`. -/
lemma to_karoubi_comp_karoubi_functor_category_embedding :
  (to_karoubi _) ⋙ karoubi_functor_category_embedding J C =
  (whiskering_right J _ _).obj (to_karoubi C) :=
begin
  apply functor.ext,
  { intros X Y f,
    ext j,
    dsimp [to_karoubi],
    simp only [eq_to_hom_app, eq_to_hom_refl, id_comp],
    erw [comp_id], },
  { intro X,
    apply functor.ext,
    { intros j j' φ,
      ext,
      dsimp,
      simpa only [comp_id, id_comp], },
    { intro j,
      refl, }, }
end

end idempotents

end category_theory
