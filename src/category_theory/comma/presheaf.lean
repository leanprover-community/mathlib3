/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.over

/-!
# Structured arrow and presheaves commute
-/

universes v u w v₂ u₂

open opposite

namespace category_theory
variables {C : Type u} [category.{v} C] (A : Cᵒᵖ ⥤ Type (max u v w))

section
variables {D : Type u₂} [category.{v₂} D] (F : C ⥤ D) (X : D) (f f' f'' : costructured_arrow F X)

@[simp]
lemma hom_mk_id : costructured_arrow.hom_mk (𝟙 f.left) (by simp) = 𝟙 _ :=
rfl

@[simp]
lemma hom_mk_comp {g : f.left ⟶ f'.left} {g' : f'.left ⟶ f''.left} {h h' h''} :
  costructured_arrow.hom_mk (g ≫ g') h'' =
    costructured_arrow.hom_mk g h ≫ costructured_arrow.hom_mk g' h' :=
by tidy

end

-- def CA := costructured_arrow (yoneda ⋙ (whiskering_right _ _ _).obj ulift_functor.{max u v w}) A
-- def CDA := over A
-- def CAD := costructured_arrow yoneda A ⥤ Type v

-- def q : costructured_arrow yoneda A ⥤ over A :=
-- costructured_arrow.pre yoneda (𝟭 _) A

section

abbreviation yoneda' : C ⥤ Cᵒᵖ ⥤ Type (max u v w) :=
yoneda ⋙ (whiskering_right _ _ _).obj ulift_functor.{max u v w}

@[simps]
def yoneda'_equiv {X : C} {F : Cᵒᵖ ⥤ Type (max u v w)} : (yoneda'.obj X ⟶ F) ≃ F.obj (op X) :=
{ to_fun := λ f, f.app (op X) (ulift.up (𝟙 _)),
  inv_fun := λ x,
  { app := λ Y f, F.map f.down.op x,
    naturality' := λ Y Z f, by { ext y, cases y, dsimp, simp } },
  left_inv :=
  begin
    intro f,
    ext Y g,
    dsimp,
    have := f.naturality g.down.op,
    dsimp at this,
    have hx := congr_fun this (ulift.up (𝟙 _)),
    dsimp at hx,
    convert hx.symm,
    ext, simp,
  end,
  right_inv :=
  begin
    tidy,
  end }



end

@[simps]
def as_presheaf_obj (f : over A) : (costructured_arrow (yoneda') A)ᵒᵖ ⥤ Type (max u v w) :=
{ obj := λ g, (costructured_arrow.pre (yoneda') (𝟭 _) A).obj g.unop ⟶ f,
  map := λ X Y f g, (costructured_arrow.pre yoneda' (𝟭 _) A).map f.unop ≫ g,
  map_id' := λ X, by { ext, simp only [unop_id, functor.map_id, category.id_comp, types_id_apply] },
  map_comp' := λ X Y Z f g,
    by { ext,
    simp only [unop_comp, functor.map_comp, over.comp_left, functor_to_types.comp, types_comp_apply], } }

@[simps]
def as_presheaf : over A ⥤ (costructured_arrow yoneda' A)ᵒᵖ ⥤ Type (max u v w) :=
{ obj := as_presheaf_obj A,
  map := λ X Y f,
  { app := λ Z g, g ≫ f,
    naturality' := λ U V g, by { ext, simp only [types_comp_apply, as_presheaf_obj_map, over.comp_left, functor_to_types.comp], } },
  map_id' := λ X, by { ext, simp only [types_id_apply, category.comp_id, nat_trans.id_app]},
  map_comp' := λ X Y Z f g, by { ext, simp } }

@[simps]
def from_presheaf_obj_obj (F : (costructured_arrow yoneda' A)ᵒᵖ ⥤ Type (max u v w)) :
  Cᵒᵖ ⥤ Type (max u v w) :=
{ obj := λ X, Σ (s : A.obj (op (unop X))), F.obj (op (costructured_arrow.mk (yoneda'_equiv.symm s))),
  map := λ X Y f g,
  begin
    refine ⟨A.map f g.1, _⟩,
    refine F.map (quiver.hom.op _) g.2,
    refine costructured_arrow.hom_mk f.unop _,
    sorry,
    -- cases g,
    -- ext Z h,
    -- cases h,
    -- dsimp, simp only [functor_to_types.map_comp_apply]
  end,
  map_id' := λ X,
  begin
    ext1 y,
    cases y,
    have : y_fst = A.map (𝟙 X) y_fst,
    { tidy, },
    rw ←this,
    erw hom_mk_id,
    simp,
  end,
  map_comp' := λ X Y Z f g,
  begin
    ext1 y,
    cases y,
    dsimp,
    rw A.map_comp,
    simp,
    dsimp,
    rw [← functor_to_types.map_comp_apply F],
    congr,
  end}


@[simps]
def from_presheaf_obj_map (F : (costructured_arrow yoneda' A)ᵒᵖ ⥤ Type (max u v w)) :
  from_presheaf_obj_obj A F ⟶ A :=
{ app := λ X f, f.fst,
  naturality' := λ X Y f, rfl }

@[simps]
def from_presheaf_obj (F : (costructured_arrow yoneda' A)ᵒᵖ ⥤ Type (max u v w)) : over A :=
over.mk (from_presheaf_obj_map A F)

@[simps]
def from_presheaf : ((costructured_arrow yoneda' A)ᵒᵖ ⥤ Type (max u v w)) ⥤ over A :=
{ obj := from_presheaf_obj A,
  map := λ X Y f, costructured_arrow.hom_mk
  { app := λ Z g, ⟨g.1, f.app _ g.2⟩,
    naturality' := λ U V g,
    begin
      ext1,
      cases x,
      simp only [types_comp_apply, from_presheaf_obj_left_map_snd],
      dsimp [from_presheaf_obj, from_presheaf_obj_obj],
      simp only [eq_self_iff_true, heq_iff_eq, true_and],
      exact congr_fun (f.naturality _) _,
    end }
    rfl,
  map_id' := λ X, by { dsimp, simp only [sigma.eta], refl },
  map_comp' := λ X Y Z f g, rfl }

def eqv : over A ≌ (costructured_arrow yoneda' A)ᵒᵖ ⥤ Type (max u v w) :=
equivalence.mk (as_presheaf A) (from_presheaf A)
  (nat_iso.of_components (λ X, over.iso_mk (nat_iso.of_components (λ Y, equiv.to_iso
  { to_fun := λ x,
    begin
      dsimp at x ⊢,
      refine ⟨X.hom.app Y x, over.hom_mk _ _⟩,
      { change X.left.obj (op (unop Y)) at x,
        exact yoneda'_equiv.symm x, },
      { dsimp,
        ext Z y,
        dsimp at y ⊢,
        exact congr_fun (X.hom.naturality y.down.op) _ }
    end,
    inv_fun := λ x,
    begin
      dsimp at x ⊢,
      change (X.left.obj (op (unop Y))),
      exact yoneda'_equiv x.snd.left,
    end,
    left_inv := λ x, by { dsimp, simp only [functor_to_types.m1ap_id_apply] },
    right_inv := λ x, by { dsimp,
      cases x,1111
      dsimp,
      sorry,

     }  }
  )
  begin
    intros, dsimp,

  end
  )
  _)
  _)
  _

end category_theory
