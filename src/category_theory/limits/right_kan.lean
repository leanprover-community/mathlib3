/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.punit
import category_theory.comma
import category_theory.limits.functor_category
import category_theory.limits.shapes.terminal

namespace category_theory
noncomputable theory

open category limits

universes v u₁ u₂ u₃
variables {C : Type v} {C' : Type u₂} {D : Type u₃}
variables [category.{v} C] [category.{v} C'] [category.{v} D]

section Ran

abbreviation Ran_index (p : C ⥤ C') (c' : C') := comma (functor.from_punit c') p

abbreviation Ran_index_map (p : C ⥤ C') {c' c'' : C'} (f : c'' ⟶ c') :
  Ran_index p c' ⥤ Ran_index p c'' := comma.map_left _ ((functor.const _).map f)

@[simp]
lemma Ran_index_map_id (p : C ⥤ C') {c' : C'} (j : Ran_index p c') :
  (Ran_index_map p (𝟙 c')).obj j = j :=
begin
  cases j,
  delta Ran_index_map comma.map_left,
  tidy,
end

@[simp]
lemma Ran_index_map_comp_apply (p : C ⥤ C') {c' c'' c''' : C'} (f : c''' ⟶ c'') (g : c'' ⟶ c')
  (j : Ran_index p c') :
  (Ran_index_map p (f ≫ g)).obj j = (Ran_index_map p f).obj ((Ran_index_map p g).obj j) :=
begin
  cases j,
  delta Ran_index_map comma.map_left,
  tidy,
end

abbreviation Ran_diagram (p : C ⥤ C') (F : C ⥤ D) (c' : C') : Ran_index p c' ⥤ D :=
  comma.snd (functor.from_punit c') p ⋙ F

def right_kan_obj (p : C ⥤ C') (F : C ⥤ D)
  [∀ X, has_limits_of_shape (Ran_index p X) D] :
  C' ⥤ D :=
{ obj := λ c', limit (Ran_diagram p F c'),
  map := λ X Y f, limit.pre (Ran_diagram _ _ _) (Ran_index_map _ f),
  map_id' := begin
    intro X,
    ext j,
    simp only [limit.pre_π, id_comp],
    congr' 1,
    simp,
  end,
  map_comp' := begin
    intros X Y Z f g,
    ext j,
    erw [limit.pre_pre, limit.pre_π, limit.pre_π],
    congr' 1,
    simp,
  end }

end Ran

@[simps]
def left_kan_obj (p : C ⥤ C') (F : C ⥤ D)
  [∀ X, has_colimits_of_shape (comma p (functor.from_punit X)) D] :
  C' ⥤ D :=
{ obj := λ c', colimit (comma.fst p (functor.from_punit c') ⋙ F),
  map := λ X Y f,
    colimit.pre
      (comma.fst p (functor.from_punit Y) ⋙ F)
      (comma.map_right _ ((functor.const _).map f)),
  map_id' := λ X,
  begin
    rw functor.map_id,
    symmetry,
    refine (colimit.is_colimit (comma.map_right p _ ⋙ comma.fst p _ ⋙ F)).uniq
                (cocone.whisker _ _) _ _,
    rintro ⟨Y, ⟨⟩, g⟩,
    dsimp [comma.map_right],
    convert comp_id _ using 2,
    simp,
  end,
  map_comp' := λ X Y Z f g,
  begin
    ext j,
    rw colimit.ι_pre,
    change _ = colimit.ι (comma.map_right p ((functor.const (discrete punit)).map f) ⋙
                            comma.fst p (functor.from_punit Y) ⋙ F) j ≫ _ ≫ _,
    rw colimit.ι_pre_assoc,
    change _ = colimit.ι (comma.map_right p ((functor.const (discrete punit)).map g) ⋙
                            comma.fst p (functor.from_punit Z) ⋙ F)
                         ((comma.map_right p ((functor.const (discrete punit)).map f)).obj j) ≫ _,
    rw [colimit.ι_pre, functor.map_comp],
    dsimp only [comma.map_right, functor.const.map_app, nat_trans.comp_app],
    rw assoc,
  end }

def left_kan_equiv (p : C ⥤ C') [∀ X, has_colimits_of_shape (comma p (functor.from_punit X)) D]
  (F : C ⥤ D) (G : C' ⥤ D) :
  (left_kan_obj p F ⟶ G) ≃ (F ⟶ ((whiskering_left _ _ _).obj p).obj G) :=
{ to_fun := λ f,
  { app := λ X, begin
        refine _ ≫ f.app _,
        refine colimit.ι (comma.fst p (functor.from_punit (p.obj X)) ⋙ F) ⟨X, ⟨⟩, 𝟙 _⟩,
      end,
    naturality' := λ X Y g,
    begin
      dsimp only [whiskering_left_obj_obj, functor.comp_map],
      rw [assoc, ← f.naturality (p.map g), left_kan_obj_map],
      have := colimit.ι_pre
                (comma.fst p (functor.from_punit (p.obj Y)) ⋙ F)
                (comma.map_right p ((functor.const (discrete punit)).map (p.map g)))
                ⟨X, punit.star, 𝟙 _⟩,
      erw reassoc_of this,
      clear this,
      rw ← assoc,
      congr' 1,
      apply colimit.w (comma.fst p (functor.from_punit (p.obj Y)) ⋙ F)
              (⟨g, _, _⟩ : comma_morphism ⟨_, _, _⟩ ⟨_, _, _⟩),
      { apply 𝟙 _ },
      apply_auto_param,
    end },
  inv_fun := λ f,
  { app := λ j,
    begin
      apply colimit.desc _ ⟨_, _⟩,
      apply whisker_left _ f ≫ _,
      refine ⟨λ X, G.map X.hom, _⟩,
      intros X Y g,
      dsimp only [whiskering_left_obj_obj, functor.comp_map, functor.const.obj_map, comma.fst_map],
      rw [← G.map_comp, g.w],
      dsimp,
      simp,
    end,
    naturality' := λ j₁ j₂ α,
    begin
      dsimp only [left_kan_obj_map],
      rw colimit.pre_desc,
      ext k,
      rw colimit.ι_desc,
      erw colimit.ι_desc_assoc,
      dsimp,
      simp,
    end },
  left_inv := λ f,
  begin
    ext,
    dsimp only,
    rw colimit.ι_desc,
    dsimp only [nat_trans.comp_app, whisker_left_app, comma.fst_obj, comma.fst_map],
    rw [assoc],
    rw ← f.naturality j.hom,
    rw ← assoc,
    congr' 1,
    dsimp only [left_kan_obj_map, functor.const.obj_obj],
    change colimit.ι (comma.map_right p ((functor.const (discrete punit)).map j.hom) ⋙
                      comma.fst p (functor.from_punit x) ⋙ F) _ ≫ _ = _,
    rw colimit.ι_pre,
    congr' 1,
    cases j,
    dsimp [comma.map_right],
    simp,
  end,
  right_inv := λ f,
  begin
    ext,
    dsimp only [],
    rw colimit.ι_desc,
    dsimp,
    simp,
  end }

def left_kan (p : C ⥤ C') [∀ X, has_colimits_of_shape (comma p (functor.from_punit X)) D] :
  (C ⥤ D) ⥤ (C' ⥤ D) :=
begin
  refine adjunction.left_adjoint_of_equiv (left_kan_equiv p) _,
  intros F G G' f g,
  ext,
  dsimp [left_kan_equiv],
  rw [assoc],
end

variable (D)
def left_kan_adjunction (p : C ⥤ C')
  [∀ X, has_colimits_of_shape (comma p (functor.from_punit X)) D] :
  left_kan p ⊣ (whiskering_left _ _ D).obj p :=
adjunction.adjunction_of_equiv_left _ _

@[simps]
def comma.terminal (p : C ⥤ C') (X : C) : comma p (functor.from_punit (p.obj X)) :=
⟨_, punit.star, 𝟙 _⟩

/--
Show that `elements.initial A` is initial in the category of elements for the `yoneda` functor.
-/
def is_terminal (p : C ⥤ C') (X : C) [full p] [faithful p] : is_terminal (comma.terminal p X) :=
{ lift := λ s,
  begin
    refine ⟨p.preimage s.X.hom, eq_to_hom (by simp), _⟩,
    dsimp,
    simp,
  end,
  uniq' := λ s m w,
  begin
    have := m.w,
    ext,
    dsimp,
    apply p.map_injective,
    dsimp [comma.terminal] at this,
    simp,
    rw comp_id at this,
    rw this,
    simp,
  end }

lemma thingy2 {J : Type v} [small_category J] {C : Type u₁} [category.{v} C]
  {F : J ⥤ C} [has_colimit F] {c₁ c₂ : cocone F} (t₁ : is_colimit c₁) (t₂ : is_colimit c₂) :
  is_iso (t₁.desc c₂) :=
begin
  letI : is_iso (t₁.desc_cocone_morphism c₂) := is_colimit.hom_is_iso t₁ t₂ _,
  apply category_theory.functor.map_is_iso (cocones.forget F) (t₁.desc_cocone_morphism c₂),
end

lemma coreflective (p : C ⥤ C') [∀ (X : C'), has_colimits_of_shape (comma p (functor.from_punit X)) D]
  [full p] [faithful p] : is_iso (left_kan_adjunction D p).unit :=
begin
  apply nat_iso.is_iso_of_is_iso_app _,
  intro F,
  apply nat_iso.is_iso_of_is_iso_app _,
  intro Y,
  dsimp [left_kan_adjunction, left_kan_equiv],
  rw comp_id,
  exact thingy2 (colimit_of_diagram_terminal (is_terminal p Y) _) (colimit.is_colimit _),
end

end category_theory
