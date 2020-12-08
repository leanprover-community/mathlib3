/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.punit
import category_theory.limits.functor_category

namespace category_theory
noncomputable theory

open category limits

universes v u₁ u₂ u₃
variables {C : Type v} {C' : Type u₂} {D : Type u₃}
variables [category.{v} C] [category.{v} C'] [category.{v} D]

@[simps]
def left_kan_obj (p : C ⥤ C') (F : C ⥤ D) [has_colimits D] :
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
    dsimp only [cocone.whisker_ι, whisker_left_app, colimit.cocone_ι, comma.map_right],
    convert comp_id _,
    apply comp_id,
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

def left_kan_equiv [has_colimits D] (p : C ⥤ C') (F : C ⥤ D) (G : C' ⥤ D) :
  (left_kan_obj p F ⟶ G) ≃ (F ⟶ ((whiskering_left _ _ _).obj p).obj G) :=
{ to_fun := λ f,
  { app := λ X,
      by apply colimit.ι (comma.fst p (functor.from_punit (p.obj X)) ⋙ F) ⟨X, ⟨⟩, 𝟙 _⟩ ≫ f.app _,
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

def left_kan [has_colimits D] (p : C ⥤ C') : (C ⥤ D) ⥤ (C' ⥤ D) :=
begin
  refine adjunction.left_adjoint_of_equiv (left_kan_equiv p) _,
  intros F G G' f g,
  ext,
  dsimp [left_kan_equiv],
  rw [assoc],
end

def left_kan_adjunction [has_colimits D] (p : C ⥤ C') :
  left_kan p ⊣ (whiskering_left _ _ D).obj p :=
adjunction.adjunction_of_equiv_left _ _

@[simps]
def comma.terminal (p : C ⥤ C') (X : _) : comma p (functor.from_punit (p.obj X)) :=
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

def reflective [has_colimits D] (p : C ⥤ C') [full p] [faithful p] :
  left_kan p ⋙ (whiskering_left _ _ _).obj p ≅ 𝟭 (C ⥤ D) :=
begin
  refine nat_iso.of_components _ _,
  intro A,
  { refine nat_iso.of_components _ _,
    { intro X,
      apply (colimit.is_colimit _).cocone_point_unique_up_to_iso
                (colimit_of_diagram_terminal (is_terminal p _) _) },
    { intros X Y f,
      ext1,
      change colimit.ι (comma.map_right p _ ⋙ comma.fst p _ ⋙ A) _ ≫ colimit.pre _ _ ≫ _ = _,
      rw colimit.ι_pre_assoc,
      simp only [cocone_of_diagram_terminal_ι_app, colimit.comp_cocone_point_unique_up_to_iso_hom,
                functor.comp_map, colimit.comp_cocone_point_unique_up_to_iso_hom_assoc,
                comma.fst_map],
      dsimp only [functor.id_obj],
      rw ← A.map_comp,
      cases j,
      congr' 1,
      dsimp [comma.map_right, is_terminal, is_terminal.from],
      simp } },
  { intros A A' α,
    ext,
    dsimp [left_kan, adjunction.left_adjoint_of_equiv, left_kan_equiv],
    rw colimit.ι_desc_assoc,
    dsimp,
    rw assoc,
    rw comp_id,
    rw assoc,

    -- change α.app _ ≫ colimit.ι (comma.map_right p _ ⋙ (comma.fst p (functor.from_punit (p.obj x)) ⋙ A')) _ ≫ colimit.pre (comma.fst p (functor.from_punit (p.obj x)) ⋙ A') (comma.map_right p ((functor.const (discrete punit)).map j.hom)) ≫ _ = _,

  }

end

-- def reflective [has_colimits D] (p : C ⥤ C') [full p] [faithful p] (A : C ⥤ D) :
--   p ⋙ (left_kan p).obj A ≅ A :=
-- begin
--   refine nat_iso.of_components _ _,
--   intro X,
--   apply (colimit.is_colimit _).cocone_point_unique_up_to_iso
--             (colimit_of_diagram_terminal (is_terminal p _) _),
--   intros X Y f,
--   ext1,
--   change colimit.ι (comma.map_right p _ ⋙ comma.fst p _ ⋙ A) _ ≫ colimit.pre _ _ ≫ _ = _,
--   rw colimit.ι_pre_assoc,
--   simp only [cocone_of_diagram_terminal_ι_app, colimit.comp_cocone_point_unique_up_to_iso_hom,
--              functor.comp_map, colimit.comp_cocone_point_unique_up_to_iso_hom_assoc, comma.fst_map],
--   rw ← A.map_comp,
--   cases j,
--   congr' 1,
--   dsimp [comma.map_right, is_terminal, is_terminal.from],
--   simp,
-- end

end category_theory
