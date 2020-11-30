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
    colimit.pre (comma.fst p (functor.from_punit Y) ⋙ F) (comma.map_right _ ((functor.const _).map f)),
  map_id' := λ X,
  begin
    ext j,
    rw colimit.ι_pre,
    erw comp_id,
    congr' 1,
    cases j,
    simp [comma.map_right],
  end,
  map_comp' := λ X Y Z f g,
  begin
    ext j,
    rw colimit.ι_pre,
    change _ = colimit.ι (comma.map_right p ((functor.const (discrete punit)).map f) ⋙ comma.fst p (functor.from_punit Y) ⋙ F) j ≫ _ ≫ _,
    rw colimit.ι_pre_assoc,
    -- change _ = colimit.ι _
    change _ = colimit.ι (comma.fst p (functor.from_punit Y) ⋙ F) ((comma.map_right p ((functor.const (discrete punit)).map f)).obj j) ≫ _,
    change _ = colimit.ι ((comma.map_right p ((functor.const (discrete punit)).map g)) ⋙ comma.fst p (functor.from_punit Z) ⋙ F) ((comma.map_right p ((functor.const (discrete punit)).map f)).obj j) ≫ _,
    rw colimit.ι_pre,
    congr' 1,
    cases j,
    dsimp [comma.map_right],
    congr' 1,
    simp,
  end }

def left_kan_equiv [has_colimits D] (p : C ⥤ C') (F : C ⥤ D) (G : C' ⥤ D) :
  (left_kan_obj p F ⟶ G) ≃ (F ⟶ ((whiskering_left _ _ _).obj p).obj G) :=
{ to_fun := λ f,
  { app := λ X,
    begin
      apply _ ≫ f.app _,
      apply colimit.ι (comma.fst p (functor.from_punit (p.obj X)) ⋙ F) ⟨X, ⟨⟩, 𝟙 _⟩,
    end,
    naturality' := λ X Y g,
    begin
      dsimp,
      rw [assoc],
      rw ← f.naturality (p.map g),
      dsimp,
      have := colimit.ι_pre (comma.fst p (functor.from_punit (p.obj Y)) ⋙ F) (comma.map_right p ((functor.const (discrete punit)).map (p.map g))) ⟨X, punit.star, 𝟙 _⟩,
      dsimp at this,
      erw reassoc_of this,
      rw ← assoc,
      congr' 1,
      have q := colimit.w (comma.fst p (functor.from_punit (p.obj Y)) ⋙ F),
      dsimp at q,
      specialize q (⟨g, _, _⟩ : comma_morphism ⟨_, _, _⟩ ⟨_, _, _⟩),
      dsimp at q,
      apply q,
      obviously,
    end },
  inv_fun := λ f,
  { app := λ j,
    begin
      apply colimit.desc _ ⟨_, _⟩,
      apply whisker_left _ f ≫ _,
      refine ⟨_, _⟩,
      intro X,
      apply G.map X.hom,
      intros X Y g,
      dsimp,
      rw ← G.map_comp,
      rw g.w,
      rw comp_id,
      dsimp,
      rw comp_id,
    end,
    naturality' := λ j₁ j₂ α,
    begin
      dsimp,
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
    dsimp,
    rw colimit.ι_desc,
    dsimp,
    rw [assoc],
    rw ← f.naturality j.hom,
    rw ← assoc,
    congr' 1,
    dsimp,
    change colimit.ι (comma.map_right p ((functor.const (discrete punit)).map j.hom) ⋙ comma.fst p (functor.from_punit x) ⋙ F) _ ≫ _ = _,
    rw colimit.ι_pre,
    congr' 1,
    cases j,
    dsimp [comma.map_right],
    simp,
  end,
  right_inv := λ f,
  begin
    ext,
    dsimp,
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
    dsimp [comma.terminal],
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

def reflective [has_colimits D] (p : C ⥤ C') (A : C ⥤ D) :
  p ⋙ (left_kan p).obj A ≅ A :=
begin
  refine nat_iso.of_components _ _,
  intro X,
  dsimp [left_kan, adjunction.left_adjoint_of_equiv],

end

end category_theory
