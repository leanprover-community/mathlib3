-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import topology.Top.presheaf

universes v u

open category_theory
open Top
open topological_space
open opposite

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

local attribute [tidy] tactic.op_induction'

namespace algebraic_geometry

structure PresheafedSpace :=
(to_Top : Top.{v})
(𝒪 : to_Top.presheaf C)

variables {C}

namespace PresheafedSpace

instance coe_to_Top : has_coe (PresheafedSpace.{v} C) Top :=
{ coe := λ X, X.to_Top }

@[simp] lemma as_coe (X : PresheafedSpace.{v} C) : X.to_Top = (X : Top.{v}) := rfl
@[simp] lemma mk_coe (to_Top) (𝒪) : (({ to_Top := to_Top, 𝒪 := 𝒪 } :
  PresheafedSpace.{v} C) : Top.{v}) = to_Top := rfl

instance (X : PresheafedSpace.{v} C) : topological_space X := X.to_Top.str

structure hom (X Y : PresheafedSpace.{v} C) :=
(f : (X : Top.{v}) ⟶ (Y : Top.{v}))
(c : Y.𝒪 ⟶ f _* X.𝒪)

@[extensionality] lemma ext {X Y : PresheafedSpace.{v} C} (α β : hom X Y)
  (w : α.f = β.f) (h : α.c ≫ (whisker_right (nat_trans.op (opens.map_iso _ _ w).inv) X.𝒪) = β.c) :
  α = β :=
begin
  cases α, cases β,
  dsimp [presheaf.pushforward] at *,
  tidy, -- TODO including `injections` would make tidy work earlier.
end
.

def id (X : PresheafedSpace.{v} C) : hom X X :=
{ f := 𝟙 (X : Top.{v}),
  c := ((functor.left_unitor _).inv) ≫ (whisker_right (nat_trans.op (opens.map_id _).hom) _) }

def comp (X Y Z : PresheafedSpace.{v} C) (α : hom X Y) (β : hom Y Z) : hom X Z :=
{ f := α.f ≫ β.f,
  c := β.c ≫ (whisker_left (opens.map β.f).op α.c) }

variables (C)

section
local attribute [simp] id comp presheaf.pushforward

/- Ihis proof is filled in by the `tidy` hole command and modified for performance.
   It should not remain like this. -/
instance category_of_PresheafedSpaces : category (PresheafedSpace.{v} C) :=
{ hom := hom,
  id := id,
  comp := comp,
  id_comp' :=
  begin
    intros X Y f,
    dsimp at *,
    tactic.ext1 [] {new_goals := tactic.new_goals.all},
    work_on_goal 0 { simp only [category_theory.category.id_comp] },
    dsimp at *,
    ext1,
    dsimp at *,
    simp only [category.id_comp, category.assoc],
    tactic.op_induction',
    cases X_1,
    dsimp at *,
    simp only [category_theory.category.comp_id, category_theory.functor.map_id]
  end,
  comp_id' :=
  begin
    intros X Y f,
    dsimp at *,
    tactic.ext1 [] {new_goals := tactic.new_goals.all},
    work_on_goal 0 { simp only [category_theory.category.comp_id] },
    dsimp at *,
    ext1,
    dsimp at *,
    tactic.op_induction',
    cases X_1,
    dsimp at *,
    simp
  end,
  assoc' :=
  begin
    intros W X Y Z f g h,
    simp only [true_and, presheaf.pushforward, id, comp, whisker_left_twice, whisker_left_comp,
               heq_iff_eq, category.assoc],
    split; refl
  end }

end

variables {C}

instance {X Y : PresheafedSpace.{v} C} : has_coe (X ⟶ Y) (X.to_Top ⟶ Y.to_Top) :=
{ coe := λ α, α.f }

@[simp] lemma hom_mk_coe {X Y : PresheafedSpace.{v} C} (f) (c) :
  (({ f := f, c := c } : X ⟶ Y) : (X : Top.{v}) ⟶ (Y : Top.{v})) = f := rfl
@[simp] lemma f_as_coe {X Y : PresheafedSpace.{v} C} (α : X ⟶ Y) :
  α.f = (α : (X : Top.{v}) ⟶ (Y : Top.{v})) := rfl
@[simp] lemma id_coe (X : PresheafedSpace.{v} C) :
  (((𝟙 X) : X ⟶ X) : (X : Top.{v}) ⟶ X) = 𝟙 (X : Top.{v}) := rfl
@[simp] lemma comp_coe {X Y Z : PresheafedSpace.{v} C} (α : X ⟶ Y) (β : Y ⟶ Z) :
  ((α ≫ β : X ⟶ Z) : (X : Top.{v}) ⟶ Z) = (α : (X : Top.{v}) ⟶ Y) ≫ (β : Y ⟶ Z) := rfl

lemma id_c (X : PresheafedSpace.{v} C) :
  ((𝟙 X) : X ⟶ X).c =
  (((functor.left_unitor _).inv) ≫ (whisker_right (nat_trans.op (opens.map_id _).hom) _)) := rfl

lemma comp_c {X Y Z : PresheafedSpace.{v} C} (α : X ⟶ Y) (β : Y ⟶ Z) :
  (α ≫ β).c = (β.c ≫ (whisker_left (opens.map β.f).op α.c)) := rfl

@[simp] lemma id_c_app (X : PresheafedSpace.{v} C) (U) :
  ((𝟙 X) : X ⟶ X).c.app U = eq_to_hom (by tidy) :=
by { simp only [id_c], tidy }

@[simp] lemma comp_c_app {X Y Z : PresheafedSpace.{v} C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
  (α ≫ β).c.app U = (β.c).app U ≫ (α.c).app (op ((opens.map (β.f)).obj (unop U))) := rfl

def forget : PresheafedSpace.{v} C ⥤ Top :=
{ obj := λ X, (X : Top.{v}),
  map := λ X Y f, f }

end PresheafedSpace

end algebraic_geometry

open algebraic_geometry
variables {C}

namespace category_theory

variables {D : Type u} [𝒟 : category.{v+1} D]
include 𝒟

local attribute [simp] PresheafedSpace.id_c PresheafedSpace.comp_c presheaf.pushforward

namespace functor

/- Ihis proof is filled in by the `tidy` hole command and modified for performance.
   It should not remain like this. -/
def map_presheaf (F : C ⥤ D) : PresheafedSpace.{v} C ⥤ PresheafedSpace.{v} D :=
{ obj := λ X, { to_Top := X.to_Top, 𝒪 := X.𝒪 ⋙ F },
  map := λ X Y f, { f := f.f, c := whisker_right f.c F },
  map_id' :=
  begin
    intros X,
    dsimp at *,
    simp only [presheaf.pushforward, whisker_right_twice, whisker_right_comp],
    tactic.ext1 [] {new_goals := tactic.new_goals.all},
    work_on_goal 0 { refl },
    dsimp at *,
    ext1,
    dsimp at *,
    simp only [category_theory.category.comp_id, topological_space.opens.map_id_obj,
               category_theory.category.id_comp, category_theory.functor.map_id]
  end,
  map_comp' :=
  begin
    intros X Y Z f g,
    simp only [PresheafedSpace.comp_c, presheaf.pushforward, whisker_right_comp],
    refl
  end }

@[simp] lemma map_presheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace.{v} C) :
  ((F.map_presheaf.obj X) : Top.{v}) = (X : Top.{v}) := rfl
@[simp] lemma map_presheaf_obj_𝒪 (F : C ⥤ D) (X : PresheafedSpace.{v} C) :
  (F.map_presheaf.obj X).𝒪 = X.𝒪 ⋙ F := rfl
@[simp] lemma map_presheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) :
  ((F.map_presheaf.map f) : (X : Top.{v}) ⟶ (Y : Top.{v})) = f := rfl
@[simp] lemma map_presheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).c = whisker_right f.c F := rfl

end functor

namespace nat_trans

/- Ihis proof is filled in by the `tidy` hole command and modified for performance.
   It should not remain like this. -/
def on_presheaf {F G : C ⥤ D} (α : F ⟶ G) : G.map_presheaf ⟶ F.map_presheaf :=
{ app := λ X,
  { f := 𝟙 _,
    c := whisker_left X.𝒪 α ≫ ((functor.left_unitor _).inv) ≫
           (whisker_right (nat_trans.op (opens.map_id _).hom) _) },
  naturality' :=
  begin
    intros X Y f,
    dsimp at *,
    tactic.ext1 [] {new_goals := tactic.new_goals.all},
    work_on_goal 0 { refl },
    dsimp at *,
    ext1,
    dsimp at *,
    simp at *,
    tactic.op_induction',
    cases X_1,
    dsimp at *,
    simp at *
  end }


end nat_trans

end category_theory
