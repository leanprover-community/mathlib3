/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.presheaf

/-!
# Presheafed spaces

Introduces the category of topological spaces equipped with a presheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

universes v u

open category_theory
open Top
open topological_space
open opposite
open category_theory.category category_theory.functor

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

local attribute [tidy] tactic.op_induction'

namespace algebraic_geometry

/-- A `PresheafedSpace C` is a topological space equipped with a presheaf of `C`s. -/
structure PresheafedSpace :=
(to_Top : Top)
(𝒪 : to_Top.presheaf C)

variables {C}

namespace PresheafedSpace

instance coe_to_Top : has_coe (PresheafedSpace C) Top :=
{ coe := λ X, X.to_Top }

@[simp] lemma as_coe (X : PresheafedSpace C) : X.to_Top = (X : Top.{v}) := rfl
@[simp] lemma mk_coe (to_Top) (𝒪) : (({ to_Top := to_Top, 𝒪 := 𝒪 } :
  PresheafedSpace.{v} C) : Top.{v}) = to_Top := rfl

instance (X : PresheafedSpace.{v} C) : topological_space X := X.to_Top.str

/-- A morphism between presheafed spaces `X` and `Y` consists of a continuous map
    `f` between the underlying topological spaces, and a (notice contravariant!) map
    from the presheaf on `Y` to the pushforward of the presheaf on `X` via `f`. -/
structure hom (X Y : PresheafedSpace C) :=
(f : (X : Top.{v}) ⟶ (Y : Top.{v}))
(c : Y.𝒪 ⟶ f _* X.𝒪)

@[ext] lemma ext {X Y : PresheafedSpace C} (α β : hom X Y)
  (w : α.f = β.f) (h : α.c ≫ (whisker_right (nat_trans.op (opens.map_iso _ _ w).inv) X.𝒪) = β.c) :
  α = β :=
begin
  cases α, cases β,
  dsimp [presheaf.pushforward] at *,
  tidy, -- TODO including `injections` would make tidy work earlier.
end
.

def id (X : PresheafedSpace C) : hom X X :=
{ f := 𝟙 (X : Top.{v}),
  c := ((functor.left_unitor _).inv) ≫ (whisker_right (nat_trans.op (opens.map_id (X.to_Top)).hom) _) }

def comp (X Y Z : PresheafedSpace C) (α : hom X Y) (β : hom Y Z) : hom X Z :=
{ f := α.f ≫ β.f,
  c := β.c ≫ (whisker_left (opens.map β.f).op α.c) ≫ (Top.presheaf.pushforward.comp _ _ _).inv }

variables (C)

section
local attribute [simp] id comp presheaf.pushforward

/- The proofs below can be done by `tidy`, but it is too slow,
   and we don't have a tactic caching mechanism. -/
/-- The category of PresheafedSpaces. Morphisms are pairs, a continuous map and a presheaf map
    from the presheaf on the target to the pushforward of the presheaf on the source. -/
instance category_of_PresheafedSpaces : category (PresheafedSpace C) :=
{ hom := hom,
  id := id,
  comp := comp,
  id_comp' := λ X Y f,
  begin
    ext1, swap,
    { dsimp, simp only [id_comp] },
    { ext U, op_induction, cases U,
      dsimp,
      simp only [comp_id, id_comp, map_id, presheaf.pushforward, presheaf.pushforward.comp_inv_app],
      dsimp,
      simp only [comp_id], },
  end,
  comp_id' := λ X Y f,
  begin
    ext1, swap,
    { dsimp, simp only [comp_id] },
    { ext U, op_induction, cases U,
      dsimp,
      simp only [comp_id, id_comp, map_id, presheaf.pushforward, presheaf.pushforward.comp_inv_app],
      dsimp,
      simp only [comp_id], }
  end,
  assoc' := λ W X Y Z f g h,
  begin
     ext1, swap,
     refl,
     { ext U, op_induction, cases U,
       dsimp,
       simp only [assoc, map_id, comp_id, presheaf.pushforward, presheaf.pushforward.comp_inv_app],
       dsimp,
       simp only [comp_id, id_comp], }
  end }

end

variables {C}

instance {X Y : PresheafedSpace C} : has_coe (X ⟶ Y) ((X : Top.{v}) ⟶ (Y : Top.{v})) :=
{ coe := λ α, α.f }

-- see Note [function coercion]
instance {X Y : PresheafedSpace C} : has_coe_to_fun (X ⟶ Y) :=
⟨λ _, (X : Top.{v}) → (Y : Top.{v}), λ h, h⟩

@[simp] lemma hom_mk_coe {X Y : PresheafedSpace C} (f) (c) :
  (({ f := f, c := c } : X ⟶ Y) : (X : Top.{v}) ⟶ (Y : Top.{v})) = f := rfl
@[simp] lemma f_as_coe {X Y : PresheafedSpace C} (α : X ⟶ Y) :
  α.f = (α : (X : Top.{v}) ⟶ (Y : Top.{v})) := rfl
@[simp] lemma id_coe (X : PresheafedSpace C) :
  (((𝟙 X) : X ⟶ X) : (X : Top.{v}) ⟶ X) = 𝟙 (X : Top.{v}) := rfl
@[simp] lemma id_coe_fn (X : PresheafedSpace C) :
  (((𝟙 X) : X ⟶ X) : (X : Top.{v}) → X) = 𝟙 (X : Top.{v}) := rfl
@[simp] lemma comp_coe {X Y Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) :
  ((α ≫ β : X ⟶ Z) : (X : Top.{v}) ⟶ Z) = (α : (X : Top.{v}) ⟶ Y) ≫ (β : Y ⟶ Z) := rfl

lemma id_c (X : PresheafedSpace C) :
  ((𝟙 X) : X ⟶ X).c =
  (((functor.left_unitor _).inv) ≫ (whisker_right (nat_trans.op (opens.map_id (X.to_Top)).hom) _)) := rfl

-- Implementation note: this harmless looking lemma causes deterministic timeouts,
-- but happily we can survive without it.
-- lemma comp_c {X Y Z : PresheafedSpace.{v} C} (α : X ⟶ Y) (β : Y ⟶ Z) :
--   (α ≫ β).c = (β.c ≫ (whisker_left (opens.map β.f).op α.c)) := rfl

@[simp] lemma id_c_app (X : PresheafedSpace C) (U) :
  ((𝟙 X) : X ⟶ X).c.app U = eq_to_hom (by { op_induction U, cases U, refl }) :=
by { op_induction U, cases U, simp only [id_c], dsimp, simp, }

@[simp] lemma comp_c_app {X Y Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
  (α ≫ β).c.app U = (β.c).app U ≫ (α.c).app (op ((opens.map (β.f)).obj (unop U))) ≫
    (Top.presheaf.pushforward.comp _ _ _).inv.app U := rfl

/-- The forgetful functor from `PresheafedSpace` to `Top`. -/
def forget : PresheafedSpace C ⥤ Top :=
{ obj := λ X, (X : Top.{v}),
  map := λ X Y f, f }

end PresheafedSpace

end algebraic_geometry

open algebraic_geometry algebraic_geometry.PresheafedSpace

variables {C}

namespace category_theory

variables {D : Type u} [category.{v} D]

local attribute [simp] presheaf.pushforward

namespace functor

/-- We can apply a functor `F : C ⥤ D` to the values of the presheaf in any `PresheafedSpace C`,
    giving a functor `PresheafedSpace C ⥤ PresheafedSpace D` -/
/- The proofs below can be done by `tidy`, but it is too slow,
   and we don't have a tactic caching mechanism. -/
def map_presheaf (F : C ⥤ D) : PresheafedSpace C ⥤ PresheafedSpace D :=
{ obj := λ X, { to_Top := X.to_Top, 𝒪 := X.𝒪 ⋙ F },
  map := λ X Y f, { f := f.f, c := whisker_right f.c F },
  map_id' := λ X,
  begin
    ext1, swap,
    { refl },
    { ext,
      dsimp,
      simp only [presheaf.pushforward, eq_to_hom_map, map_id, comp_id, id_c_app],
      refl }
  end,
  map_comp' := λ X Y Z f g,
  begin
    ext1, swap,
    { refl, },
    { ext, dsimp,
      simp only [comp_id, assoc, map_comp, map_id, comp_c_app,
        presheaf.pushforward, presheaf.pushforward.comp_inv_app],
      dsimp,
      simp only [comp_id, map_id] }
  end }

@[simp] lemma map_presheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace C) :
  ((F.map_presheaf.obj X) : Top.{v}) = (X : Top.{v}) := rfl
@[simp] lemma map_presheaf_obj_𝒪 (F : C ⥤ D) (X : PresheafedSpace C) :
  (F.map_presheaf.obj X).𝒪 = X.𝒪 ⋙ F := rfl
@[simp] lemma map_presheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) :
  ((F.map_presheaf.map f) : (F.map_presheaf.obj X : Top.{v}) ⟶ (F.map_presheaf.obj Y : Top.{v})) =
    (f : (X : Top.{v}) ⟶ (Y : Top.{v})) := rfl
@[simp] lemma map_presheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).c = whisker_right f.c F := rfl

end functor

namespace nat_trans

/- The proofs below can be done by `tidy`, but it is too slow,
   and we don't have a tactic caching mechanism. -/
def on_presheaf {F G : C ⥤ D} (α : F ⟶ G) : G.map_presheaf ⟶ F.map_presheaf :=
{ app := λ X,
  { f := 𝟙 _,
    c := whisker_left X.𝒪 α ≫ ((functor.left_unitor _).inv) ≫
           (whisker_right (nat_trans.op (opens.map_id X.to_Top).hom) _) },
  naturality' := λ X Y f,
  begin
    ext1, swap,
    { refl },
    { ext U,
      op_induction,
      cases U,
      dsimp,
      simp only [comp_id, assoc, map_id, presheaf.pushforward, presheaf.pushforward.comp_inv_app],
      dsimp,
      simp only [comp_id, nat_trans.naturality], }
  end }

-- TODO Assemble the last two constructions into a functor
--   `(C ⥤ D) ⥤ (PresheafedSpace C ⥤ PresheafedSpace D)`
end nat_trans

end category_theory
