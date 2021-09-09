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

variables (C : Type u) [category.{v} C]

local attribute [tidy] tactic.op_induction'

namespace algebraic_geometry

/-- A `PresheafedSpace C` is a topological space equipped with a presheaf of `C`s. -/
structure PresheafedSpace :=
(carrier : Top)
(presheaf : carrier.presheaf C)

variables {C}

namespace PresheafedSpace

attribute [protected] presheaf

instance coe_carrier : has_coe (PresheafedSpace C) Top :=
{ coe := λ X, X.carrier }

@[simp] lemma as_coe (X : PresheafedSpace C) : X.carrier = (X : Top.{v}) := rfl
@[simp] lemma mk_coe (carrier) (presheaf) : (({ carrier := carrier, presheaf := presheaf } :
  PresheafedSpace.{v} C) : Top.{v}) = carrier := rfl

instance (X : PresheafedSpace.{v} C) : topological_space X := X.carrier.str

/-- The constant presheaf on `X` with value `Z`. -/
def const (X : Top) (Z : C) : PresheafedSpace C :=
{ carrier := X,
  presheaf :=
  { obj := λ U, Z,
    map := λ U V f, 𝟙 Z, } }

instance [inhabited C] : inhabited (PresheafedSpace C) := ⟨const (Top.of pempty) (default C)⟩

/-- A morphism between presheafed spaces `X` and `Y` consists of a continuous map
    `f` between the underlying topological spaces, and a (notice contravariant!) map
    from the presheaf on `Y` to the pushforward of the presheaf on `X` via `f`. -/
structure hom (X Y : PresheafedSpace C) :=
(base : (X : Top.{v}) ⟶ (Y : Top.{v}))
(c : Y.presheaf ⟶ base _* X.presheaf)

@[ext] lemma ext {X Y : PresheafedSpace C} (α β : hom X Y)
  (w : α.base = β.base)
  (h : α.c ≫ (whisker_right (nat_trans.op (opens.map_iso _ _ w).inv) X.presheaf) = β.c) :
  α = β :=
begin
  cases α, cases β,
  dsimp [presheaf.pushforward_obj] at *,
  tidy, -- TODO including `injections` would make tidy work earlier.
end
.

/-- The identity morphism of a `PresheafedSpace`. -/
def id (X : PresheafedSpace C) : hom X X :=
{ base := 𝟙 (X : Top.{v}),
  c := (functor.left_unitor _).inv ≫ whisker_right (nat_trans.op (opens.map_id X.carrier).hom) _ }

instance hom_inhabited (X : PresheafedSpace C) : inhabited (hom X X) := ⟨id X⟩

/-- Composition of morphisms of `PresheafedSpace`s. -/
def comp {X Y Z : PresheafedSpace C} (α : hom X Y) (β : hom Y Z) : hom X Z :=
{ base := α.base ≫ β.base,
  c := β.c ≫ (whisker_left (opens.map β.base).op α.c) ≫ (Top.presheaf.pushforward.comp _ _ _).inv }

variables (C)

section
local attribute [simp] id comp

/- The proofs below can be done by `tidy`, but it is too slow,
   and we don't have a tactic caching mechanism. -/
/-- The category of PresheafedSpaces. Morphisms are pairs, a continuous map and a presheaf map
    from the presheaf on the target to the pushforward of the presheaf on the source. -/
instance category_of_PresheafedSpaces : category (PresheafedSpace C) :=
{ hom := hom,
  id := id,
  comp := λ X Y Z f g, comp f g,
  id_comp' := λ X Y f,
  begin
    ext1, swap,
    { dsimp, simp only [id_comp] },  -- See note [dsimp, simp].
    { ext U, op_induction, cases U,
      dsimp,
      simp only [presheaf.pushforward.comp_inv_app, opens.map_iso_inv_app],
      dsimp,
      simp only [comp_id, comp_id, map_id], },
  end,
  comp_id' := λ X Y f,
  begin
    ext1, swap,
    { dsimp, simp only [comp_id] },
    { ext U, op_induction, cases U,
      dsimp,
      simp only [presheaf.pushforward.comp_inv_app, opens.map_iso_inv_app],
      dsimp,
      simp only [id_comp, comp_id, map_id], }
  end,
  assoc' := λ W X Y Z f g h,
  begin
     ext1, swap,
     refl,
     { ext U, op_induction, cases U,
       dsimp,
       simp only [assoc, presheaf.pushforward.comp_inv_app, opens.map_iso_inv_app],
       dsimp,
       simp only [comp_id, id_comp, map_id], }
  end }

end

variables {C}

@[simp] lemma id_base (X : PresheafedSpace C) :
  ((𝟙 X) : X ⟶ X).base = (𝟙 (X : Top.{v})) := rfl

lemma id_c (X : PresheafedSpace C) :
  ((𝟙 X) : X ⟶ X).c =
  (functor.left_unitor _).inv ≫ whisker_right (nat_trans.op (opens.map_id X.carrier).hom) _ := rfl

@[simp] lemma id_c_app (X : PresheafedSpace C) (U) :
  ((𝟙 X) : X ⟶ X).c.app U = eq_to_hom (by { op_induction U, cases U, refl }) :=
by { op_induction U, cases U, simp only [id_c], dsimp, simp, }

@[simp] lemma comp_base {X Y Z : PresheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).base = f.base ≫ g.base := rfl

@[simp] lemma comp_c_app {X Y Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
  (α ≫ β).c.app U = (β.c).app U ≫ (α.c).app (op ((opens.map (β.base)).obj (unop U))) ≫
    (Top.presheaf.pushforward.comp _ _ _).inv.app U := rfl

lemma congr_app {X Y : PresheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) :
  α.c.app U = β.c.app U ≫ X.presheaf.map (eq_to_hom (by subst h)) :=
by { subst h, dsimp, simp, }

section
variables (C)

/-- The forgetful functor from `PresheafedSpace` to `Top`. -/
@[simps]
def forget : PresheafedSpace C ⥤ Top :=
{ obj := λ X, (X : Top.{v}),
  map := λ X Y f, f.base }

end

/--
The restriction of a presheafed space along an open embedding into the space.
-/
@[simps]
def restrict {U : Top} (X : PresheafedSpace C)
  (f : U ⟶ (X : Top.{v})) (h : open_embedding f) : PresheafedSpace C :=
{ carrier := U,
  presheaf := h.is_open_map.functor.op ⋙ X.presheaf }

/--
The map from the restriction of a presheafed space.
-/
def of_restrict {U : Top} (X : PresheafedSpace C)
  (f : U ⟶ (X : Top.{v})) (h : open_embedding f) :
  X.restrict f h ⟶ X :=
{ base := f,
  c := { app := λ V, X.presheaf.map $
      ((h.is_open_map.adjunction.hom_equiv _ _).symm (𝟙 $ (opens.map f).obj $ unop V)).op,
    naturality':= λ U V f, show _ = _ ≫ X.presheaf.map _,
      by { rw [← map_comp, ← map_comp], refl } } }

/--
The map to the restriction of a presheafed space along the canonical inclusion from the top
subspace.
-/
@[simps]
def to_restrict_top (X : PresheafedSpace C) :
  X ⟶ X.restrict (opens.inclusion ⊤) (opens.open_embedding ⊤) :=
{ base := ⟨λ x, ⟨x, trivial⟩, continuous_def.2 $ λ U ⟨S, hS, hSU⟩, hSU ▸ hS⟩,
  c := { app := λ U, X.presheaf.map $ (hom_of_le $ λ x hxU, ⟨⟨x, trivial⟩, hxU, rfl⟩ :
      (opens.map (⟨λ x, ⟨x, trivial⟩, continuous_def.2 $ λ U ⟨S, hS, hSU⟩, hSU ▸ hS⟩ :
          X.1 ⟶ (opens.to_Top X.1).obj ⊤)).obj (unop U) ⟶
        (opens.open_embedding ⊤).is_open_map.functor.obj (unop U)).op,
    naturality':= λ U V f, show X.presheaf.map _ ≫ _ = _ ≫ X.presheaf.map _,
      by { rw [← map_comp, ← map_comp], refl } } }

/--
The isomorphism from the restriction to the top subspace.
-/
@[simps]
def restrict_top_iso (X : PresheafedSpace C) :
  X.restrict (opens.inclusion ⊤) (opens.open_embedding ⊤) ≅ X :=
{ hom := X.of_restrict _ _,
  inv := X.to_restrict_top,
  hom_inv_id' := ext _ _ (concrete_category.hom_ext _ _ $ λ ⟨x, _⟩, rfl) $
    nat_trans.ext _ _ $ funext $ λ U, by { op_induction U,
      dsimp only [nat_trans.comp_app, comp_c_app, to_restrict_top, of_restrict,
          whisker_right_app, comp_base, nat_trans.op_app, opens.map_iso_inv_app],
      erw [presheaf.pushforward.comp_inv_app, comp_id, ← X.presheaf.map_comp,
          ← X.presheaf.map_comp, id_c_app],
      exact X.presheaf.map_id _ },
  inv_hom_id' := ext _ _ rfl $ nat_trans.ext _ _ $ funext $ λ U, by { op_induction U,
    dsimp only [nat_trans.comp_app, comp_c_app, of_restrict, to_restrict_top,
        whisker_right_app, comp_base, nat_trans.op_app, opens.map_iso_inv_app],
    erw [← X.presheaf.map_comp, ← X.presheaf.map_comp, ← X.presheaf.map_comp, id_c_app],
    convert eq_to_hom_map X.presheaf _,
    erw [op_obj, id_base, opens.map_id_obj], refl } }

/--
The global sections, notated Gamma.
-/
@[simps]
def Γ : (PresheafedSpace C)ᵒᵖ ⥤ C :=
{ obj := λ X, (unop X).presheaf.obj (op ⊤),
  map := λ X Y f, f.unop.c.app (op ⊤) ≫ (unop Y).presheaf.map (opens.le_map_top _ _).op,
  map_id' := λ X, begin
    op_induction X,
    erw [unop_id_op, id_c_app, eq_to_hom_refl, id_comp],
    exact X.presheaf.map_id _
  end,
  map_comp' := λ X Y Z f g, begin
    rw [unop_comp, comp_c_app],
    simp_rw category.assoc,
    erw [nat_trans.naturality_assoc, presheaf.pushforward.comp_inv_app, id_comp,
        category_theory.functor.comp_map, ← map_comp],
    refl
  end }

lemma Γ_obj_op (X : PresheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) := rfl

lemma Γ_map_op {X Y : PresheafedSpace C} (f : X ⟶ Y) :
  Γ.map f.op = f.c.app (op ⊤) ≫ X.presheaf.map (opens.le_map_top _ _).op := rfl

end PresheafedSpace

end algebraic_geometry

open algebraic_geometry algebraic_geometry.PresheafedSpace

variables {C}

namespace category_theory

variables {D : Type u} [category.{v} D]

local attribute [simp] presheaf.pushforward_obj

namespace functor

/-- We can apply a functor `F : C ⥤ D` to the values of the presheaf in any `PresheafedSpace C`,
    giving a functor `PresheafedSpace C ⥤ PresheafedSpace D` -/
def map_presheaf (F : C ⥤ D) : PresheafedSpace C ⥤ PresheafedSpace D :=
{ obj := λ X, { carrier := X.carrier, presheaf := X.presheaf ⋙ F },
  map := λ X Y f, { base := f.base, c := whisker_right f.c F }, }

@[simp] lemma map_presheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace C) :
  ((F.map_presheaf.obj X) : Top.{v}) = (X : Top.{v}) := rfl
@[simp] lemma map_presheaf_obj_presheaf (F : C ⥤ D) (X : PresheafedSpace C) :
  (F.map_presheaf.obj X).presheaf = X.presheaf ⋙ F := rfl
@[simp] lemma map_presheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).base = f.base := rfl
@[simp] lemma map_presheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).c = whisker_right f.c F := rfl

end functor

namespace nat_trans

/--
A natural transformation induces a natural transformation between the `map_presheaf` functors.
-/
def on_presheaf {F G : C ⥤ D} (α : F ⟶ G) : G.map_presheaf ⟶ F.map_presheaf :=
{ app := λ X,
  { base := 𝟙 _,
    c := whisker_left X.presheaf α ≫ (functor.left_unitor _).inv ≫
           whisker_right (nat_trans.op (opens.map_id X.carrier).hom) _ }, }

-- TODO Assemble the last two constructions into a functor
--   `(C ⥤ D) ⥤ (PresheafedSpace C ⥤ PresheafedSpace D)`
end nat_trans

end category_theory
