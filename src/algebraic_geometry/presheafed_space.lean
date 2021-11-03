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
  (h : α.c ≫ eq_to_hom (by rw w) = β.c) :
  α = β :=
begin
  cases α, cases β,
  dsimp [presheaf.pushforward_obj] at *,
  tidy, -- TODO including `injections` would make tidy work earlier.
end

lemma hext {X Y : PresheafedSpace C} (α β : hom X Y)
  (w : α.base = β.base)
  (h : α.c == β.c) :
  α = β :=
by { cases α, cases β, congr, exacts [w,h] }

.

/-- The identity morphism of a `PresheafedSpace`. -/
def id (X : PresheafedSpace C) : hom X X :=
{ base := 𝟙 (X : Top.{v}),
  c := eq_to_hom (presheaf.pushforward.id_eq X.presheaf).symm }

instance hom_inhabited (X : PresheafedSpace C) : inhabited (hom X X) := ⟨id X⟩

/-- Composition of morphisms of `PresheafedSpace`s. -/
def comp {X Y Z : PresheafedSpace C} (α : hom X Y) (β : hom Y Z) : hom X Z :=
{ base := α.base ≫ β.base,
  c := β.c ≫ (presheaf.pushforward β.base).map α.c }

lemma comp_c {X Y Z : PresheafedSpace C} (α : hom X Y) (β : hom Y Z) :
  (comp α β).c = β.c ≫ (presheaf.pushforward β.base).map α.c := rfl


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
  id_comp' := λ X Y f, by { ext1,
    { rw comp_c, erw eq_to_hom_map, simp, apply comp_id }, apply id_comp },
  comp_id' := λ X Y f, by { ext1,
    { rw comp_c, erw congr_hom (presheaf.id_pushforward) f.c,
      simp, erw eq_to_hom_trans_assoc, simp }, apply comp_id },
  assoc' := λ W X Y Z f g h, by { ext1,
    repeat {rw comp_c}, simpa, refl } }

end

variables {C}

@[simp] lemma id_base (X : PresheafedSpace C) :
  ((𝟙 X) : X ⟶ X).base = 𝟙 (X : Top.{v}) := rfl

lemma id_c (X : PresheafedSpace C) :
  ((𝟙 X) : X ⟶ X).c = eq_to_hom (presheaf.pushforward.id_eq X.presheaf).symm := rfl

@[simp] lemma id_c_app (X : PresheafedSpace C) (U) :
  ((𝟙 X) : X ⟶ X).c.app U = eq_to_hom (by { induction U using opposite.rec, cases U, refl }) :=
by { induction U using opposite.rec, cases U, simp only [id_c], dsimp, simp, }

@[simp] lemma comp_base {X Y Z : PresheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).base = f.base ≫ g.base := rfl

@[simp] lemma comp_c_app {X Y Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
  (α ≫ β).c.app U = (β.c).app U ≫ (α.c).app (op ((opens.map (β.base)).obj (unop U))) := rfl

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
  {f : U ⟶ (X : Top.{v})} (h : open_embedding f) : PresheafedSpace C :=
{ carrier := U,
  presheaf := h.is_open_map.functor.op ⋙ X.presheaf }

/--
The map from the restriction of a presheafed space.
-/
def of_restrict {U : Top} (X : PresheafedSpace C)
  {f : U ⟶ (X : Top.{v})} (h : open_embedding f) :
  X.restrict h ⟶ X :=
{ base := f,
  c := { app := λ V, X.presheaf.map (h.is_open_map.adjunction.counit.app V.unop).op,
    naturality' := λ U V f, show _ = _ ≫ X.presheaf.map _,
      by { rw [← map_comp, ← map_comp], refl } } }

lemma restrict_top_presheaf (X : PresheafedSpace C) :
  (X.restrict (opens.open_embedding ⊤)).presheaf =
  (opens.inclusion_top_iso X.carrier).inv _* X.presheaf :=
by { dsimp, rw opens.inclusion_top_functor X.carrier, refl }

lemma of_restrict_top_c (X : PresheafedSpace C) :
  (X.of_restrict (opens.open_embedding ⊤)).c = eq_to_hom
    (by { rw [restrict_top_presheaf, ←presheaf.pushforward.comp_eq],
          erw iso.inv_hom_id, rw presheaf.pushforward.id_eq }) :=
  /- another approach would be to prove the left hand side
     is a natural isoomorphism, but I encountered a universe
     issue when `apply nat_iso.is_iso_of_is_iso_app`. -/
begin
  ext U, change X.presheaf.map _ = _, convert eq_to_hom_map _ _ using 1,
  congr, simpa,
  { induction U using opposite.rec, dsimp, congr, ext,
    exact ⟨ λ h, ⟨⟨x,trivial⟩,h,rfl⟩, λ ⟨⟨_,_⟩,h,rfl⟩, h ⟩ },
  /- or `rw [opens.inclusion_top_functor, ←comp_obj, ←opens.map_comp_eq],
         erw iso.inv_hom_id, cases U, refl` after `dsimp` -/
end

/--
The map to the restriction of a presheafed space along the canonical inclusion from the top
subspace.
-/
@[simps]
def to_restrict_top (X : PresheafedSpace C) :
  X ⟶ X.restrict (opens.open_embedding ⊤) :=
{ base := (opens.inclusion_top_iso X.carrier).inv,
  c := eq_to_hom (restrict_top_presheaf X) }

/--
The isomorphism from the restriction to the top subspace.
-/
@[simps]
def restrict_top_iso (X : PresheafedSpace C) :
  X.restrict (opens.open_embedding ⊤) ≅ X :=
{ hom := X.of_restrict _,
  inv := X.to_restrict_top,
  hom_inv_id' := ext _ _ (concrete_category.hom_ext _ _ $ λ ⟨x, _⟩, rfl) $
    by { erw comp_c, rw X.of_restrict_top_c, simpa },
  inv_hom_id' := ext _ _ rfl $
    by { erw comp_c, rw X.of_restrict_top_c, simpa } }

/--
The global sections, notated Gamma.
-/
@[simps]
def Γ : (PresheafedSpace C)ᵒᵖ ⥤ C :=
{ obj := λ X, (unop X).presheaf.obj (op ⊤),
  map := λ X Y f, f.unop.c.app (op ⊤) }

lemma Γ_obj_op (X : PresheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) := rfl

lemma Γ_map_op {X Y : PresheafedSpace C} (f : X ⟶ Y) :
  Γ.map f.op = f.c.app (op ⊤) := rfl

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
    c := whisker_left X.presheaf α ≫ eq_to_hom (presheaf.pushforward.id_eq _).symm } }

-- TODO Assemble the last two constructions into a functor
--   `(C ⥤ D) ⥤ (PresheafedSpace C ⥤ PresheafedSpace D)`
end nat_trans

end category_theory
