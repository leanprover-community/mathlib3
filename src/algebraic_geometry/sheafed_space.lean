/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_geometry.presheafed_space.has_colimits
import topology.sheaves.functors

/-!
# Sheafed spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Introduces the category of topological spaces equipped with a sheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

universes v u

open category_theory
open Top
open topological_space
open opposite
open category_theory.limits
open category_theory.category category_theory.functor

variables (C : Type u) [category.{v} C]

local attribute [tidy] tactic.op_induction'

namespace algebraic_geometry

/-- A `SheafedSpace C` is a topological space equipped with a sheaf of `C`s. -/
structure SheafedSpace extends PresheafedSpace.{v} C :=
(is_sheaf : presheaf.is_sheaf)

variables {C}

namespace SheafedSpace

instance coe_carrier : has_coe (SheafedSpace C) Top :=
{ coe := λ X, X.carrier }

/-- Extract the `sheaf C (X : Top)` from a `SheafedSpace C`. -/
def sheaf (X : SheafedSpace C) : sheaf C (X : Top.{v}) := ⟨X.presheaf, X.is_sheaf⟩

@[simp] lemma as_coe (X : SheafedSpace.{v} C) : X.carrier = (X : Top.{v}) := rfl
@[simp] lemma mk_coe (carrier) (presheaf) (h) :
  (({ carrier := carrier, presheaf := presheaf, is_sheaf := h } : SheafedSpace.{v} C) :
  Top.{v}) = carrier :=
rfl

instance (X : SheafedSpace.{v} C) : topological_space X := X.carrier.str

/-- The trivial `unit` valued sheaf on any topological space. -/
def unit (X : Top) : SheafedSpace (discrete unit) :=
{ is_sheaf := presheaf.is_sheaf_unit _,
  ..@PresheafedSpace.const (discrete unit) _ X ⟨⟨⟩⟩ }

instance : inhabited (SheafedSpace (discrete _root_.unit)) := ⟨unit (Top.of pempty)⟩

instance : category (SheafedSpace C) :=
show category (induced_category (PresheafedSpace.{v} C) SheafedSpace.to_PresheafedSpace),
by apply_instance

/-- Forgetting the sheaf condition is a functor from `SheafedSpace C` to `PresheafedSpace C`. -/
@[derive [full, faithful]]
def forget_to_PresheafedSpace : (SheafedSpace.{v} C) ⥤ (PresheafedSpace.{v} C) :=
induced_functor _

instance is_PresheafedSpace_iso {X Y : SheafedSpace.{v} C} (f : X ⟶ Y) [is_iso f] :
  @is_iso (PresheafedSpace C) _ _ _ f :=
SheafedSpace.forget_to_PresheafedSpace.map_is_iso f

variables {C}

section
local attribute [simp] id comp

@[simp] lemma id_base (X : SheafedSpace C) :
  ((𝟙 X) : X ⟶ X).base = (𝟙 (X : Top.{v})) := rfl

lemma id_c (X : SheafedSpace C) :
  ((𝟙 X) : X ⟶ X).c = eq_to_hom (presheaf.pushforward.id_eq X.presheaf).symm := rfl

@[simp] lemma id_c_app (X : SheafedSpace C) (U) :
  ((𝟙 X) : X ⟶ X).c.app U = eq_to_hom (by { induction U using opposite.rec, cases U, refl }) :=
by { induction U using opposite.rec, cases U, simp only [id_c], dsimp, simp, }

@[simp] lemma comp_base {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).base = f.base ≫ g.base := rfl

@[simp] lemma comp_c_app {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
  (α ≫ β).c.app U = (β.c).app U ≫ (α.c).app (op ((opens.map (β.base)).obj (unop U)))
:= rfl

lemma comp_c_app' {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
  (α ≫ β).c.app (op U) = (β.c).app (op U) ≫ (α.c).app (op ((opens.map (β.base)).obj U))
:= rfl

lemma congr_app {X Y : SheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) :
  α.c.app U = β.c.app U ≫ X.presheaf.map (eq_to_hom (by subst h)) :=
PresheafedSpace.congr_app h U

variables (C)

/-- The forgetful functor from `SheafedSpace` to `Top`. -/
def forget : SheafedSpace C ⥤ Top :=
{ obj := λ X, (X : Top.{v}),
  map := λ X Y f, f.base }

end

open Top.presheaf

/--
The restriction of a sheafed space along an open embedding into the space.
-/
def restrict {U : Top} (X : SheafedSpace C)
  {f : U ⟶ (X : Top.{v})} (h : open_embedding f) : SheafedSpace C :=
{ is_sheaf := is_sheaf_of_open_embedding h X.is_sheaf,
  ..X.to_PresheafedSpace.restrict h }

/--
The restriction of a sheafed space `X` to the top subspace is isomorphic to `X` itself.
-/
def restrict_top_iso (X : SheafedSpace C) :
  X.restrict (opens.open_embedding ⊤) ≅ X :=
forget_to_PresheafedSpace.preimage_iso X.to_PresheafedSpace.restrict_top_iso

/--
The global sections, notated Gamma.
-/
def Γ : (SheafedSpace C)ᵒᵖ ⥤ C :=
forget_to_PresheafedSpace.op ⋙ PresheafedSpace.Γ

lemma Γ_def : (Γ : _ ⥤ C) = forget_to_PresheafedSpace.op ⋙ PresheafedSpace.Γ := rfl

@[simp] lemma Γ_obj (X : (SheafedSpace C)ᵒᵖ) : Γ.obj X = (unop X).presheaf.obj (op ⊤) := rfl

lemma Γ_obj_op (X : SheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) := rfl

@[simp] lemma Γ_map {X Y : (SheafedSpace C)ᵒᵖ} (f : X ⟶ Y) :
  Γ.map f = f.unop.c.app (op ⊤) := rfl

lemma Γ_map_op {X Y : SheafedSpace C} (f : X ⟶ Y) :
  Γ.map f.op = f.c.app (op ⊤) := rfl

noncomputable
instance [has_limits C] : creates_colimits (forget_to_PresheafedSpace : SheafedSpace C ⥤ _) :=
⟨λ J hJ, by exactI ⟨λ K, creates_colimit_of_fully_faithful_of_iso
  ⟨(PresheafedSpace.colimit_cocone (K ⋙ forget_to_PresheafedSpace)).X,
    limit_is_sheaf _ (λ j, sheaf.pushforward_sheaf_of_sheaf _ (K.obj (unop j)).2)⟩
  (colimit.iso_colimit_cocone ⟨_, PresheafedSpace.colimit_cocone_is_colimit _⟩).symm⟩⟩

instance [has_limits C] : has_colimits (SheafedSpace C) :=
has_colimits_of_has_colimits_creates_colimits forget_to_PresheafedSpace

noncomputable instance [has_limits C] : preserves_colimits (forget C) :=
limits.comp_preserves_colimits forget_to_PresheafedSpace (PresheafedSpace.forget C)

end SheafedSpace

end algebraic_geometry
