/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_geometry.presheafed_space
import topology.sheaves.sheaf

/-!
# Sheafed spaces

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

variables (C : Type u) [category.{v} C] [limits.has_products C]

local attribute [tidy] tactic.op_induction'

namespace algebraic_geometry

/-- A `SheafedSpace C` is a topological space equipped with a sheaf of `C`s. -/
structure SheafedSpace extends PresheafedSpace C :=
(sheaf_condition : presheaf.sheaf_condition)

variables {C}

namespace SheafedSpace

instance coe_carrier : has_coe (SheafedSpace C) Top :=
{ coe := λ X, X.carrier }

/-- Extract the `sheaf C (X : Top)` from a `SheafedSpace C`. -/
def sheaf (X : SheafedSpace C) : sheaf C (X : Top.{v}) := ⟨X.presheaf, X.sheaf_condition⟩

@[simp] lemma as_coe (X : SheafedSpace C) : X.carrier = (X : Top.{v}) := rfl
@[simp] lemma mk_coe (carrier) (presheaf) (h) :
  (({ carrier := carrier, presheaf := presheaf, sheaf_condition := h } : SheafedSpace.{v} C) :
  Top.{v}) = carrier :=
rfl

instance (X : SheafedSpace.{v} C) : topological_space X := X.carrier.str

/-- The trivial `punit` valued sheaf on any topological space. -/
noncomputable
def punit (X : Top) : SheafedSpace (discrete punit) :=
{ sheaf_condition := presheaf.sheaf_condition_punit _,
  ..@PresheafedSpace.const (discrete punit) _ X punit.star }

noncomputable
instance : inhabited (SheafedSpace (discrete _root_.punit)) := ⟨punit (Top.of pempty)⟩

instance : category (SheafedSpace C) :=
show category (induced_category (PresheafedSpace C) SheafedSpace.to_PresheafedSpace),
by apply_instance

/-- Forgetting the sheaf condition is a functor from `SheafedSpace C` to `PresheafedSpace C`. -/
@[derive [full, faithful]]
def forget_to_PresheafedSpace : (SheafedSpace C) ⥤ (PresheafedSpace C) :=
induced_functor _

variables {C}

section
local attribute [simp] id comp

@[simp] lemma id_base (X : SheafedSpace C) :
  ((𝟙 X) : X ⟶ X).base = (𝟙 (X : Top.{v})) := rfl

lemma id_c (X : SheafedSpace C) :
  ((𝟙 X) : X ⟶ X).c =
  (((functor.left_unitor _).inv) ≫
  (whisker_right (nat_trans.op (opens.map_id (X.carrier)).hom) _)) := rfl

@[simp] lemma id_c_app (X : SheafedSpace C) (U) :
  ((𝟙 X) : X ⟶ X).c.app U = eq_to_hom (by { op_induction U, cases U, refl }) :=
by { op_induction U, cases U, simp only [id_c], dsimp, simp, }

@[simp] lemma comp_base {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).base = f.base ≫ g.base := rfl

@[simp] lemma comp_c_app {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
  (α ≫ β).c.app U = (β.c).app U ≫ (α.c).app (op ((opens.map (β.base)).obj (unop U))) ≫
    (Top.presheaf.pushforward.comp _ _ _).inv.app U := rfl

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
noncomputable
def restrict {U : Top} (X : SheafedSpace C)
  (f : U ⟶ (X : Top.{v})) (h : open_embedding f) : SheafedSpace C :=
{ sheaf_condition := λ ι 𝒰, is_limit.of_iso_limit
    ((is_limit.postcompose_inv_equiv _ _).inv_fun (X.sheaf_condition _))
    (sheaf_condition_equalizer_products.fork.iso_of_open_embedding h 𝒰).symm,
  ..X.to_PresheafedSpace.restrict f h }

/--
The restriction of a sheafed space `X` to the top subspace is isomorphic to `X` itself.
-/
noncomputable
def restrict_top_iso (X : SheafedSpace C) :
  X.restrict (opens.inclusion ⊤) (opens.open_embedding ⊤) ≅ X :=
@preimage_iso _ _ _ _ forget_to_PresheafedSpace _ _
  (X.restrict (opens.inclusion ⊤) (opens.open_embedding ⊤)) _
  X.to_PresheafedSpace.restrict_top_iso

/--
The global sections, notated Gamma.
-/
def Γ : (SheafedSpace C)ᵒᵖ ⥤ C :=
forget_to_PresheafedSpace.op ⋙ PresheafedSpace.Γ

lemma Γ_def : (Γ : _ ⥤ C) = forget_to_PresheafedSpace.op ⋙ PresheafedSpace.Γ := rfl

@[simp] lemma Γ_obj (X : (SheafedSpace C)ᵒᵖ) : Γ.obj X = (unop X).presheaf.obj (op ⊤) := rfl

lemma Γ_obj_op (X : SheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) := rfl

@[simp] lemma Γ_map {X Y : (SheafedSpace C)ᵒᵖ} (f : X ⟶ Y) :
  Γ.map f = f.unop.c.app (op ⊤) ≫ (unop Y).presheaf.map (opens.le_map_top _ _).op := rfl

lemma Γ_map_op {X Y : SheafedSpace C} (f : X ⟶ Y) :
  Γ.map f.op = f.c.app (op ⊤) ≫ X.presheaf.map (opens.le_map_top _ _).op := rfl

end SheafedSpace

end algebraic_geometry
