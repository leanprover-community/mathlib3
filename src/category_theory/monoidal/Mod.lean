/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.Mon_

/-!
# The category of module objects over a monoid object.
-/

universes v₁ v₂ u₁ u₂

open category_theory
open category_theory.monoidal_category

variables (C : Type u₁) [category.{v₁} C] [monoidal_category.{v₁} C]

variables {C}

/-- A module object for a monoid object, all internal to some monoidal category. -/
structure Mod (A : Mon_ C) :=
(X : C)
(act : A.X ⊗ X ⟶ X)
(one_act' : (A.one ⊗ 𝟙 X) ≫ act = (λ_ X).hom . obviously)
(assoc' : (A.mul ⊗ 𝟙 X) ≫ act = (α_ A.X A.X X).hom ≫ (𝟙 A.X ⊗ act) ≫ act . obviously)

restate_axiom Mod.one_act'
restate_axiom Mod.assoc'
attribute [simp, reassoc] Mod.one_act Mod.assoc

namespace Mod

variables {A : Mon_ C} (M : Mod A)

lemma assoc_flip : (𝟙 A.X ⊗ M.act) ≫ M.act = (α_ A.X A.X M.X).inv ≫ (A.mul ⊗ 𝟙 M.X) ≫ M.act :=
by simp

/-- A morphism of module objects. -/
@[ext]
structure hom (M N : Mod A) :=
(hom : M.X ⟶ N.X)
(act_hom' : M.act ≫ hom = (𝟙 A.X ⊗ hom) ≫ N.act . obviously)

restate_axiom hom.act_hom'
attribute [simp, reassoc] hom.act_hom

/-- The identity morphism on a module object. -/
@[simps]
def id (M : Mod A) : hom M M :=
{ hom := 𝟙 M.X, }

instance hom_inhabited (M : Mod A) : inhabited (hom M M) := ⟨id M⟩

/-- Composition of module object morphisms. -/
@[simps]
def comp {M N O : Mod A} (f : hom M N) (g : hom N O) : hom M O :=
{ hom := f.hom ≫ g.hom, }

instance : category (Mod A) :=
{ hom := λ M N, hom M N,
  id := id,
  comp := λ M N O f g, comp f g, }

@[simp] lemma id_hom' (M : Mod A) : (𝟙 M : hom M M).hom = 𝟙 M.X := rfl
@[simp] lemma comp_hom' {M N K : Mod A} (f : M ⟶ N) (g : N ⟶ K) :
  (f ≫ g : hom M K).hom = f.hom ≫ g.hom := rfl

variables (A)

/-- A monoid object as a module over itself. -/
@[simps]
def regular : Mod A :=
{ X := A.X,
  act := A.mul, }

instance : inhabited (Mod A) := ⟨regular A⟩

/-- The forgetful functor from module objects to the ambient category. -/
def forget : Mod A ⥤ C :=
{ obj := λ A, A.X,
  map := λ A B f, f.hom, }

open category_theory.monoidal_category

/--
A morphism of monoid objects induces a "restriction" or "comap" functor
between the categories of module objects.
-/
@[simps]
def comap {A B : Mon_ C} (f : A ⟶ B) : Mod B ⥤ Mod A :=
{ obj := λ M,
  { X := M.X,
    act := (f.hom ⊗ 𝟙 M.X) ≫ M.act,
    one_act' :=
    begin
      slice_lhs 1 2 { rw [←comp_tensor_id], },
      rw [f.one_hom, one_act],
    end,
    assoc' :=
    begin
      -- oh, for homotopy.io in a widget!
      slice_rhs 2 3 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor], },
      rw id_tensor_comp,
      slice_rhs 4 5 { rw Mod.assoc_flip, },
      slice_rhs 3 4 { rw associator_inv_naturality, },
      slice_rhs 2 3 { rw [←tensor_id, associator_inv_naturality], },
      slice_rhs 1 3 { rw [iso.hom_inv_id_assoc], },
      slice_rhs 1 2 { rw [←comp_tensor_id, tensor_id_comp_id_tensor], },
      slice_rhs 1 2 { rw [←comp_tensor_id, ←f.mul_hom], },
      rw [comp_tensor_id, category.assoc],
    end, },
  map := λ M N g,
  { hom := g.hom,
    act_hom' :=
    begin
      dsimp,
      slice_rhs 1 2 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor], },
      slice_rhs 2 3 { rw ←g.act_hom, },
      rw category.assoc,
    end }, }

-- Lots more could be said about `comap`, e.g. how it interacts with
-- identities, compositions, and equalities of monoid object morphisms.

end Mod
