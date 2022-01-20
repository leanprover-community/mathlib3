/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.monad.basic
import category_theory.monoidal.End
import category_theory.monoidal.Mon_
import category_theory.category.Cat

/-!

# The equivalence between `Monad C` and `Mon_ (C ⥤ C)`.

A monad "is just" a monoid in the category of endofunctors.

# Definitions/Theorems

1. `to_Mon` associates a monoid object in `C ⥤ C` to any monad on `C`.
2. `Monad_to_Mon` is the functorial version of `to_Mon`.
3. `of_Mon` associates a monad on `C` to any monoid object in `C ⥤ C`.
4. `Monad_Mon_equiv` is the equivalence between `Monad C` and `Mon_ (C ⥤ C)`.

-/

namespace category_theory
open category

universes v u -- morphism levels before object levels. See note [category_theory universes].
variables {C : Type u} [category.{v} C]

namespace Monad
local attribute [instance, reducible] endofunctor_monoidal_category

/-- To every `Monad C` we associated a monoid object in `C ⥤ C`.-/
@[simps]
def to_Mon : monad C → Mon_ (C ⥤ C) := λ M,
{ X := (M : C ⥤ C),
  one := M.η,
  mul := M.μ,
  mul_assoc' := by { ext, dsimp, simp [M.assoc] } }

variable (C)
/-- Passing from `Monad C` to `Mon_ (C ⥤ C)` is functorial. -/
@[simps]
def Monad_to_Mon : monad C ⥤ Mon_ (C ⥤ C) :=
{ obj := to_Mon,
  map := λ _ _ f, { hom := f.to_nat_trans } }
variable {C}

/-- To every monoid object in `C ⥤ C` we associate a `Monad C`. -/
@[simps]
def of_Mon : Mon_ (C ⥤ C) → monad C := λ M,
{ to_functor := M.X,
  η' := M.one,
  μ' := M.mul,
  left_unit' := λ X, by { rw [←M.one.id_hcomp_app, ←nat_trans.comp_app, M.mul_one], refl },
  right_unit' := λ X, by { rw [←M.one.hcomp_id_app, ←nat_trans.comp_app, M.one_mul], refl },
  assoc' := λ X, by { rw [←nat_trans.hcomp_id_app, ←nat_trans.comp_app], simp } }

variable (C)
/-- Passing from `Mon_ (C ⥤ C)` to `Monad C` is functorial. -/
@[simps]
def Mon_to_Monad : Mon_ (C ⥤ C) ⥤ monad C :=
{ obj := of_Mon,
  map := λ _ _ f,
  { app_η' := begin
      intro X,
      erw [←nat_trans.comp_app, f.one_hom],
      refl,
    end,
    app_μ' := begin
      intro X,
      erw [←nat_trans.comp_app, f.mul_hom], -- `finish` closes this goal
      simpa only [nat_trans.naturality, nat_trans.hcomp_app, assoc, nat_trans.comp_app, of_Mon_μ],
    end,
    ..f.hom } }

namespace Monad_Mon_equiv
variable {C}

/-- Isomorphism of functors used in `Monad_Mon_equiv` -/
@[simps {rhs_md := semireducible}]
def counit_iso : Mon_to_Monad C ⋙ Monad_to_Mon C ≅ 𝟭 _ :=
{ hom := { app := λ _, { hom := 𝟙 _ } },
  inv := { app := λ _, { hom := 𝟙 _ } } }

/-- Auxiliary definition for `Monad_Mon_equiv` -/
@[simps]
def unit_iso_hom : 𝟭 _ ⟶ Monad_to_Mon C ⋙ Mon_to_Monad C :=
{ app := λ _, { app := λ _, 𝟙 _ } }

/-- Auxiliary definition for `Monad_Mon_equiv` -/
@[simps]
def unit_iso_inv : Monad_to_Mon C ⋙ Mon_to_Monad C ⟶ 𝟭 _ :=
{ app := λ _, { app := λ _, 𝟙 _ } }

/-- Isomorphism of functors used in `Monad_Mon_equiv` -/
@[simps]
def unit_iso : 𝟭 _ ≅ Monad_to_Mon C ⋙ Mon_to_Monad C :=
{ hom := unit_iso_hom,
  inv := unit_iso_inv }

end Monad_Mon_equiv

open Monad_Mon_equiv

/-- Oh, monads are just monoids in the category of endofunctors (equivalence of categories). -/
@[simps]
def Monad_Mon_equiv : (monad C) ≌ (Mon_ (C ⥤ C)) :=
{ functor := Monad_to_Mon _,
  inverse := Mon_to_Monad _,
  unit_iso := unit_iso,
  counit_iso := counit_iso }

-- Sanity check
example (A : monad C) {X : C} : ((Monad_Mon_equiv C).unit_iso.app A).hom.app X = 𝟙 _ := rfl

end Monad
end category_theory
