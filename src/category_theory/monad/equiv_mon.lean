/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.monad.bundled
import category_theory.monoidal.End
import category_theory.monoidal.internal
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

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation
variables {C : Type u} [category.{v} C]

namespace Monad
local attribute [instance, reducible] endofunctor_monoidal_category

/-- To every `Monad C` we associated a monoid object in `C ⥤ C`.-/
@[simps]
def to_Mon : Monad C → Mon_ (C ⥤ C) := λ M,
{ X := M.func,
  one := η_ _,
  mul := μ_ _ }

variable (C)
/-- Passing from `Monad C` to `Mon_ (C ⥤ C)` is functorial. -/
@[simps]
def Monad_to_Mon : Monad C ⥤ Mon_ (C ⥤ C) :=
{ obj := to_Mon,
  map := λ M N f,
  { hom := f.to_nat_trans } }
variable {C}

/-- To every monoid object in `C ⥤ C` we associate a `Monad C`. -/
@[simps]
def of_Mon : Mon_ (C ⥤ C) → Monad C := λ M,
{ func := M.X,
  str :=
  { η := M.one,
    μ := M.mul,
    assoc' := begin
      intro X,
      rw [←nat_trans.hcomp_id_app, ←nat_trans.comp_app],
      simp,
    end,
    left_unit' := begin
      intro X,
      rw [←nat_trans.id_hcomp_app, ←nat_trans.comp_app, M.mul_one],
      refl,
    end,
    right_unit' := begin
      intro X,
      rw [←nat_trans.hcomp_id_app, ←nat_trans.comp_app, M.one_mul],
      refl,
    end } }

variable (C)
/-- Passing from `Mon_ (C ⥤ C)` to `Monad C` is functorial. -/
@[simps]
def Mon_to_Monad : Mon_ (C ⥤ C) ⥤ Monad C :=
{ obj := of_Mon,
  map := λ M N f,
  { app_η' := begin
      intro X,
      erw [←nat_trans.comp_app, f.one_hom],
      refl,
    end,
    app_μ' := begin
      intro X,
      erw [←nat_trans.comp_app, f.mul_hom],
      finish,
    end,
    ..f.hom } }
variable {C}

@[simp]
theorem of_to_mon_end_obj (M : Mon_ (C ⥤ C)) : (of_Mon M).to_Mon = M :=
by {apply Mon_.hext, repeat {refl}}

@[simp]
theorem to_of_mon_end_obj (M : Monad C) : of_Mon M.to_Mon = M :=
by {apply Monad.hext, repeat {refl}}

/-- Isomorphism of functors used in `Monad_Mon_equiv` -/
@[simps]
def of_to_mon_end_iso : Mon_to_Monad C ⋙ Monad_to_Mon C ≅ 𝟭 _ :=
{ hom :=
  { app := λ M,
  { hom := 𝟙 _ } },
  inv :=
  { app := λ M,
  { hom := 𝟙 _ } } }

/-- Isomorphism of functors used in `Monad_Mon_equiv` -/
@[simps]
def to_of_mon_end_iso : Monad_to_Mon C ⋙ Mon_to_Monad C ≅ 𝟭 _ :=
{ hom :=
  { app := λ M,
  { app := λ X, 𝟙 _ } },
  inv :=
  { app := λ M,
  { app := λ X, 𝟙 _ } } }

variable (C)
/-- Oh, monads are just monoids in the category of endofunctors (equivalence of categories). -/
@[simps]
def Monad_Mon_equiv : (Monad C) ≌ (Mon_ (C ⥤ C)) :=
{ functor := Monad_to_Mon _,
  inverse := Mon_to_Monad _,
  unit_iso := to_of_mon_end_iso.symm,
  counit_iso := of_to_mon_end_iso }

-- Sanity check
example (A : Monad C) {X : C} : ((Monad_Mon_equiv C).unit_iso.app A).hom.app X = 𝟙 _ := rfl

end Monad
end category_theory
