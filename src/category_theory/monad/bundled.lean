/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.monad.basic
import category_theory.eq_to_hom

/-!
# Bundled Monads

We define bundled (co)monads as a structure consisting of a functor `func : C ⥤ C` endowed with
a term of type `(co)monad func`. See `category_theory.monad.basic` for the definition.
The type of bundled (co)monads on a category `C` is denoted `(Co)Monad C`.

We also define morphisms of bundled (co)monads as morphisms of their underlying (co)monads
in the sense of `category_theory.(co)monad_hom`. We construct a category instance on `(Co)Monad C`.
-/

namespace category_theory
open category

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

variables (C : Type u) [category.{v} C]

/-- Bundled monads. -/
structure Monad :=
(func : C ⥤ C)
(str : monad func . tactic.apply_instance)

/-- Bundled comonads -/
structure Comonad :=
(func : C ⥤ C)
(str : comonad func . tactic.apply_instance)

namespace Monad

/-- The initial monad. TODO: Prove it's initial. -/
def initial : Monad C := { func := 𝟭 _ }

variable {C}

instance : inhabited (Monad C) := ⟨initial C⟩

instance {M : Monad C} : monad M.func := M.str

/-- Morphisms of bundled monads. -/
def hom (M N : Monad C) := monad_hom M.func N.func

namespace hom
instance {M : Monad C} : inhabited (hom M M) := ⟨monad_hom.id _⟩
end hom

instance : category (Monad C) :=
{ hom := hom,
  id := λ _, monad_hom.id _,
  comp := λ _ _ _, monad_hom.comp }

section
variables (C)

/-- The forgetful functor from `Monad C` to `C ⥤ C`. -/
def forget : Monad C ⥤ (C ⥤ C) :=
{ obj := func,
  map := λ _ _ f, f.to_nat_trans }

end

@[simp]
lemma comp_to_nat_trans {M N L : Monad C} (f : M ⟶ N) (g : N ⟶ L) :
  (f ≫ g).to_nat_trans = nat_trans.vcomp f.to_nat_trans g.to_nat_trans := rfl

@[simp] lemma assoc_func_app {M : Monad C} {X : C} :
  M.func.map ((μ_ M.func).app X) ≫ (μ_ M.func).app X =
  (μ_ M.func).app (M.func.obj X) ≫ (μ_ M.func).app X := by apply monad.assoc

end Monad

namespace Comonad

/-- The terminal comonad. TODO: Prove it's terminal. -/
def terminal : Comonad C := { func := 𝟭 _ }

variable {C}

instance : inhabited (Comonad C) := ⟨terminal C⟩

instance {M : Comonad C} : comonad M.func := M.str

/-- Morphisms of bundled comonads. -/
def hom (M N : Comonad C) := comonad_hom M.func N.func

namespace hom
instance {M : Comonad C} : inhabited (hom M M) := ⟨comonad_hom.id _⟩
end hom

instance : category (Comonad C) :=
{ hom := hom,
  id := λ _, comonad_hom.id _,
  comp := λ _ _ _, comonad_hom.comp }

section
variables (C)

/-- The forgetful functor from `CoMonad C` to `C ⥤ C`. -/
def forget : Comonad C ⥤ (C ⥤ C) :=
{ obj := func,
  map := λ _ _ f, f.to_nat_trans }

end

@[simp]
lemma comp_to_nat_trans {M N L : Comonad C} (f : M ⟶ N) (g : N ⟶ L) :
  (f ≫ g).to_nat_trans = nat_trans.vcomp f.to_nat_trans g.to_nat_trans := rfl

@[simp] lemma coassoc_func_app {M : Comonad C} {X : C} :
  (δ_ M.func).app X ≫ M.func.map ((δ_ M.func).app X) =
  (δ_ M.func).app X ≫ (δ_ M.func).app (M.func.obj X) := by apply comonad.coassoc

end Comonad
end category_theory
