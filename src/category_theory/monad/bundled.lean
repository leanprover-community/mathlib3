/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.monad.basic
import category_theory.eq_to_hom

/-!
# Bundled Monads

We define bundled monads as a structure consisting of a functor `func : C ⥤ C` endowed with
a term of type `monad func`. See `category_theory.monad.basic` for the definition.
The type of bundled monads on a category `C` is denoted `Monad C`.

We also define morphisms of bundled monads as morphisms of their underlying monads
in the sense of `category_theory.monad_hom`. We construct a category instance on `Monad C`.
-/

namespace category_theory
open category

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

variables (C : Type u) [category.{v} C]

/-- Bundled monads. -/
structure Monad :=
(func : C ⥤ C)
(str : monad func . tactic.apply_instance)


namespace Monad

/-- The initial monad. TODO: Prove it's initial. -/
def initial : Monad C := { func := 𝟭 _ }

variable {C}

instance : inhabited (Monad C) := ⟨initial C⟩

instance {M : Monad C} : monad M.func := M.str

/-- Morphisms of bundled monads. -/
def hom (M N : Monad C) := monad_hom M.func N.func

namespace hom
instance {M : Monad C} : inhabited (hom M M) := ⟨monad_hom.ident _⟩
end hom

instance : category (Monad C) :=
{ hom := hom,
  id := λ _, monad_hom.ident _,
  comp := λ _ _ _, monad_hom.comp,
  id_comp' := λ _ _, by apply monad_hom.ident_comp,
  comp_id' := λ _ _, by apply monad_hom.comp_ident,
  assoc' := λ _ _ _ _, by apply monad_hom.comp_assoc }

/-- The forgetful functor from `Monad C` to `C ⥤ C`. -/
def forget : Monad C ⥤ (C ⥤ C) :=
{ obj := func,
  map := λ _ _ f, f.to_nat_trans }

theorem hext (M N : Monad C) : M.func = N.func → (η_ M.func) == (η_ N.func) →
  (μ_ M.func) == (μ_ N.func) → M = N := λ h1 h2 h3,
begin
  cases M, cases N,
  dsimp only [] at h1,
  subst h1,
  congr,
  cases M_str, cases N_str,
  congr,
  repeat {apply eq_of_heq, assumption}
end

theorem to_nat_trans_eq_to_hom (M N : Monad C) (h : M = N) :
  monad_hom.to_nat_trans (eq_to_hom h) = eq_to_hom (congr_arg (Monad.func) h) := by {subst h, refl}

end Monad
end category_theory
