/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.monad.bundled
import category_theory.monoidal.End
import category_theory.monoidal.internal

/-!

# The equivalence between `Monad C` and `Mon_ (C ⥤ C)`.

A monad "is just" a monoid in the category of endofunctors.
-/

namespace category_theory
open category

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation
variables {C : Type u} [category.{v} C]

namespace Monad
local attribute [instance] endofunctor_monoidal_category

/-- To every `Monad C` we associated a monoid object in `C ⥤ C`.-/
def to_Mon : Monad C → Mon_ (C ⥤ C) := λ M,
{ X := M.func,
  one := η_ _,
  mul := μ_ _,
  one_mul' := begin
    change (_ ◫ _) ≫ _ = _,
    ext A,
    simp only [nat_trans.hcomp_id_app, nat_trans.comp_app],
    apply monad.right_unit,
  end,
  mul_one' := begin
    change (_ ◫ _) ≫ _ = _,
    tidy,
  end,
  mul_assoc' := begin
    change (_ ◫ _) ≫ _ = _ ≫ (_ ◫ _) ≫ _,
    ext A,
    simp only [nat_trans.hcomp_id_app, nat_trans.hcomp_app, functor.map_id,
      nat_trans.id_app, comp_id, nat_trans.comp_app],
    erw id_comp,
    simp_rw monad.assoc,
    change _ = ((α_ M.func M.func M.func).app A).hom ≫ _ ≫ _,
    suffices : ((α_ M.func M.func M.func).app A).hom = 𝟙 _, by {rw this, simp},
    refl,
  end }

/-- Passing from `Monad C` to `Mon_ (C ⥤ C)` is functorial. -/
def Monad_to_Mon : Monad C ⥤ Mon_ (C ⥤ C) :=
{ obj := to_Mon,
  map := λ M N f,
  { hom := f.to_nat_trans,
    one_hom' := begin
      ext,
      simp only [nat_trans.comp_app],
      apply f.app_η,
    end,
    mul_hom' := begin
      change _ = (_ ◫ _) ≫ _,
      ext,
      simp only [nat_trans.hcomp_app, assoc, nat_trans.comp_app],
      change (μ_ _).app x ≫ f.app x = _,
      rw f.app_μ,
      simp only [nat_trans.naturality, assoc],
      refl,
    end } }

/-- To every term of `Mon_ (C ⥤ C)` we associate a `Monad C`. -/
def of_Mon : Mon_ (C ⥤ C) → Monad C := λ M,
{ func := M.X,
  str :=
  { η := M.one,
    μ := M.mul,
    assoc' := λ X, begin
      have := M.mul_assoc,
      rw ←nat_trans.hcomp_id_app,
      change ((M.mul ◫ 𝟙 M.X) ≫ M.mul).app X = _,
      erw this,
      simp only [nat_trans.comp_app],
      change ((α_ M.X M.X M.X).app X).hom ≫ (_ ◫ _).app X ≫ _ = _,
      suffices : ((α_ M.X M.X M.X).app X).hom = 𝟙 _, by {rw this, simp},
      refl,
    end,
    left_unit' := λ X, begin
      have := M.mul_one,
      change (_ ◫ _) ≫ _ = _ at this,
      rw [←nat_trans.id_hcomp_app, ←nat_trans.comp_app, this],
      refl,
    end,
    right_unit' := λ X, begin
      have := M.one_mul,
      change (_ ◫ _) ≫ _ = _ at this,
      rw [←nat_trans.hcomp_id_app, ←nat_trans.comp_app, this],
      refl,
    end } }

/-- Passing from `Mon_ (C ⥤ C)` to `Monad C` is functorial. -/
def Mon_to_Monad : Mon_ (C ⥤ C) ⥤ Monad C :=
{ obj := of_Mon,
  map := λ M N f,
  { app_η' := λ X, begin
      simp only [auto_param_eq],
      rw ←nat_trans.comp_app,
      erw f.one_hom,
      refl,
    end,
    app_μ' := λ X, begin
      simp only [auto_param_eq],
      rw ←nat_trans.comp_app,
      erw f.mul_hom,
      simp only [nat_trans.naturality, assoc, nat_trans.comp_app],
      erw nat_trans.hcomp_app,
      simp only [assoc],
      refl,
    end,
    ..show M.X ⟶ N.X, by exact f.hom } }

theorem of_to_mon_end_obj (M : Mon_ (C ⥤ C)) : (Mon_to_Monad ⋙ Monad_to_Mon).obj M = M :=
  by {apply Mon_.hext, repeat {refl}}

theorem to_of_mon_end_obj (M : Monad C) : (Monad_to_Mon ⋙ Mon_to_Monad).obj M = M :=
  by {apply Monad.hext, repeat {refl}}

end Monad
end category_theory
