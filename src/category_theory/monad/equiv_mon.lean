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

# Definitions/Theorems

1. `to_Mon` associates a monoid object in `C ⥤ C` to any monad on `C`.
2. `Monad_to_Mon` is the functorial version of `to_Mon`.
3. `of_Mon` associates a monad on `C` to any monoid object in `C ⥤ C`.
4. `Mon_to_Monad` is the functorial version of `of_Mon`.
5. `Monad_Mon_equiv` is the equivalence between `Monad C` and `Mon_ (C ⥤ C)`.
  NB: It is really an isomorphism of categories!

The primary purpose for the theorems in this file is to construct `Monad_Mon_equiv`.
1. `of_to_mon_end_obj` and `to_of_mon_end_obj` show that the compositions of
  `Mon_to_Monad` and `Monad_to_Mon` act as the identity on objects.
2. `of_to_mon_end` and `to_of_mon_end` promote the equalities from these two theorems to
  equalities with the identity functor.

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

variable (C)
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
variable {C}

/-- To every monoid object in `C ⥤ C` we associate a `Monad C`. -/
def of_Mon : Mon_ (C ⥤ C) → Monad C := λ M,
{ func := M.X,
  str :=
  { η := M.one,
    μ := M.mul,
    assoc' := begin
      intro X,
      rw ←nat_trans.hcomp_id_app,
      change ((M.mul ◫ 𝟙 M.X) ≫ M.mul).app X = _,
      erw M.mul_assoc,
      simp only [nat_trans.comp_app],
      change ((α_ M.X M.X M.X).app X).hom ≫ (_ ◫ _).app X ≫ _ = _,
      suffices : ((α_ M.X M.X M.X).app X).hom = 𝟙 _, by {rw this, simp},
      refl,
    end,
    left_unit' := begin
      intro X,
      have := M.mul_one,
      change (_ ◫ _) ≫ _ = _ at this,
      rw [←nat_trans.id_hcomp_app, ←nat_trans.comp_app, this],
      refl,
    end,
    right_unit' := begin
      intro X,
      have := M.one_mul,
      change (_ ◫ _) ≫ _ = _ at this,
      rw [←nat_trans.hcomp_id_app, ←nat_trans.comp_app, this],
      refl,
    end } }

variable (C)
/-- Passing from `Mon_ (C ⥤ C)` to `Monad C` is functorial. -/
def Mon_to_Monad : Mon_ (C ⥤ C) ⥤ Monad C :=
{ obj := of_Mon,
  map := λ M N f,
  { app_η' := begin
      intro X,
      simp only [auto_param_eq],
      erw [←nat_trans.comp_app,f.one_hom],
      refl,
    end,
    app_μ' := begin
      intro X,
      simp only [auto_param_eq],
      erw [←nat_trans.comp_app, f.mul_hom],
      simp only [nat_trans.naturality, assoc, nat_trans.comp_app],
      erw [nat_trans.hcomp_app, assoc],
      refl,
    end,
    ..f.hom } }
variable {C}

theorem of_to_mon_end_obj (M : Mon_ (C ⥤ C)) : (Mon_to_Monad C ⋙ Monad_to_Mon C).obj M = M :=
  by {apply Mon_.hext, repeat {refl}}

theorem to_of_mon_end_obj (M : Monad C) : (Monad_to_Mon C ⋙ Mon_to_Monad C).obj M = M :=
  by {apply Monad.hext, repeat {refl}}

theorem of_to_mon_end : Mon_to_Monad C ⋙ Monad_to_Mon C = 𝟭 _ :=
begin
  apply functor.ext,
  { intros X Y f,
    ext,
    simp only [functor.id_map, functor.comp_map, Mon_.comp_hom', nat_trans.comp_app,
      Mon_.hom_eq_to_hom, eq_to_hom_app, id_comp, eq_to_hom_refl, comp_id],
    refl },
  { intro X,
    apply of_to_mon_end_obj },
end

theorem to_of_mon_end : Monad_to_Mon C ⋙ Mon_to_Monad _ = 𝟭 _ :=
begin
  apply functor.ext,
  { intros X Y f,
    ext,
    simp only [Monad.comp_to_nat_trans, functor.id_map, functor.comp_map, nat_trans.vcomp_eq_comp,
      nat_trans.comp_app, to_nat_trans_eq_to_hom, eq_to_hom_app, id_comp, eq_to_hom_refl, comp_id],
    refl },
  { intro X,
    apply to_of_mon_end_obj }
end

/-- Oh, monads are just monoids in the category of endofunctors. -/
def Monad_Mon_equiv : equivalence (Monad C) (Mon_ (C ⥤ C)) :=
{ functor := Monad_to_Mon _,
  inverse := Mon_to_Monad _,
  unit_iso := eq_to_iso (eq.symm to_of_mon_end),
  counit_iso := eq_to_iso of_to_mon_end }

end Monad
end category_theory
