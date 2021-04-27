/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.homology
import tactic.omega

/-!
# Chain complexes supported in a single degree

We define `single V j c : V ⥤ homological_complex V c`,
which constructs complexes in `V` of shape `c`, supported in degree `j`.

-/

open category_theory
open category_theory.limits

universes v u

variables (V : Type u) [category.{v} V] [has_zero_morphisms V] [has_zero_object V]

namespace homological_complex
variables {ι : Type*} [decidable_eq ι] (c : complex_shape ι)

local attribute [instance] has_zero_object.has_zero

@[simps]
def single (j : ι) : V ⥤ homological_complex V c :=
{ obj := λ A,
  { X := λ i, if i = j then A else 0,
    d := λ i j, 0, },
  map := λ A B f,
  { f := λ i, if h : i = j then
      eq_to_hom (by { dsimp, rw if_pos h, }) ≫ f ≫ eq_to_hom (by { dsimp, rw if_pos h, })
    else
      0, },
  map_id' := λ A, begin
    ext,
    dsimp,
    split_ifs with h,
    { subst h, simp, },
    { rw if_neg h, simp, },
  end,
  map_comp' := λ A B C f g, begin
    ext,
    dsimp,
    split_ifs with h,
    { subst h, simp, },
    { simp, },
  end, }.

@[simp] lemma single_obj_X_self (j : ι) (A : V) : ((single V c j).obj A).X j = A :=
by simp

@[simp] lemma single_map_f_self (j : ι) {A B : V} (f : A ⟶ B) :
  ((single V c j).map f).f j = eq_to_hom (by simp) ≫ f ≫ eq_to_hom (by simp) :=
by { simp, refl, }

end homological_complex

open homological_complex

namespace chain_complex

variables {V}

/--
Morphisms from a `ℕ`-indexed chain complex `C`
to a single object chain complex with `X` concentrated in degree 0
are the same as morphisms `f : C.X 0 ⟶ X` such that `C.d 1 0 ≫ f = 0`.
-/
def to_single_equiv (C : chain_complex V ℕ) (X : V) :
  (C ⟶ (single V _ 0).obj X) ≃ { f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 } :=
{ to_fun := λ f, ⟨f.f 0, by { rw ←f.comm 1 0, simp, }⟩,
  inv_fun := λ f,
  { f := λ i, if h : i = 0 then
      eq_to_hom (congr_arg C.X h) ≫ f.1 ≫ eq_to_hom (by { subst h, refl, })
    else
      0,
    comm' := λ i j, begin
      split_ifs with hi hj hj,
      { substs hi hj, simp, },
      { simp, },
      { subst hj,
        simp only [category.comp_id, category.id_comp, single_obj_d, eq_to_hom_refl, zero_comp],
        cases i,
        { simp, },
        { cases i,
          { exact f.2.symm, },
          { rw [C.shape, zero_comp],
            simp only [complex_shape.down_rel],
            omega, } }, },
      { simp, },
    end, },
  left_inv := λ f, begin
    ext i,
    dsimp,
    split_ifs with h,
    { subst h, simp, },
    { refine (zero_of_target_iso_zero _ _).symm,
      rw if_neg h, },
  end,
  right_inv := by tidy, }

end chain_complex
