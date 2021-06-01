/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.homology.homological_complex

/-!
# Complexes in functor categories

We can view a complex valued in a functor category `T ⥤ V` as
a functor from `T` to complexes valued in `V`.

## Future work
In fact this is an equivalence of categories.

-/

universes v u

open category_theory
open category_theory.limits

namespace homological_complex

variables {V : Type u} [category.{v} V] [has_zero_morphisms V]
variables {ι : Type*} {c : complex_shape ι}

/-- A complex of functors gives a functor to complexes. -/
@[simps obj map]
def as_functor {T : Type*} [category T]
  (C : homological_complex (T ⥤ V) c) :
  T ⥤ homological_complex V c :=
{ obj := λ t,
  { X := λ i, (C.X i).obj t,
    d := λ i j, (C.d i j).app t,
    d_comp_d' := λ i j k hij hjk, begin
      have := C.d_comp_d i j k,
      rw [nat_trans.ext_iff, function.funext_iff] at this,
      exact this t
    end,
    shape' := λ i j h, begin
      have := C.shape _ _ h,
      rw [nat_trans.ext_iff, function.funext_iff] at this,
      exact this t
    end },
  map := λ t₁ t₂ h,
  { f := λ i, (C.X i).map h,
    comm' := λ i j hij, nat_trans.naturality _ _ },
  map_id' := λ t, by { ext i, dsimp, rw (C.X i).map_id, },
  map_comp' := λ t₁ t₂ t₃ h₁ h₂, by { ext i, dsimp, rw functor.map_comp, } }

/-- The functorial version of `homological_complex.as_functor`. -/
-- TODO in fact, this is an equivalence of categories.
@[simps]
def complex_of_functors_to_functor_to_complex {T : Type*} [category T] :
  (homological_complex (T ⥤ V) c) ⥤ (T ⥤ homological_complex V c) :=
{ obj := λ C, C.as_functor,
  map := λ C D f,
  { app := λ t,
    { f := λ i, (f.f i).app t,
      comm' := λ i j w, nat_trans.congr_app (f.comm i j) t, },
    naturality' := λ t t' g, by { ext i, exact (f.f i).naturality g, }, } }

end homological_complex
