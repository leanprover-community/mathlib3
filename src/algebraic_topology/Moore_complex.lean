/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.homological_complex
import algebraic_topology.simplicial_object
import category_theory.abelian.basic

/-!
## Moore complex

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We construct the normalized Moore complex, as a functor
`simplicial_object C ⥤ chain_complex C ℕ`,
for any abelian category `C`.

The `n`-th object is intersection of
the kernels of `X.δ i : X.obj n ⟶ X.obj (n-1)`, for `i = 1, ..., n`.

The differentials are induced from `X.δ 0`,
which maps each of these intersections of kernels to the next.

This functor is one direction of the Dold-Kan equivalence, which we're still working towards.

### References

* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex
-/

universes v u

noncomputable theory

open category_theory category_theory.limits
open opposite

namespace algebraic_topology

variables {C : Type*} [category C] [abelian C]
local attribute [instance] abelian.has_pullbacks

/-! The definitions in this namespace are all auxiliary definitions for `normalized_Moore_complex`
and should usually only be accessed via that. -/
namespace normalized_Moore_complex

open category_theory.subobject
variables (X : simplicial_object C)

/--
The normalized Moore complex in degree `n`, as a subobject of `X n`.
-/
@[simp]
def obj_X : Π n : ℕ, subobject (X.obj (op (simplex_category.mk n)))
| 0 := ⊤
| (n+1) := finset.univ.inf (λ k : fin (n+1), kernel_subobject (X.δ k.succ))

/--
The differentials in the normalized Moore complex.
-/
@[simp]
def obj_d : Π n : ℕ, (obj_X X (n+1) : C) ⟶ (obj_X X n : C)
| 0 := subobject.arrow _ ≫ X.δ (0 : fin 2) ≫ inv ((⊤ : subobject _).arrow)
| (n+1) :=
begin
  -- The differential is `subobject.arrow _ ≫ X.δ (0 : fin (n+3))`,
  -- factored through the intersection of the kernels.
  refine factor_thru _ (arrow _ ≫ X.δ (0 : fin (n+3))) _,
  -- We now need to show that it factors!
  -- A morphism factors through an intersection of subobjects if it factors through each.
  refine ((finset_inf_factors _).mpr (λ i m, _)),
  -- A morphism `f` factors through the kernel of `g` exactly if `f ≫ g = 0`.
  apply kernel_subobject_factors,
  -- Use a simplicial identity
  dsimp [obj_X],
  erw [category.assoc, ←X.δ_comp_δ (fin.zero_le i.succ), ←category.assoc],
  -- It's the first two factors which are zero.
  convert zero_comp,
  -- We can rewrite the arrow out of the intersection of all the kernels as a composition
  -- of a morphism we don't care about with the arrow out of the kernel of `X.δ i.succ.succ`.
  rw ←factor_thru_arrow _ _ (finset_inf_arrow_factors finset.univ _ i.succ (by simp)),
  -- It's the second two factors which are zero.
  rw [category.assoc],
  convert comp_zero,
  exact kernel_subobject_arrow_comp _,
end

lemma d_squared (n : ℕ) : obj_d X (n+1) ≫ obj_d X n = 0 :=
begin
  -- It's a pity we need to do a case split here;
  -- after the first simp the proofs are almost identical
  cases n; dsimp,
  { simp only [subobject.factor_thru_arrow_assoc],
    slice_lhs 2 3 { erw ←X.δ_comp_δ (fin.zero_le (0 : fin (0 + 2))), },
    rw ←factor_thru_arrow _ _ (finset_inf_arrow_factors finset.univ _ (0 : fin 2) (by simp)),
    slice_lhs 2 3 { rw [kernel_subobject_arrow_comp], },
    simp, },
  { simp [factor_thru_right],
    slice_lhs 2 3 { erw ←X.δ_comp_δ (fin.zero_le (0 : fin (n.succ + 2))) },
    rw ←factor_thru_arrow _ _ (finset_inf_arrow_factors finset.univ _ (0 : fin (n+3)) (by simp)),
    slice_lhs 2 3 { rw [kernel_subobject_arrow_comp], },
    simp, },
end

/--
The normalized Moore complex functor, on objects.
-/
@[simps]
def obj (X : simplicial_object C) : chain_complex C ℕ :=
chain_complex.of (λ n, (obj_X X n : C)) -- the coercion here picks a representative of the subobject
  (obj_d X) (d_squared X)

variables {X} {Y : simplicial_object C} (f : X ⟶ Y)

/--
The normalized Moore complex functor, on morphisms.
-/
@[simps]
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
chain_complex.of_hom _ _ _ _ _ _
  (λ n, begin
    refine factor_thru _ (arrow _ ≫ f.app (op (simplex_category.mk n))) _,
    cases n; dsimp,
    { apply top_factors, },
    { refine (finset_inf_factors _).mpr (λ i m, _),
      apply kernel_subobject_factors,
      slice_lhs 2 3 { erw ←f.naturality, },
      rw ←factor_thru_arrow _ _ (finset_inf_arrow_factors finset.univ _ i (by simp)),
      slice_lhs 2 3 { erw [kernel_subobject_arrow_comp], },
      simp, }
  end)
  (λ n, begin
    cases n; dsimp,
    { ext, simp, },
    { ext, simp, },
  end)

end normalized_Moore_complex

open normalized_Moore_complex

variables (C)

/--
The (normalized) Moore complex of a simplicial object `X` in an abelian category `C`.

The `n`-th object is intersection of
the kernels of `X.δ i : X.obj n ⟶ X.obj (n-1)`, for `i = 1, ..., n`.

The differentials are induced from `X.δ 0`,
which maps each of these intersections of kernels to the next.
-/
@[simps]
def normalized_Moore_complex : simplicial_object C ⥤ chain_complex C ℕ :=
{ obj := obj,
  map := λ X Y f, map f,
  map_id' := λ X, by { ext n, cases n; { dsimp, simp, }, },
  map_comp' := λ X Y Z f g, by { ext n, cases n; simp, }, }

variable {C}

@[simp]
lemma normalized_Moore_complex_obj_d (X : simplicial_object C) (n : ℕ) :
  ((normalized_Moore_complex C).obj X).d (n+1) n = normalized_Moore_complex.obj_d X n :=
by apply chain_complex.of_d

end algebraic_topology
