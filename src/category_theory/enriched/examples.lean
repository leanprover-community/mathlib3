/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Scott Morrison
-/
import category_theory.enriched.enriched_over
import algebra.category.Module.basic
import linear_algebra.tensor_product

universes v u

open category_theory

section
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

abbreviation preadditive := enriched_over.{v} AddCommGroup.{v} C
end

namespace AddCommGroup

-- Unless https://github.com/leanprover-community/lean/issues/197 is fixed,
-- I'm not sure we can successfully replace this
-- "definition by tactic" with the usual structure syntax.
-- Replacing either the outer `fsplit` or the inner `fsplits` by explicit structures causes
-- errors in which things have been unfolded too far.
instance : preadditive AddCommGroup :=
begin
  fsplit,
  { exact λ X Y, AddCommGroup.of (X ⟶ Y), },
  { intros X Y, refl, },
  { intros X Y f Z,
    { fsplit,
      { exact λ g, g.comp f, },
      { exact add_monoid_hom.zero_comp f, },
      { exact λ x y, by { ext, simp [add_monoid_hom.add_apply], }, }, }, },
  { intros X Y f Z, refl, },
  { intros X Y Z g,
    { fsplit,
      { exact λ f, g.comp f, },
      { exact add_monoid_hom.comp_zero g, },
      { exact λ x y, by { ext, simp [add_monoid_hom.add_apply], }, }, }, },
  { intros X Y Z g, refl, },
end

end AddCommGroup

namespace Module

section
variables (R : Type u) [ring R]

instance : preadditive (Module R) :=
{ enriched_hom := λ X Y, AddCommGroup.of (X ⟶ Y),
  comp_left := λ X Y f Z,
  { to_fun := λ g, g.comp f, map_zero' := by simp, map_add' := λ x y, by { ext, simp, } },
  comp_right := λ X Y Z g,
  { to_fun := λ f, g.comp f, map_zero' := by simp, map_add' := λ x y, by { ext, simp, } }, }.
end

section
variables {R : Type} [ring R]
abbreviation Ab := AddCommGroup.{0}
variables {M N P : Module R}

open category_theory.enriched_over

-- We get an `AddCommGroup` worth of morphisms:
example : AddCommGroup := M ⟶[Ab] N
-- We can add them!
example (f g : M ⟶[Ab] N) : M ⟶ N := f + g
-- We can see that composition is additive in either argument:
example (f : M ⟶[Ab] N) : (N ⟶[Ab] P) →+ (M ⟶[Ab] P) := comp_left Ab f P
-- Coercions to functions isn't as good as we'd like,
-- but we can verify that `comp_left` is definitionally what we expect:
example (f : M ⟶[Ab] N) (g : N ⟶[Ab] P) (m : M) :
  ((comp_left Ab f P : (N ⟶[Ab] P) → (M ⟶[Ab] P)) g).to_fun m = g (f m) := rfl
end

section
variables (R : Type u) [comm_ring R]

instance : enriched_over (Module R) (Module R) :=
{ enriched_hom := λ X Y, Module.of R (X ⟶ Y),
  comp_left := λ X Y f Z, (linear_map.llcomp R X Y Z).flip f,
  comp_right := λ X Y Z g, linear_map.llcomp R X Y Z g, }

-- Out of the box, we can treat morphisms between R-modules as elements of an R-module.
example (X Y : Module R) (r : R) (f g : X ⟶[Module R] Y) : r • (f + g) = r • g + r • f :=
by simp [smul_add, add_comm]

-- Check that the coercion to functions works:
example (X Y : Module R) (f : X ⟶[Module R] Y) : f (0 : X) = (0 : Y) := by simp

end

end Module
