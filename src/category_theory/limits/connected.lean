/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.equalizers
import category_theory.limits.preserves.basic
import category_theory.is_connected

/-!
# Connected limits

A connected limit is a limit whose shape is a connected category.

We give examples of connected categories, and prove that the functor given
by `(X × -)` preserves any connected limit. That is, any limit of shape `J`
where `J` is a connected category is preserved by the functor `(X × -)`.
-/

noncomputable theory

universes v₁ v₂ u₁ u₂

open category_theory category_theory.category category_theory.limits
namespace category_theory

section examples

instance wide_pullback_shape_connected (J : Type v₁) : is_connected (wide_pullback_shape J) :=
begin
  apply is_connected.of_induct,
  introv hp t,
  cases j,
  { exact hp },
  { rwa t (wide_pullback_shape.hom.term j) }
end

instance wide_pushout_shape_connected (J : Type v₁) : is_connected (wide_pushout_shape J) :=
begin
  apply is_connected.of_induct,
  introv hp t,
  cases j,
  { exact hp },
  { rwa ← t (wide_pushout_shape.hom.init j) }
end

instance parallel_pair_inhabited : inhabited walking_parallel_pair := ⟨walking_parallel_pair.one⟩

instance parallel_pair_connected : is_connected (walking_parallel_pair) :=
begin
  apply is_connected.of_induct,
  introv _ t,
  cases j,
  { rwa t walking_parallel_pair_hom.left },
  { assumption }
end
end examples

local attribute [tidy] tactic.case_bash

variables {C : Type u₂} [category.{v₂} C]

variables [has_binary_products C]

variables {J : Type v₂} [small_category J]

namespace prod_preserves_connected_limits

/-- (Impl). The obvious natural transformation from (X × K -) to K. -/
@[simps]
def γ₂ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ K :=
{ app := λ Y, limits.prod.snd }

/-- (Impl). The obvious natural transformation from (X × K -) to X -/
@[simps]
def γ₁ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ (functor.const J).obj X :=
{ app := λ Y, limits.prod.fst }

/-- (Impl).
Given a cone for (X × K -), produce a cone for K using the natural transformation `γ₂` -/
@[simps]
def forget_cone {X : C} {K : J ⥤ C} (s : cone (K ⋙ prod.functor.obj X)) : cone K :=
{ X := s.X,
  π := s.π ≫ γ₂ X }

end prod_preserves_connected_limits

open prod_preserves_connected_limits

/--
The functor `(X × -)` preserves any connected limit.
Note that this functor does not preserve the two most obvious disconnected limits - that is,
`(X × -)` does not preserve products or terminal object, eg `(X ⨯ A) ⨯ (X ⨯ B)` is not isomorphic to
`X ⨯ (A ⨯ B)` and `X ⨯ 1` is not isomorphic to `1`.
-/
noncomputable
def prod_preserves_connected_limits [is_connected J] (X : C) :
  preserves_limits_of_shape J (prod.functor.obj X) :=
{ preserves_limit := λ K,
  { preserves := λ c l,
    { lift := λ s, prod.lift
        (s.π.app (classical.arbitrary _) ≫ limits.prod.fst)
        (l.lift (forget_cone s)),
      fac' := λ s j,
      begin
        apply prod.hom_ext,
        { erw [assoc, lim_map_π, comp_id, limit.lift_π],
          exact (nat_trans_from_is_connected (s.π ≫ γ₁ X) j (classical.arbitrary _)).symm },
        { simp [← l.fac (forget_cone s) j] }
      end,
      uniq' := λ s m L,
      begin
        apply prod.hom_ext,
        { erw [limit.lift_π, ← L (classical.arbitrary J), assoc, lim_map_π, comp_id],
          refl },
        { rw limit.lift_π,
          apply l.uniq (forget_cone s),
          intro j,
          simp [← L j] }
      end } } }

end category_theory
