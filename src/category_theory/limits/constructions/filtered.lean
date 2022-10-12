/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.constructions.limits_of_products_and_equalizers
import category_theory.limits.opposites

/-!
# Constructing colimits from finite colimits and filtered colimits

We construct colimits of size `w` from finite colimits and filtered colimits of size `w`. Since
`w`-sized colimits are constructured from coequalizers and `w`-sized coproducts, it suffices to
construct `w`-sized coproducts from finite coproducts and `w`-sized filtered colimits.

The idea is simple: to construct coproducts of shape `α`, we take the colimit of the filtered
diagram of all coproducts of finite subsets of `α`.

We also deduce the dual statement by invoking the original statement in `Cᵒᵖ`.
-/

universes w v u

noncomputable theory

open category_theory

variables {C : Type u} [category.{v} C] {α : Type w}

namespace category_theory.limits

namespace coproducts_from_finite_filtered
local attribute [tidy] tactic.case_bash

/-- If `C` has finite coproducts, a functor `discrete α ⥤ C` lifts to a functor
    `finset (discrete α) ⥤ C` by taking coproducts. -/
@[simps]
def lift_to_finset [has_finite_coproducts C] (F : discrete α ⥤ C) : finset (discrete α) ⥤ C :=
{ obj := λ s, ∐ λ x : s, F.obj x,
  map := λ s t h, sigma.desc (λ y, sigma.ι (λ x : t, F.obj x) ⟨y, h.down.down y.2⟩) }

/-- If `C` has finite coproducts and filtered colimits, we can construct arbitrary coproducts by
    taking the colimit of the diagram formed by the coproducts of finite sets over the indexing
    type. -/
@[simps]
def lift_to_finset_colimit_cocone [has_finite_coproducts C] [has_filtered_colimits_of_size.{w w} C]
  [decidable_eq α] (F : discrete α ⥤ C) : colimit_cocone F :=
{ cocone :=
  { X := colimit (lift_to_finset F),
    ι := discrete.nat_trans $ λ j,
      @sigma.ι _ _ _ (λ x : ({j} : finset (discrete α)), F.obj x) _ ⟨j, by simp⟩ ≫
      colimit.ι (lift_to_finset F) {j} },
  is_colimit :=
  { desc := λ s, colimit.desc (lift_to_finset F)
    { X := s.X,
      ι := { app := λ t, sigma.desc (λ x, s.ι.app x) } },
    uniq' := λ s m h,
    begin
      ext t ⟨⟨j, hj⟩⟩,
      convert h j using 1,
      { simp [← colimit.w (lift_to_finset F) ⟨⟨finset.singleton_subset_iff.2 hj⟩⟩], refl },
      { tidy }
    end } }

end coproducts_from_finite_filtered

open coproducts_from_finite_filtered

lemma has_coproducts_of_finite_and_filtered [has_finite_coproducts C]
  [has_filtered_colimits_of_size.{w w} C] : has_coproducts.{w} C :=
λ α, by { classical, exactI ⟨λ F, has_colimit.mk (lift_to_finset_colimit_cocone F)⟩ }

lemma has_colimits_of_finite_and_filtered [has_finite_colimits C]
  [has_filtered_colimits_of_size.{w w} C] : has_colimits_of_size.{w w} C :=
have has_coproducts.{w} C, from has_coproducts_of_finite_and_filtered,
by exactI has_colimits_of_has_coequalizers_and_coproducts

lemma has_products_of_finite_and_cofiltered [has_finite_products C]
  [has_cofiltered_limits_of_size.{w w} C] : has_products.{w} C :=
have has_coproducts.{w} Cᵒᵖ, from has_coproducts_of_finite_and_filtered,
by exactI has_products_of_opposite

lemma has_limits_of_finite_and_cofiltered [has_finite_limits C]
  [has_cofiltered_limits_of_size.{w w} C] : has_limits_of_size.{w w} C :=
have has_products.{w} C, from has_products_of_finite_and_cofiltered,
by exactI has_limits_of_has_equalizers_and_products

end category_theory.limits
