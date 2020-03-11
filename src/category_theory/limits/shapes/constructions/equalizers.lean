/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.pullbacks

/-!
# Constructing equalizers from pullbacks and binary products.

If a category has pullbacks and binary products, then it has equalizers.

TODO: provide the dual result.
-/
universes v u

open category_theory category_theory.category

namespace category_theory.limits

variables {C : Type u} [𝒞 : category.{v} C] [has_binary_products.{v} C] [has_pullbacks.{v} C]
include 𝒞

-- We hide the "implementation details" inside a namespace
namespace has_equalizers_of_pullbacks_and_binary_products

/-- Define the equalizing object -/
@[reducible]
def construct_equalizer (F : walking_parallel_pair ⥤ C) : C :=
pullback (prod.lift (𝟙 _) (F.map walking_parallel_pair_hom.left))
         (prod.lift (𝟙 _) (F.map walking_parallel_pair_hom.right))

/-- Define the equalizing morphism -/
@[reducible]
def construct_ι (F : walking_parallel_pair ⥤ C) :
  construct_equalizer F ⟶ F.obj walking_parallel_pair.zero :=
pullback.fst

lemma construct_ι_eq_snd (F : walking_parallel_pair ⥤ C) : construct_ι F = pullback.snd :=
begin
  have l: (pullback.fst ≫ prod.lift (𝟙 _) (F.map walking_parallel_pair_hom.left)) ≫ limits.prod.fst = (pullback.snd ≫ prod.lift (𝟙 _) (F.map walking_parallel_pair_hom.right)) ≫ limits.prod.fst,
    rw pullback.condition,
  erw [assoc, assoc, limit.lift_π, limit.lift_π, comp_id, comp_id] at l, exact l
end

/-- Define the equalizing cone -/
@[reducible]
def equalizer_cone (F : walking_parallel_pair ⥤ C) : cone F :=
cone.of_fork
  (fork.of_ι (construct_ι F)
    (begin
      have r: (pullback.fst ≫ prod.lift (𝟙 _) (F.map walking_parallel_pair_hom.left)) ≫ limits.prod.snd = (pullback.snd ≫ prod.lift (𝟙 _) (F.map walking_parallel_pair_hom.right)) ≫ limits.prod.snd,
        rw pullback.condition,
      simp only [limit.lift_π, assoc] at r,
      erw r, rw construct_ι_eq_snd, refl
     end))

/-- Show the equalizing cone is a limit -/
def equalizer_cone_is_limit (F : walking_parallel_pair ⥤ C) : is_limit (equalizer_cone F) :=
{ lift :=
  begin
    intro c, apply pullback.lift (c.π.app _) (c.π.app _),
    apply limit.hom_ext,
    rintro (_ | _), all_goals { simp [assoc, limit.lift_π] }
  end,
  fac' :=
  begin
    intro c, rintro (_ | _),
    { simp, refl },
    { simp, exact c.w _ }
  end,
  uniq' :=
  begin
    intros c _ J,
    have J1 := J walking_parallel_pair.zero, simp at J1,
    apply pullback.hom_ext,
    { rwa limit.lift_π },
    { erw [limit.lift_π, ← J1, construct_ι_eq_snd] }
  end
}

end has_equalizers_of_pullbacks_and_binary_products

open has_equalizers_of_pullbacks_and_binary_products
/-- Any category with pullbacks and binary products, has equalizers. -/
-- This is not an instance, as it is not always how one wants to construct equalizers!
def has_equalizers_of_pullbacks_and_binary_products :
  has_equalizers.{v} C :=
{ has_limits_of_shape :=
  { has_limit := λ F,
    { cone := equalizer_cone F,
      is_limit := equalizer_cone_is_limit F } } }

end category_theory.limits
