-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.limits
import category_theory.limits.products
import category_theory.limits.equalizers
import category_theory.discrete_category
import category_theory.walking

universes u v w

open category_theory

namespace category_theory.limits

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞
variables [has_limits.{u v} C] {J : Type v} [𝒥 : small_category J]
include 𝒥

def has_products_from_has_limits : has_products.{u v} C :=
{ fan := λ β f, { .. (limit.cone (functor.of_function f)) },
  is_product := λ β f, { lift := λ s, limit.lift (functor.of_function f) { .. s } } }.

open category_theory.walking

def has_equalizers_from_has_limits : has_equalizers.{u v} C :=
{ fork := λ Y Z f g,
    let c := limit.cone.{u v} (parallel_pair_functor f g) in
    { X := c.X, ι := c.π walking_parallel_pair._1,
      w' :=
      begin
        have h_f := @cone.w _ _ _ _ _ c walking_parallel_pair._1 walking_parallel_pair._2 side.L,
        dsimp [parallel_pair_functor] at h_f,
        rw h_f,
        have h_g := @cone.w _ _ _ _ _ c walking_parallel_pair._1 walking_parallel_pair._2 side.R,
        dsimp [parallel_pair_functor] at h_g,
        rw h_g,
      end },
  is_equalizer := λ Y Z f g,
    let c := limit.cone.{u v} (parallel_pair_functor f g) in
    { lift := λ s, limit.lift (parallel_pair_functor f g)
      { X := s.X,
        π := λ j, begin
                    cases j,
                    exact s.ι,
                    exact s.ι ≫ f
                  end,
        w' := λ j j' f', begin
                          cases j; cases j'; cases f'; dsimp [parallel_pair_functor],
                          simp, exact eq.symm s.w, simp,
                         end, },
      uniq' := begin
                 tidy,
                 cases j,
                 { exact w, },
                 { have h := @limits.limit.w _ _ _ _ _ (parallel_pair_functor f g) walking_parallel_pair._1 walking_parallel_pair._2 side.L,
                   rw [←h, ←category.assoc, w],
                   refl, }
               end } }

end category_theory.limits