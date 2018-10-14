-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.functor

open category_theory

namespace tactic
meta def case_bash : tactic unit :=
do l ← local_context,
   r ← successes (l.reverse.map (λ h, cases h >> skip)),
   when (r.empty) failed
end tactic

local attribute [tidy] tactic.case_bash

namespace category_theory.walking

universes u₁ v₁ u₂ v₂

section
@[derive decidable_eq]
inductive walking_pair : Type u₁ -- TODO reuse `side` from below?
| _1
| _2

open walking_pair

def walking_pair.hom : walking_pair → walking_pair → Type u₁
| _1 _1 := punit
| _2 _2 := punit
| _  _  := pempty

instance walking_pair_category : small_category walking_pair :=
{ hom  := walking_pair.hom,
  id   := by tidy,
  comp := by tidy }

variable {C : Type u₁}
variable [𝒞 : category.{u₁ v₁} C]
include 𝒞

def pair_functor (α β : C) : walking_pair.{v₁} ⥤ C :=
{ obj := λ X, match X with
              | _1 := α
              | _2 := β
              end,
  map' := λ X Y f, match X, Y, f with
                  | _1, _1, _ := 𝟙 α
                  | _2, _2, _ := 𝟙 β
                  end, }
end

section
inductive walking_parallel_pair : Type u₁ | _1 | _2 -- TODO better names? 𝔰 𝔱 for 's'ource and 't'arget?

inductive side : Type u₁ | L | R

open walking_parallel_pair side

instance : small_category walking_parallel_pair :=
{ hom := λ X Y, match X, Y with
                | _1, _1 := punit
                | _2, _2 := punit
                | _1, _2 := side
                | _2, _1 := pempty
                end,
  id       := by tidy,
  comp  := λ X Y Z f g, match X, Y, Z, f, g with
                        | _1, _1, _1, _, _ := punit.star
                        | _2, _2, _2, _, _ := punit.star
                        | _1, _1, _2, _, h := h
                        | _1, _2, _2, h, _ := h
                        end }

variable {C : Type u₁}
variable [category.{u₁ v₁} C]

def parallel_pair_functor {α β : C} (f g : α ⟶ β) : walking_parallel_pair.{v₁} ⥤ C :=
{ obj := λ X, match X with
              | _1 := α
              | _2 := β
              end,
  map' := λ X Y h, match X, Y, h with
                  | _1, _1, _ := 𝟙 α
                  | _2, _2, _ := 𝟙 β
                  | _1, _2, L := f
                  | _1, _2, R := g
                  end, }
end

end category_theory.walking

