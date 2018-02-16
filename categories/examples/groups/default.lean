-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import ...functor
import ...types
import tactic.finish
import algebra.group

namespace categories.examples.groups


open categories

universe u₁

definition Group := Σ α : Type u₁, group α

instance group_from_Group (G : Group) : group G.1 := G.2

meta def is_group_hom_obviously := `[unfold is_group_hom, obviously]

structure GroupHomomorphism (G H : Group.{u₁}) : Type (u₁+1) := -- Notice that we push this up one universe level, because our categories expect Obj and Hom at the same universe level.
  (map: G.1 → H.1)
  (is_group_hom : by exactI is_group_hom map . is_group_hom_obviously) -- we need `by exactI` here to get the group instances.

instance GroupHomomorphism_to_map {G H : Group} : has_coe_to_fun (GroupHomomorphism G H) :=
{F   := λ f, Π x : G.1, H.1,
  coe := GroupHomomorphism.map}

@[simp] lemma GroupHomomorphism.is_group_hom_lemma (G H : Group) (f : GroupHomomorphism G H) (x y : G.1) : by exactI f(x * y) = f(x) * f(y) := -- again, we need to get the group instances.
begin
  dsimp {unfold_reducible := tt, md := semireducible},
  erw f.is_group_hom,
  refl,
end

#print GroupHomomorphism.is_group_hom_lemma -- yuck, the type is
-- ∀ (G H : Group) (f : GroupHomomorphism G H) (x y : G.fst),
--  id (λ (G H : Group) (f : GroupHomomorphism G H) (x y : G.fst), ⇑f (x * y) = ⇑f x * ⇑f y) G H f x y

definition GroupHomomorphism.identity (G : Group) : GroupHomomorphism G G := ⟨ id ⟩

definition GroupHomomorphism.composition
  {G H K : Group}
  (f: GroupHomomorphism G H) (g: GroupHomomorphism H K) : GroupHomomorphism G K :=
{
  map := λ x, g (f x),
  is_group_hom := begin
                    unfold is_group_hom, 
                    dsimp, 
                    intros, 
                    -- we can't just say `simp`, and have GroupHomomorphism.is_group_hom_lemma finish, because its type is gross because of the exactI.
                    have h := GroupHomomorphism.is_group_hom_lemma, 
                    dsimp at h, 
                    rw h, 
                    rw h,
                  end
}

lemma GroupHomomorphism_pointwise_equality
  {G H : Group}
  (f g : GroupHomomorphism G H)
  (w : ∀ x : G.1, f x = g x) : f = g :=
begin
    induction f with fc,
    induction g with gc,
    have hc : fc = gc := funext w,
    subst hc
end

instance CategoryOfGroups : category Group := {
    Hom := GroupHomomorphism,
    identity := GroupHomomorphism.identity,
    compose  := @GroupHomomorphism.composition
}

open categories.functor
open categories.types

definition ForgetfulFunctor_Groups_to_Types : Functor Group (Type u₁) :=
{
  onObjects     := λ s, s.1,
  onMorphisms   := λ s t, λ f, ulift.up f.map, -- we need this ulift because there's only one universe level in the category of types.
}

end categories.examples.groups
