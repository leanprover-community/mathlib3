-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..category
import ..isomorphism

namespace categories.types

open categories
open categories.isomorphism

universes u v

instance CategoryOfTypes : category.{u+1} (Type u) := {
    Hom := λ a b, ulift.{u+1} (a → b),
    identity := λ a, ulift.up id,
    compose  := λ _ _ _ f g, ulift.up (g.down ∘ f.down)
}

lemma ulift_equal {α : Type v}
  (X Y : ulift.{u v} α)
  (w : X.down = Y.down) : X = Y :=
  begin
    induction X,
    induction Y,
    obviously
  end

definition Bijection (α β : Type u) := Isomorphism α β 

@[simp] definition Bijection.witness_1 {α β : Type u} (iso : Bijection α β) (x : α) : iso.inverse.down (iso.morphism.down x) = x :=
begin
  have p := iso.witness_1, 
  have p' := congr_arg ulift.down p,
  obviously,
end
@[simp] definition Bijection.witness_2 {α β : Type u} (iso : Bijection α β) (x : β) : iso.morphism.down (iso.inverse.down x) = x :=
begin
  have p := iso.witness_2,
  have p' := congr_arg ulift.down p,
  obviously,
end

-- TODO the @s are unpleasant here
@[simp] definition is_Isomorphism_in_Types.witness_1 {α β : Type u} (f : α → β) (h : @is_Isomorphism _ _ α β (ulift.up f)) (x : α) : h.inverse.down (f x) = x :=
begin
  have p := h.witness_1, 
  have p' := congr_arg ulift.down p,
  obviously,
end
@[simp] definition is_Isomorphism_in_Types.witness_2 {α β : Type u} (f : α → β) (h : @is_Isomorphism _ _ α β (ulift.up f)) (x : β) : f (h.inverse.down x) = x :=
begin
  have p := h.witness_2,
  have p' := congr_arg ulift.down p,
  obviously,
end


end categories.types
