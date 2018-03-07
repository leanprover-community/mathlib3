/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Instances for identity and composition functors
-/

import category.functor

universe variables u v w u' v' w'

section lemmas

open function

variables {f : Type u → Type v}
variables [applicative f] [is_lawful_applicative f]

attribute [norm] seq_assoc pure_seq_eq_map map_pure seq_map_assoc map_seq

lemma applicative.map_seq_map {α β γ σ : Type u} (g : α → β → γ) (h : σ → β) (x : f α) (y : f σ) :
  (g <$> x) <*> (h <$> y) = (flip comp h ∘ g) <$> x <*> y :=
by simp [flip] with norm

end lemmas

instance : applicative id :=
{ pure := @id,
  seq := λ α β f, f }

instance : is_lawful_applicative id :=
by refine { .. }; intros; refl

namespace comp

open function (hiding comp)
open functor

variables {f : Type u → Type u'} {g : Type v → Type u}

variables [applicative f] [applicative g]

def seq  {α β : Type v} : comp f g (α → β) → comp f g α → comp f g β
| ⟨h⟩ ⟨x⟩ := ⟨has_seq.seq <$> h <*> x⟩

instance : has_pure (comp f g) :=
⟨λ _ x, ⟨pure $ pure x⟩⟩

local infix ` <$> ` := comp.map
local infix ` <*> ` := seq

variables [is_lawful_applicative f] [is_lawful_applicative g]
variables {α β γ : Type v}

lemma map_pure (h : α → β) (x : α) : (h <$> pure x : comp f g β) = pure (h x) :=
begin
  unfold has_pure.pure function.comp comp.map,
  apply congr_arg,
  rw [map_pure, map_pure],
end

lemma seq_pure (h : comp f g (α → β)) (x : α) :
  h <*> pure x = (λ g : α → β, g x) <$> h :=
begin
  cases h with h,
  unfold comp.map has_pure.pure comp.seq function.comp,
  apply congr_arg,
  rw [seq_pure, ← comp_map],
  apply congr_fun, apply congr_arg,
  apply funext, intro y,
  unfold function.comp,
  apply seq_pure
end

lemma seq_assoc : ∀ (x : comp f g α) (h₀ : comp f g (α → β)) (h₁ : comp f g (β → γ)),
   h₁ <*> (h₀ <*> x) = (@function.comp α β γ <$> h₁) <*> h₀ <*> x
| ⟨x⟩ ⟨h₀⟩ ⟨h₁⟩ :=
by simp! [(∘),flip] with norm

lemma pure_seq_eq_map (h : α → β) : ∀ (x : comp f g α), pure h <*> x = h <$> x
| ⟨x⟩ :=
begin
  simp! with norm,
  congr, funext, simp with norm,
end

instance {f : Type u → Type u'} {g : Type v → Type u}
  [applicative f] [applicative g] :
  applicative (comp f g) :=
{ map := @comp.map f g _ _,
  seq := @comp.seq f g _ _,
  ..comp.has_pure }

instance {f : Type u → Type u'} {g : Type v → Type u}
  [applicative f] [applicative g]
  [is_lawful_applicative f] [is_lawful_applicative g] :
  is_lawful_applicative (comp f g) :=
{ pure_seq_eq_map := @comp.pure_seq_eq_map f g _ _ _ _,
  map_pure := @comp.map_pure f g _ _ _ _,
  seq_pure := @comp.seq_pure f g _ _ _ _,
  seq_assoc := @comp.seq_assoc f g _ _ _ _ }

end comp
open functor

@[norm]
lemma comp.seq_mk {α β : Type u'}
  {f : Type u → Type v} {g : Type u' → Type u}
  [applicative f] [applicative g]
  (h : f (g (α → β))) (x : f (g α)) :
  comp.mk h <*> comp.mk x = comp.mk (has_seq.seq <$> h <*> x) := rfl
