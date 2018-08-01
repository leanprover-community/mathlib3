/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Instances for identity and composition functors
-/

import category.functor

universe variables u v w

section lemmas

open function

variables {f : Type u → Type v}
variables [applicative f] [is_lawful_applicative f]
variables {α β γ σ : Type u}

attribute [functor_norm] seq_assoc pure_seq_eq_map map_pure seq_map_assoc map_seq

lemma applicative.map_seq_map (g : α → β → γ) (h : σ → β) (x : f α) (y : f σ) :
  (g <$> x) <*> (h <$> y) = (flip (∘) h ∘ g) <$> x <*> y :=
by simp [flip] with functor_norm

lemma applicative.pure_seq_eq_map' (g : α → β) :
  (<*>) (pure g : f (α → β)) = (<$>) g :=
by ext; simp with functor_norm

end lemmas

namespace comp

open function (hiding comp)
open functor

variables {f : Type u → Type w} {g : Type v → Type u}

variables [applicative f] [applicative g]

protected def seq  {α β : Type v} : comp f g (α → β) → comp f g α → comp f g β
| ⟨h⟩ ⟨x⟩ := ⟨has_seq.seq <$> h <*> x⟩

instance : has_pure (comp f g) :=
⟨λ _ x, ⟨pure $ pure x⟩⟩

instance : has_seq (comp f g) :=
⟨λ _ _ f x, comp.seq f x⟩

@[simp]
protected lemma run_pure {α : Type v} :
  ∀ x : α, (pure x : comp f g α).run = pure (pure x)
| _ := rfl

@[simp]
protected lemma run_seq {α β : Type v} :
  ∀ (h : comp f g (α → β)) (x : comp f g α),
  (h <*> x).run = (<*>) <$> h.run <*> x.run
| ⟨_⟩ ⟨_⟩ := rfl

variables [is_lawful_applicative f] [is_lawful_applicative g]
variables {α β γ : Type v}

lemma map_pure (h : α → β) (x : α) : (h <$> pure x : comp f g β) = pure (h x) :=
by ext; simp

lemma seq_pure (h : comp f g (α → β)) (x : α) :
  h <*> pure x = (λ g : α → β, g x) <$> h :=
by ext; simp [(∘)] with functor_norm

lemma seq_assoc (x : comp f g α) (h₀ : comp f g (α → β)) (h₁ : comp f g (β → γ)) :
   h₁ <*> (h₀ <*> x) = (@function.comp α β γ <$> h₁) <*> h₀ <*> x :=
by ext; simp [(∘)] with functor_norm

lemma pure_seq_eq_map (h : α → β)  (x : comp f g α) :
  pure h <*> x = h <$> x :=
by ext; simp [applicative.pure_seq_eq_map'] with functor_norm

instance {f : Type u → Type w} {g : Type v → Type u}
  [applicative f] [applicative g] :
  applicative (comp f g) :=
{ map := @comp.map f g _ _,
  seq := @comp.seq f g _ _,
  ..comp.has_pure }

instance {f : Type u → Type w} {g : Type v → Type u}
  [applicative f] [applicative g]
  [is_lawful_applicative f] [is_lawful_applicative g] :
  is_lawful_applicative (comp f g) :=
{ pure_seq_eq_map := @comp.pure_seq_eq_map f g _ _ _ _,
  map_pure := @comp.map_pure f g _ _ _ _,
  seq_pure := @comp.seq_pure f g _ _ _ _,
  seq_assoc := @comp.seq_assoc f g _ _ _ _ }

end comp
open functor

@[functor_norm]
lemma comp.seq_mk {α β : Type w}
  {f : Type u → Type v} {g : Type w → Type u}
  [applicative f] [applicative g]
  (h : f (g (α → β))) (x : f (g α)) :
  comp.mk h <*> comp.mk x = comp.mk (has_seq.seq <$> h <*> x) := rfl
