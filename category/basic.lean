/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Extends the theory on functors, applicatives and monads.
-/

universes u v w x y
variables {α β γ : Type u}

section applicative
variables {f : Type u → Type v} [applicative f]

lemma pure_seq_eq_map : ∀ {α β : Type u} (g : α → β) (x : f α), pure g <*> x = g <$> x :=
@applicative.pure_seq_eq_map f _

end applicative

section monad
variables {m : Type u → Type v} [monad m]

lemma map_bind (x : m α) {g : α → m β} {f : β → γ} : f <$> (x >>= g) = (x >>= λa, f <$> g a) :=
by simp [monad.bind_assoc, (∘), (monad.bind_pure_comp_eq_map _ _ _).symm]

lemma seq_bind_eq (x : m α) {g : β → m γ} {f : α → β} : (f <$> x) >>= g = (x >>= g ∘ f) :=
show bind (f <$> x) g = bind x (g ∘ f),
by rw [←monad.bind_pure_comp_eq_map, monad.bind_assoc]; simp [monad.pure_bind]

lemma seq_eq_bind_map {x : m α} {f : m (α → β)} : f <*> x = (f >>= (<$> x)) :=
(monad.bind_map_eq_seq m f x).symm

lemma bind_assoc : ∀ {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),
  x >>= f >>= g = x >>= λ x, f x >>= g :=
@monad.bind_assoc m _

end monad
