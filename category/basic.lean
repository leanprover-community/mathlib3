/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Extends the theory on functors, applicatives and monads.
-/

universes u v w x y
variables {α β γ : Type u}

section monad
variables {m : Type u → Type v} [monad m] [is_lawful_monad m]

lemma map_bind (x : m α) {g : α → m β} {f : β → γ} : f <$> (x >>= g) = (x >>= λa, f <$> g a) :=
by simp [bind_assoc, (∘), (bind_pure_comp_eq_map _ _ _).symm]

lemma seq_bind_eq (x : m α) {g : β → m γ} {f : α → β} : (f <$> x) >>= g = (x >>= g ∘ f) :=
show bind (f <$> x) g = bind x (g ∘ f),
by rw [← bind_pure_comp_eq_map, bind_assoc]; simp [pure_bind]

lemma seq_eq_bind_map {x : m α} {f : m (α → β)} : f <*> x = (f >>= (<$> x)) :=
(bind_map_eq_seq m f x).symm

end monad
