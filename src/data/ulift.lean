/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Jannis Limperg

Facts about `ulift` and `plift`.
-/

universes u v

namespace plift

variables {α : Sort u} {β : Sort v}

/-- Functorial action. -/
@[simp] protected def map (f : α → β) : plift α → plift β
| (up a) := up (f a)

/-- Embedding of pure values. -/
@[simp] protected def pure : α → plift α := up

/-- Applicative sequencing. -/
@[simp] protected def seq : plift (α → β) → plift α → plift β
| (up f) (up a) := up (f a)

/-- Monadic bind. -/
@[simp] protected def bind : plift α → (α → plift β) → plift β
| (up a) f := f a

instance : monad plift :=
{ map := @plift.map,
  pure := @plift.pure,
  seq := @plift.seq,
  bind := @plift.bind }

instance : is_lawful_functor plift :=
{ id_map := λ α ⟨x⟩, rfl,
  comp_map := λ α β γ g h ⟨x⟩, rfl }

instance : is_lawful_applicative plift :=
{ pure_seq_eq_map := λ α β g ⟨x⟩, rfl,
  map_pure := λ α β g x, rfl,
  seq_pure := λ α β ⟨g⟩ x, rfl,
  seq_assoc := λ α β γ ⟨x⟩ ⟨g⟩ ⟨h⟩, rfl }

instance : is_lawful_monad plift :=
{ bind_pure_comp_eq_map := λ α β f ⟨x⟩, rfl,
  bind_map_eq_seq := λ α β ⟨a⟩ ⟨b⟩, rfl,
  pure_bind := λ α β x f, rfl,
  bind_assoc := λ α β γ ⟨x⟩ f g, rfl }

@[simp] lemma rec.constant {α : Sort u} {β : Type v} (b : β) :
  @plift.rec α (λ _, β) (λ _, b) = λ _, b :=
funext (λ x, plift.cases_on x (λ a, eq.refl (plift.rec (λ a', b) {down := a})))

end plift


namespace ulift

variables {α : Type u} {β : Type v}

/-- Functorial action. -/
@[simp] protected def map (f : α → β) : ulift α → ulift β
| (up a) := up (f a)

/-- Embedding of pure values. -/
@[simp] protected def pure : α → ulift α := up

/-- Applicative sequencing. -/
@[simp] protected def seq : ulift (α → β) → ulift α → ulift β
| (up f) (up a) := up (f a)

/-- Monadic bind. -/
@[simp] protected def bind : ulift α → (α → ulift β) → ulift β
| (up a) f := up (down (f a))
-- The `up ∘ down` gives us more universe polymorphism than simply `f a`.

instance : monad ulift :=
{ map := @ulift.map,
  pure := @ulift.pure,
  seq := @ulift.seq,
  bind := @ulift.bind }

instance : is_lawful_functor ulift :=
{ id_map := λ α ⟨x⟩, rfl,
  comp_map := λ α β γ g h ⟨x⟩, rfl }

instance : is_lawful_applicative ulift :=
{ pure_seq_eq_map := λ α β g ⟨x⟩, rfl,
  map_pure := λ α β g x, rfl,
  seq_pure := λ α β ⟨g⟩ x, rfl,
  seq_assoc := λ α β γ ⟨x⟩ ⟨g⟩ ⟨h⟩, rfl }

instance : is_lawful_monad ulift :=
{ bind_pure_comp_eq_map := λ α β f ⟨x⟩, rfl,
  bind_map_eq_seq := λ α β ⟨a⟩ ⟨b⟩, rfl,
  pure_bind := λ α β x f,
    by { dsimp only [bind, pure, ulift.pure, ulift.bind], cases (f x), refl },
  bind_assoc := λ α β γ ⟨x⟩ f g,
    by { dsimp only [bind, pure, ulift.pure, ulift.bind], cases (f x), refl } }

@[simp] lemma rec.constant {α : Type u} {β : Sort v} (b : β) :
  @ulift.rec α (λ _, β) (λ _, b) = λ _, b :=
funext (λ x, ulift.cases_on x (λ a, eq.refl (ulift.rec (λ a', b) {down := a})))

end ulift
