/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Jannis Limperg
-/

/-!
# Monadic instances for `ulift` and `plift`

In this file we define `monad` and `is_lawful_monad` instances on `plift` and `ulift`. -/

universes u v

namespace plift

variables {α : Sort u} {β : Sort v}

/-- Functorial action. -/
protected def map (f : α → β) (a : plift α) : plift β :=
plift.up (f a.down)

@[simp] lemma map_up (f : α → β) (a : α) : (plift.up a).map f = plift.up (f a) := rfl

/-- Embedding of pure values. -/
@[simp] protected def pure : α → plift α := up

/-- Applicative sequencing. -/
protected def seq (f : plift (α → β)) (x : plift α) : plift β :=
plift.up (f.down x.down)

@[simp] lemma seq_up (f : α → β) (x : α) : (plift.up f).seq (plift.up x) = plift.up (f x) := rfl

/-- Monadic bind. -/
protected def bind (a : plift α) (f : α → plift β) : plift β := f a.down

@[simp] lemma bind_up (a : α) (f : α → plift β) : (plift.up a).bind f = f a := rfl

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
protected def map (f : α → β) (a : ulift α) : ulift β :=
ulift.up (f a.down)

@[simp] lemma map_up (f : α → β) (a : α) : (ulift.up a).map f = ulift.up (f a) := rfl

/-- Embedding of pure values. -/
@[simp] protected def pure : α → ulift α := up

/-- Applicative sequencing. -/
protected def seq (f : ulift (α → β)) (x : ulift α) : ulift β :=
ulift.up (f.down x.down)

@[simp] lemma seq_up (f : α → β) (x : α) : (ulift.up f).seq (ulift.up x) = ulift.up (f x) := rfl

/-- Monadic bind. -/
protected def bind (a : ulift α) (f : α → ulift β) : ulift β := f a.down

@[simp] lemma bind_up (a : α) (f : α → ulift β) : (ulift.up a).bind f = f a := rfl

instance : monad ulift :=
{ map := @ulift.map,
  pure := @ulift.pure,
  seq := @ulift.seq,
  bind := @ulift.bind }

instance : is_lawful_functor ulift :=
{ id_map := λ α ⟨x⟩, rfl,
  comp_map := λ α β γ g h ⟨x⟩, rfl }

instance : is_lawful_applicative ulift :=
{ to_is_lawful_functor := ulift.is_lawful_functor,
  pure_seq_eq_map := λ α β g ⟨x⟩, rfl,
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
