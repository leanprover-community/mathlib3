/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Monad encapsulating continuation passing programming style, similar to
Haskell's `Cont`, `ContT` and `MonadCont`:
http://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html
-/

import tactic.interactive

universes u v w

structure monad_cont.label (α : Type w) (m : Type u → Type v) (β : Type u) :=
(apply : α → m β)

def monad_cont.goto {α β} {m : Type u → Type v} (f : monad_cont.label α m β) (x : α) := f.apply x

class monad_cont (m : Type u → Type v)
extends monad m :=
(call_cc : Π {α β}, ((monad_cont.label α m β) → m α) → m α)

open monad_cont

class is_lawful_monad_cont (m : Type u → Type v) [monad_cont m]
extends is_lawful_monad m :=
(call_cc_bind_right {α ω γ} (cmd : m α) (next : (label ω m γ) → α → m ω) :
  call_cc (λ f, cmd >>= next f) = cmd >>= λ x, call_cc (λ f, next f x))
(call_cc_bind_left {α} (β) (x : α) (dead : label α m β → β → m α) :
  call_cc (λ f : label α m β, goto f x >>= dead f) = pure x)
(call_cc_dummy {α β} (dummy : m α) :
  call_cc (λ f : label α m β, dummy) = dummy)

export is_lawful_monad_cont

def cont_t (r : Type u) (m : Type u → Type v) (α : Type w) := (α → m r) → m r

namespace cont_t

export monad_cont (label goto)

variables {r : Type u} {m : Type u → Type v} {α β γ ω : Type w}

def run : cont_t r m α → (α → m r) → m r := id

def map (f : m r → m r) (x : cont_t r m α) : cont_t r m α := f ∘ x

lemma run_cont_t_map_cont_t (f : m r → m r) (x : cont_t r m α) :
  run (map f x) = f ∘ run x := rfl

def with_cont_t (f : (β → m r) → α → m r) (x : cont_t r m α) : cont_t r m β :=
λ g, x $ f g

lemma run_with_cont_t (f : (β → m r) → α → m r) (x : cont_t r m α) :
  run (with_cont_t f x) = run x ∘ f := rfl

instance : monad (cont_t r m) :=
{ pure := λ α x f, f x,
  bind := λ α β x f g, x $ λ i, f i g }

instance : is_lawful_monad (cont_t r m) :=
{ id_map := by { intros, refl },
  pure_bind := by { intros, ext, refl },
  bind_assoc := by { intros, ext, refl } }

instance [monad m] : has_monad_lift m (cont_t r m) :=
{ monad_lift := λ a x f, x >>= f }

lemma monad_lift_bind [monad m] [is_lawful_monad m] {α β} (x : m α) (f : α → m β) :
  (monad_lift (x >>= f) : cont_t r m β) = monad_lift x >>= monad_lift ∘ f :=
by { ext, simp only [monad_lift,has_monad_lift.monad_lift,(∘),(>>=),bind_assoc,id.def] }

instance : monad_cont (cont_t r m) :=
{ call_cc := λ α β f g, f ⟨λ x h, g x⟩ g }

instance : is_lawful_monad_cont (cont_t r m) :=
{ call_cc_bind_right := by intros; ext; refl,
  call_cc_bind_left := by intros; ext; refl,
  call_cc_dummy := by intros; ext; refl }

end cont_t
