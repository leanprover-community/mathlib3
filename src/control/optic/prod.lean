/-
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/
import control.traversable

/-!
Some definitions for optics on products.
-/

universes u v
variables {A B C D S T X Y : Type}

def prod.elim {A B C} : (A → B → C) → A × B → C
| f (a,b) := f a b

def prod.intro {A B C} : (C → A) → (C → B) → C → (A × B)
| f g c := (f c, g c)

def prod.delta {A} : A → A × A
| a := (a,a)

def sum.codelta {A} : A ⊕ A → A
| (sum.inl a) := a
| (sum.inr a) := a

/-- `square A := A × A` -/
def prod.square (A : Type u) := A × A

namespace prod.square

open prod

instance : functor square := {map := λ A B f, prod.map f f}

instance [has_repr A] : has_repr (square A) := prod.has_repr

def traverse {M} [applicative M] {A B : Type} (f : A → M B) : square A → M (square B)
| (a₁, a₂) := pure prod.mk <*> f a₁ <*> f a₂

instance is_trav : traversable square :=
{ traverse := @traverse }

end prod.square
