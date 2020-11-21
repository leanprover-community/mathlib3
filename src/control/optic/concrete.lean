/-
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/
import control.profunctor
import data.vector
import data.vector2
import tactic

/-!
Definitions of concrete lenses (as opposed to profunctor definitions).
-/

namespace control.optic.concrete

open control
open control.profunctor

variables {A B C S T : Type}

structure lens (A B S T : Type) :=
(view : S → A)
(update : B → S → T)

namespace lens
  protected def id : lens A B A B :=
  ⟨λ a, a, λ b a, b⟩

  instance : profunctor (lens A B) :=
  { dimap := λ S T U V ts uv ⟨v,u⟩, ⟨v ∘ ts, λ b t, uv $ u b (ts t)⟩}

  instance : strong (lens A B) :=
  { first := λ X Y C ⟨v,u⟩, ⟨λ ⟨x,c⟩, v x , λ b ⟨x,c⟩, ⟨u b x,c⟩⟩
  , second := λ X Y C ⟨v,u⟩, ⟨λ ⟨c,x⟩, v x , λ b ⟨c,x⟩, ⟨c, u b x⟩⟩
  }
end lens

/-- Concrete prism. -/
structure prism (A B S T : Type) :=
(get : S → T ⊕ A)
(review : B → T)

namespace prism
  def preview (p : prism A B S T) (s : S) : option A :=
  sum.elim (λ _, none) some $ p.get s

  protected def id : prism A B A B :=
  ⟨λ a, sum.inr a, λ b, b⟩

  instance : profunctor (prism A B) :=
  { dimap := λ S T U V ts uv p, ⟨λ t, sum.map uv id $ p.get $ ts t, uv ∘ p.review⟩}

  instance : choice (prism A B) :=
  { left := λ S T U ⟨g,s⟩, ⟨sum.elim (sum.map (sum.inl) id ∘ g) (sum.inl ∘ sum.inr), sum.inl ∘ s⟩
  , right := λ S T U ⟨g,s⟩, ⟨sum.elim (sum.inl ∘ sum.inl) (sum.map sum.inr id ∘ g), sum.inr ∘ s⟩
  }
end prism

structure traversal0 (A B S T : Type) :=
(get    : S → T ⊕ A)
(review : S → B → T)

/-- The representation functor for `traversal`. -/
structure fun_list (A B T : Type) :=
(n : nat)
(get : vector A n)
(out : vector B n → T)

namespace fun_list
  def vector.split {n m : nat} : vector A (n + m) → vector A n × vector A m :=
  begin
    intro bs,
    let b1 := vector.take n bs,
    let b2 := vector.drop n bs,
    have : min n (n + m) = n,
      refine le_antisymm (min_le_left _ _) (le_min (le_refl _) (le_add_right (le_refl _))),
    rw this at b1,
    have : (n + m) - n = m,
      rw [add_comm, nat.add_sub_assoc (le_refl _)], simp,
    rw this at b2,
    exact (b1, b2)
  end

  instance : functor (fun_list A B) :=
  { map := λ X Y xy ⟨n,a,b⟩, ⟨n,a, xy ∘ b⟩}

  instance : applicative (fun_list A B) :=
  { pure := λ T t, ⟨0, vector.nil, λ _, t⟩
  , seq := λ X Y ⟨n, a1, bxy⟩ ⟨m, a2, bx⟩,
      ⟨ n + m
      , vector.append a1 a2
      , λ bs, prod.cases_on (vector.split bs) $ λ b1 b2, bxy b1 $ bx b2
      ⟩
  }
end fun_list

/-- A concrete definition of a traversal. -/
def traversal (A B S T : Type) := star (fun_list A B) S T

namespace traversal
  instance : profunctor (traversal A B) := star.is_profunctor
  instance : strong (traversal A B) := star.is_strong
  instance : choice (traversal A B) := star.is_choice
  instance : representable (traversal A B) := star.is_representable
  instance : traversing (traversal A B) := {}
  protected def id : traversal A B A B :=
  λ a, fun_list.mk 1 (vector.cons a $ vector.nil) (vector.head)
end traversal

def setter (A B S T : Type) :=
(A → B) → (S → T)

namespace setter
  instance : affine (setter A B) :=
  { dimap := λ U V W X vu wx h ab v, wx $ h ab $ vu v
  , left := λ U V W s ab uw, sum.map (s ab) id uw
  , right := λ U V W s ab uw, sum.map id (s ab) uw
  , first := λ U V W s ab uw, prod.map (s ab) id uw
  , second := λ U V W s ab uw, prod.map id (s ab) uw
  }

  instance : mapping (setter A B) :=
  { Rep := λ X, (A → B) → X
  , sieve := λ X Y s x ab, s ab x
  , tabulate := λ X Y s ab x, s x ab
  , a := { pure := λ A a ab, a
         , seq := λ X Y xy x ab, xy ab $ x ab
         }
  , d := ⟨λ F ftor X frx ab, @functor.map F ftor _ _ (λ (j : (A → B) → X), j ab) frx⟩
  }
end setter

def grate (A B S T : Type) := ((S → A) → B) → T

namespace grate
  protected def id : grate A B A B
  | sab := sab _root_.id

  instance : closed (grate A B) :=
  {close := λ X Y S g f s, g $ λ i, f $ λ j, i $ j s }

  instance : profunctor (grate A B) :=
  {dimap := λ X Y S T yx st g yab, st $ g $ λ xa, yab $ xa ∘ yx}
end grate

end control.optic.concrete
