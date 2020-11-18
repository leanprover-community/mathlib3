import control.profunctor
import data.vector

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

/-- An inefficient, concrete definition of a traversal. -/
def traversal (A B S T : Type) :=
S → Σ (n : nat), (vector A n) × (vector B n → T)

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
