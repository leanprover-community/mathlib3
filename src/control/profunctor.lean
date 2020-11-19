/-
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/
import control.functor control.traversable

namespace control

class profunctor (P : Type → Type → Type) :=
(dimap {A A' B B'} : (A' → A) → (B → B') → P A B → P A' B')

class lawful_profunctor (P : Type → Type → Type) extends profunctor P :=
(did : ∀ {A B}, dimap (@id A) (@id B) = id)
(dcomp : ∀ {A₀ A₁ A₂} (a₂₁ : A₂ → A₁) (a₁₀ : A₁ → A₀)
           {B₀ B₁ B₂} (b₀₁ : B₀ → B₁) (b₁₂ : B₁ → B₂),
             dimap (a₁₀ ∘ a₂₁) (b₁₂ ∘ b₀₁)  = dimap a₂₁ b₁₂ ∘ dimap a₁₀ b₀₁)

namespace profunctor

class strong (P : Type → Type → Type) :=
(first  {A B} (C) : P A B → P (A × C) (B × C))
(second {A B} (C) : P A B → P (C × A) (C × B))

@[reducible] def first := @strong.first
@[reducible] def second := @strong.second

class costrong (P : Type → Type → Type) :=
(unfirst  {A B} (C : Type) : P (A × C) (B × C) → P A B)
(unsecond {A B} (C : Type) : P (C × A) (C × B) → P A B)

class choice (P : Type → Type → Type) :=
(left  {A B} (C) : P A B → P (A ⊕ C) (B ⊕ C))
(right {A B} (C) : P A B → P (C ⊕ A) (C ⊕ B))

@[reducible] def left := @choice.left
@[reducible] def right := @choice.right

class closed (P : Type → Type → Type) :=
(close {A B : Type} : ∀ (X : Type), P A B → P (X → A) (X → B))

/-- A profunctor is __affine__ when it is strong and choice. That is, it plays well with `⊕` and `×`. -/
class affine (P : Type → Type → Type) extends profunctor P, strong P, choice P

class monoidal (P : Type → Type → Type) :=
(par {A B C D} : P A B → P C D → P (A × C) (B × D))
(empty : P unit unit)

class distributive (R : Type → Type) :=
(dist : ∀ ⦃F⦄ [functor F] {A}, F (R A) → R (F A))

class representable (P : Type → Type → Type) :=
(Rep : Type → Type)
(sieve    {A B} : P A B        → (A → Rep B))
(tabulate {A B} : (A → Rep B) → P A B       )

class contrafunctor (F : Type → Type) :=
(comap : ∀ (A B : Type), (B → A) → F A → F B)

class coerce_r (P : Type → Type → Type) :=
(asdf : ∀ A, contrafunctor (P A))

/-- The representation functor of a representable profunctor-/
def Rep := @representable.Rep

instance (P : Type → Type → Type) [representable P] [functor (representable.Rep P)] : profunctor P :=
{dimap := λ A B C D ba cd pac, representable.tabulate $ (λ b, cd <$> representable.sieve pac (ba b))}

/-- A profunctor `P` is __traversing__ when it is representable with an applicative functor. -/
class traversing (P : Type → Type → Type) extends (representable P) :=
[a : applicative Rep]

/-- A profunctor `P` is __mapping__ when it is representable with a distributive functor. -/
class mapping (P : Type → Type → Type) extends (traversing P) :=
[d : distributive Rep]

/-- `star F A B := A → F B` -/
def star (F : Type → Type) (A B : Type) := A → F B

namespace star
  variables {F : Type → Type} [functor F]

  instance is_profunctor : profunctor (star F) :=
  { dimap := λ A B C D f g h a, g <$> (h $ f a) }

  instance is_choice [has_pure F]: choice (star F) :=
  { left :=  λ A B C afb ac, match ac with | (sum.inl a) := sum.inl <$> afb a | (sum.inr c) := sum.inr <$> pure c end
  , right := λ A B C afb ca, match ca with | (sum.inr a) := sum.inr <$> afb a | (sum.inl c) := sum.inl <$> pure c end
  }

  instance is_strong : strong (star F) :=
  { first  := λ A B C afb ⟨a,c⟩, (λ b, prod.mk b c) <$> afb a
  , second := λ A B C afb ⟨c,a⟩, (λ b, prod.mk c b) <$> afb a
  }

  instance is_representable : representable (star F) :=
  { Rep := F, sieve := λ A B, id, tabulate := λ A B, id }

  @[simp] lemma rep_star : Rep (star F) = F := rfl

  instance is_affine [has_pure F] : affine (star F) := {}
  instance is_traversing [applicative F] : traversing (star F) := {}
end star

/-- `costar F A B = F A → B` -/
def costar (F : Type → Type) (A B : Type) := F A → B

namespace costar
  variables {F : Type → Type} [functor F]
  instance : profunctor (costar F) :=
  { dimap := λ A B X Y ba xy cs fb, xy $ cs $ functor.map ba fb }

  instance : closed (costar F) :=
  { close := λ A B X fab fxa x, fab $ (λ (f : X → A), f x) <$> fxa }
end costar

namespace function
  instance is_lawful : lawful_profunctor (→) :=
  { dimap := λ A B C D f g h, g ∘ h ∘ f
  , did := λ _ _, rfl
  , dcomp := λ _ _ _ _ _ _ _ _ _ _, rfl
  }

  instance is_strong : strong (→) :=
  { first  := λ A B C f, prod.map f id
  , second := λ A B C f, prod.map id f
  }

  instance is_choice : choice (→) :=
  { left  := λ A B C f, sum.map f id
  , right := λ A B C f, sum.map id f
  }

  instance is_closed : closed (→) :=
  { close := λ A B X ab xa x, ab $ xa $ x}

  instance is_representable : representable (→) :=
  { Rep := id, sieve := λ _ _, id, tabulate := λ _ _, id }

  /-- `A → _` is a functor. -/
  instance is_functor {A : Type} : functor ((→) A) :=
  {map := λ X Y f g a, f $ g $ a}

  def dist_reader {R : Type → Type} [distributive R] {A B : Type} : (A → R B) → R (A → B)
  | f := @distributive.dist R _ ((→) A) function.is_functor _ f

end function

instance applicative_rep_of_traversing {P : Type → Type → Type} [traversing P] : applicative (Rep P) :=
traversing.a

instance functor_rep_of_traversing {P : Type → Type → Type} [traversing P] : functor (Rep P) :=
by apply_instance

instance dist_rep_of_mapping {P : Type → Type → Type} [mapping P] : distributive (Rep P) :=
mapping.d

instance applicative_rep_of_mapping {P : Type → Type → Type} [mapping P] : applicative (Rep P) :=
mapping.to_traversing.a

end profunctor

end control
