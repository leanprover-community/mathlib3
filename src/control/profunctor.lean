/-
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/

import control.functor
import control.traversable
import control.bifunctor

/-!
Functors `Typeᵒᵖ → Type → Type` and various typeclasses based on them.
c.f. control.bifunctor
-/

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

/-- A profunctor is __affine__ when it is strong and choice.
That is, it plays well with `⊕` and `×`. -/
class affine (P : Type → Type → Type) extends profunctor P, strong P, choice P

class monoidal (P : Type → Type → Type) :=
(par {A B C D} : P A B → P C D → P (A × C) (B × D))
(empty : P unit unit)

class distributive (R : Type → Type) :=
(dist : ∀ ⦃F⦄ [functor F] {A}, F (R A) → R (F A))

instance id_dist : distributive id := { dist := λ _ _ _, id}

/-- A profunctor is representable if `P A B` is iso to `A → R B`. -/
class representable (P : Type → Type → Type) :=
(Rep : Type → Type)
(sieve    {A B} : P A B        → (A → Rep B))
(tabulate {A B} : (A → Rep B) → P A B       )

/-- A functor but `map` is reversed. That is, `map : (B → A) → F A → F B`.
A functor `Typeᵒᵖ → Type`. -/
class contrafunctor (F : Type → Type) :=
(comap : ∀ (A B : Type), (B → A) → F A → F B)

class coerce_r (P : Type → Type → Type) :=
(asdf : ∀ A, contrafunctor (P A))

/-- The representation functor of a representable profunctor-/
def Rep := @representable.Rep

variables {P : Type → Type → Type}

def representable.lift [representable P] {A B S T : Type}
  (f : (A → Rep P B) → S → Rep P T) : P A B → P S T
| pab := representable.tabulate $ f $ representable.sieve pab

instance (P : Type → Type → Type) [representable P] [rf : functor (representable.Rep P)]
  : profunctor P :=
{dimap := λ A B C D ba cd, representable.lift $ (λ pac b, @functor.map _ rf _ _ cd $ pac (ba b))}

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
  { left :=  λ A B C afb, sum.fmap afb pure
  , right := λ A B C afb, sum.fmap pure afb
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

def representable.star_lift [representable P] {A B S T : Type}
  (f : star (Rep P) A B → star (Rep P) S T) : P A B → P S T :=
representable.lift f

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

  instance is_mapping : mapping (→) :=
  { Rep := id, sieve := λ _ _, id, tabulate := λ _ _, id }

  /-- `A → _` is a functor. -/
  instance is_functor {A : Type} : functor ((→) A) :=
  {map := λ X Y f g a, f $ g $ a}

  /-- R distributes with the functor `(A → _)`. -/
  def dist_reader {R : Type → Type} [distributive R] {A B : Type} : (A → R B) → R (A → B)
  | f := @distributive.dist R _ ((→) A) function.is_functor _ f

end function

instance applicative_rep_of_traversing  [traversing P] : applicative (Rep P) :=
traversing.a

instance functor_rep_of_traversing [traversing P] : functor (Rep P) :=
by apply_instance

instance dist_rep_of_mapping [mapping P] : distributive (Rep P) :=
mapping.d

instance applicative_rep_of_mapping  [mapping P] : applicative (Rep P) :=
mapping.to_traversing.a

instance star.is_closed {F} [distributive F] : closed (star F) :=
{ close := λ A B C pab ca, function.dist_reader $ λ c, pab $ ca c}

open representable

instance closed_of_mapping [mapping P] : closed P :=
{ close := λ A B C, star_lift $ closed.close _}

instance strong_of_traversing [traversing P] : strong P :=
{ first  := λ A B C, star_lift $ first  C
, second := λ A B C, star_lift $ second C
}

instance choice_of_traversing [traversing P] : choice P :=
{ left  := λ A B C, star_lift $ left  C
, right := λ A B C, star_lift $ right C
}

instance profunctor_of_traversing [traversing P] : profunctor P :=
{ dimap := λ A B C D ba cd, star_lift $ dimap ba cd }

instance affine_of_traversing [traversing P] : affine P := {}

instance affine_of_mapping [mapping P] : affine P := {}

end profunctor

end control
