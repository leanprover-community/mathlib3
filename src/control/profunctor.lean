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
(first {A B} (C) : P A B → P (A × C) (B × C))
(second {A B} (C) : P A B → P (C × A) (C × B))

@[reducible] def first := @strong.first
@[reducible] def second := @strong.second

class choice (P : Type → Type → Type) :=
(left {A B} (C) : P A B → P (A ⊕ C) (B ⊕ C))
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
(sieve {A B} : P A B → A → Rep B)
(tabulate {A B} : (A → Rep B) → P A B)

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

  instance : profunctor (star F) :=
  {dimap := λ A B C D f g h a, g <$> (h $ f a)}

  instance : representable (star F) :=
  { Rep := F
  , sieve := λ A B, id
  , tabulate := λ A B, id
  }
end star

/-- `costar F A B = F A → B` -/
def costar (F : Type → Type) (A B : Type) := F A → B

namespace costar
  variables {F : Type → Type} [functor F]
  instance : profunctor (costar F) :=
  { dimap := λ A B X Y ba xy cs fb, xy $ cs $ functor.map ba fb}

  instance : closed (costar F) :=
  { close := λ A B X fab fxa x, fab $ (λ (f : X → A), f x) <$> fxa}
end costar

namespace function
  instance is_lawful : lawful_profunctor (→) :=
  { dimap := λ A B C D f g h, g ∘ h ∘ f
  , did := λ _ _, rfl
  , dcomp := λ _ _ _ _ _ _ _ _ _ _, rfl
  }

  instance is_strong : strong (→) :=
  { first := λ A B C f, prod.map f id
  , second := λ A B C f, prod.map id f
  }

  /-- `A → _` is a functor. -/
  instance is_functor {A : Type} : functor ((→) A) :=
  {map := λ X Y f g a, f $ g $ a}

  def dist_reader {R : Type → Type} [distributive R] {A B : Type} : (A → R B) → R (A → B)
  | f := @distributive.dist R _ ((→) A) function.is_functor _ f

end function

instance applicative_rep_of_traversing {P : Type → Type → Type} [traversing P] : applicative (Rep P) :=
traversing.a

instance dist_rep_of_mapping {P : Type → Type → Type} [mapping P] : distributive (Rep P) :=
mapping.d

instance applicative_rep_of_mapping {P : Type → Type → Type} [mapping P] : applicative (Rep P) :=
mapping.to_traversing.a

end profunctor

end control
