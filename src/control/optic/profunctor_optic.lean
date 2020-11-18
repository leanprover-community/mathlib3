import control.profunctor
import control.optic.concrete

-- https://dl.acm.org/doi/pdf/10.1145/3236779

def prod.elim {A B C} : (A → B → C) → A × B → C
| f (a,b) := f a b

def prod.intro {A B C} : (C → A) → (C → B) → C → (A × B)
| f g c := (f c, g c)

namespace control

open control
open control.profunctor

def optic (P : Type → Type → Type) (A : Type) (B : Type) (S : Type) (T : Type) :=
P A B → P S T

def optic' (P : Type → Type → Type) (A S : Type) : Type := optic P A A S S

namespace optic

section defs
  variables (A B S T : Type)

  def iso := ∀ ⦃P⦄ [profunctor P], optic P A B S T

  def lens := ∀ ⦃P⦄ [profunctor P] [strong P], optic P A B S T
  def lens' := lens A B A B

  def prism := ∀ ⦃P⦄ [profunctor P] [choice P], optic P A B S T
  def prism' := prism A B A B

  def traversal0  := ∀ ⦃P⦄ [affine P], optic P A B S T
  def traversal0' := traversal0 A B A B
  def traversal   := ∀ ⦃P⦄ [affine P] [traversing P], optic P A B S T

  def setter  := ∀ ⦃P⦄ [affine P] [mapping P], optic P A B S T
  def setter' := setter A B A B

  def grate := ∀ ⦃P⦄ [closed P], optic P A B S T

  def fold := ∀ ⦃P⦄ [affine P] [traversing P] [coerce_r P], optic' P A S

end defs

variables {S T A B C : Type}
variables {P : Type → Type → Type}

namespace iso
  def mk (g : S → A) (f : B → T) ⦃P⦄ [profunctor P] : optic P A B S T
  | p := profunctor.dimap g f p
end iso

namespace lens
  def mk_core  (g : S → A) (s : B → S → T) {P} [profunctor P] [strong P] : optic P A B S T
  | f := dimap (prod.intro g id) (prod.elim s) $ first S $ f

  def mk (g : S → A) (s : B → S → T) : lens A B S T :=
  @lens.mk_core _ _ _ _ g s

  def view (l : lens A B S T) : S → A :=
  concrete.lens.view $ l $ concrete.lens.id

  def update (l : lens A B S T) : B → S → T :=
  concrete.lens.update $ l $ concrete.lens.id
end lens

namespace prism
  def view (p : prism A B S T) : S → T ⊕ A :=
  concrete.prism.get $ p $ concrete.prism.id

  def update (p : prism A B S T) : B → T :=
  concrete.prism.review $ p $ concrete.prism.id

  def mk (g : S → T ⊕ A) (s : B → T) ⦃P⦄ [profunctor P] [choice P]: optic P A B S T
  | f := dimap g (sum.elim id s) $ right _ $ f
end prism

def traversed (F : Type → Type) [traversable F] ⦃P⦄ [affine P] [traversing P] : optic P S T (F S) (F T)
| h := representable.tabulate (λ fs, @sequence F _ (Rep P) _ _ ((representable.sieve $ h) <$> fs))

namespace setter
  def setter.mk_core (f : (A → B) → S → T) ⦃P⦄ [affine P] [mapping P] : optic P A B S T
  | g := representable.tabulate
          $ λ s, @has_seq.seq (Rep P) _ _ _ (pure $ λ ab, f ab s)
          $ function.dist_reader
          $ representable.sieve $ g
end setter

namespace grate

  def mk (f : ((S → A) → B) → T) ⦃P⦄ [profunctor P] [closed P] : optic P A B S T
  | p := profunctor.dimap (λ a (g : S → A), g a) f (closed.close (S → A) p)

  def out : grate A B S T → (((S → A) → B) → T)
  | g :=  g concrete.grate.id

  def zip_f_with_of {F : Type → Type} [functor F] : grate A B S T → (F A → B) → (F S → T)
  | g f := @g (costar F) _ f

end grate

end optic
end control
