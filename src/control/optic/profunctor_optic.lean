/-
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/
import control.profunctor
import control.optic.concrete
import data.vector
import data.vector2

/-!
Definitions of profunctor optics.

### References:
- https://hackage.haskell.org/package/profunctor-optics-0.0.2/docs/index.html
- https://dl.acm.org/doi/pdf/10.1145/3236779
- https://golem.ph.utexas.edu/category/2020/01/profunctor_optics_the_categori.html
-/

def prod.elim {A B C} : (A → B → C) → A × B → C
| f (a,b) := f a b

def prod.intro {A B C} : (C → A) → (C → B) → C → (A × B)
| f g c := (f c, g c)

def prod.delta {A} : A → A × A
| a := (a,a)

namespace control

open control
open control.profunctor

def optic (P : Type → Type → Type) (A : Type) (B : Type) (S : Type) (T : Type) :=
P A B → P S T

@[reducible]
def optic' (P : Type → Type → Type) (A S : Type) : Type := optic P A A S S

namespace optic

section defs
  variables (A B S T : Type)

  def iso         := ∀ ⦃P⦄ [profunctor P], optic P A B S T

  def lens        := ∀ ⦃P⦄ [profunctor P] [strong P], optic P A B S T
  def lens'       := lens A A B B

  def colens      := ∀ ⦃P⦄ [profunctor P] [costrong P], optic P A B S T

  def prism       := ∀ ⦃P⦄ [profunctor P] [choice P], optic P A B S T
  def prism'      := prism A A B B

  def traversal0  := ∀ ⦃P⦄ [affine P], optic P A B S T
  def traversal0' := traversal0 A A B B
  def traversal   := ∀ ⦃P⦄ [traversing P], optic P A B S T

  def setter      := ∀ ⦃P⦄ [mapping P], optic P A B S T
  def setter'     := setter A A B B

  def grate       := ∀ ⦃P⦄ [profunctor P] [closed P], optic P A B S T
  def grate'      := grate A A B B

  def fold        := ∀ ⦃P⦄ [affine P] [traversing P] [coerce_r P], optic' P A S
end defs

variables {S T A B C D X Y : Type}
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

  def matching (sca : S → C × A) (cbt : C × B → T) : lens A B S T :=
  mk (prod.snd ∘ sca) (λ b s, cbt (prod.fst $ sca s,b))

  def united : lens unit unit A A := mk (λ a, ⟨⟩) (λ x a, a)
  def voided : lens A A empty empty := mk (λ e, by cases e) (λ a e, e)

  protected def id : lens A B A B := mk (λ a, a) (λ b _, b)
end lens

namespace colens
  def mk_core (bsa : B → S → A) (bt : B → T) ⦃P⦄ [profunctor P] [costrong P]
    : optic P A B S T
  | p := profunctor.dimap id bt
          $ costrong.unsecond B
          $ profunctor.dimap (prod.elim bsa) prod.delta
          $ p
end colens

namespace prism
  def view (p : prism A B S T) : S → T ⊕ A :=
  concrete.prism.get $ p $ concrete.prism.id

  def update (p : prism A B S T) : B → T :=
  concrete.prism.review $ p $ concrete.prism.id

  def mk (g : S → T ⊕ A) (s : B → T) ⦃P⦄ [profunctor P] [choice P]: optic P A B S T
  | f := dimap g (sum.elim id s) $ right _ $ f

  def the : prism A B (option A) (option B) :=
  mk (λ s, option.cases_on s (sum.inl none) (sum.inr)) (some)

end prism

namespace traversal
  def traversed_core (F : Type → Type) [traversable F] ⦃P⦄ [traversing P]
    : optic P S T (F S) (F T) :=
  representable.lift $ λ h fs, @sequence F _ (Rep P) _ _ (h <$> fs)

  def traversed (F : Type → Type) [traversable F] {S T : Type} : traversal S T (F S) (F T) :=
  traversed_core F

  def mk (f : concrete.traversal A B S T) ⦃P⦄ [traversing P] : optic P A B S T :=
  representable.lift $ λ h s,
    let ⟨n,a,b⟩ := f s in
    @functor.map _ _ _ _ b
    $ @vector.traverse _ _ profunctor.applicative_rep_of_traversing _ _ h a

  def out : traversal A B S T → concrete.traversal A B S T
  | tr := tr $ concrete.traversal.id

  def lists : traversal A B S T → S → list A
  | t s := let ⟨n, a, _⟩ := t.out s in a.to_list
end traversal

namespace setter
  def setter.mk_core (f : (A → B) → S → T) ⦃P⦄ [mapping P] : optic P A B S T :=
  representable.lift $ λ g s, (λ ab, f ab s) <$> (function.dist_reader g)
end setter

namespace grate
  def mk (f : ((S → A) → B) → T) ⦃P⦄ [profunctor P] [closed P] : optic P A B S T
  | p := profunctor.dimap (λ a (g : S → A), g a) f (closed.close (S → A) p)

  def out : grate A B S T → (((S → A) → B) → T)
  | g := g concrete.grate.id

  def zip_with {F : Type → Type} [functor F] : grate A B S T → (F A → B) → (F S → T)
  | g f := @g (costar F) _ _ f

  def distributed {F : Type → Type} [functor F] [distributive F] : grate A B (F A) (F B) :=
  mk (λ k, k <$> function.dist_reader id)

  def endomorphed : grate' A (A → A)
  | P _ c p := @closed.close P c _ _ A p
end grate

-- idea1: get the elaborator to do it.
class has_lens_comp (l3 : out_param $ Type 1) (l1 l2 : Type 1) :=
(comp : l1 → l2 → l3)

namespace coe

instance iso_lens : has_coe (iso A B C D) (lens A B C D)             :=
begin refine {..}, intros x,  repeat {intro}, unfreezingI {apply x}, assumption end
instance iso_prism: has_coe (iso A B C D) (prism A B C D)            :=
begin refine {..}, intros x,  repeat {intro}, unfreezingI {apply x}, assumption end
instance lens_t0  : has_coe (lens A B C D) (traversal0 A B C D)      :=
begin refine {..}, intros x,  repeat {intro}, unfreezingI {apply x}, assumption end
instance prism_t0 : has_coe (prism A B C D) (traversal0 A B C D)     :=
begin refine {..}, intros x,  repeat {intro}, unfreezingI {apply x}, assumption end
instance t0_t     : has_coe (traversal0 A B C D) (traversal A B C D) :=
begin refine {..}, intros x,  repeat {intro}, unfreezingI {apply x}, assumption end
instance t_setter : has_coe (traversal A B C D) (setter A B C D)     :=
begin refine {..}, intros x,  repeat {intro}, unfreezingI {apply x}, assumption end
instance iso_grate: has_coe (iso A B C D) (grate A B C D)            :=
begin refine {..}, intros x,  repeat {intro}, unfreezingI {apply x}, assumption end

end coe
-- def tlp (p: prism C D X Y) (l : lens A B C D) ⦃P⦄ [affine P] : optic P A B X Y
-- | x := p $ l $ x

-- instance tlpi : has_lens_comp (traversal0 A B X Y) (lens A B C D) (prism C D X Y) :=
-- {comp := λ x y, tlp y x }

/-
thorem : Lens composition is really hard :=




/-
len

 -/


 -/



end optic
end control
