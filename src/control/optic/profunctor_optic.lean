/-
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/
import control.profunctor
import control.optic.concrete
import data.vector
import data.vector2
import .prod

/-!
Definitions of profunctor optics.

### References:
- https://hackage.haskell.org/package/profunctor-optics-0.0.2/docs/index.html
- https://dl.acm.org/doi/pdf/10.1145/3236779
- https://golem.ph.utexas.edu/category/2020/01/profunctor_optics_the_categori.html
-/

namespace control

open control
open control.profunctor

-- def optic (P : Type → Type → Type) (A : Type) (B : Type) (S : Type) (T : Type) :=
-- P A B → P S T

-- @[reducible]
-- def optic' (P : Type → Type → Type) (A S : Type) : Type := optic P A A S S

def Pclass := (Type → Type → Type) → Type 1

def optic (π : Pclass) (A B S T : Type) := ∀ ⦃P⦄ [c : π P], P A B → P S T

namespace optic

section defs

  def iso         := optic profunctor

  def lens        := optic strong
  -- def lens'       := lens A A B B

  def colens      := optic costrong

  def prism       := optic choice
  -- def prism'      := prism A A B B

  def affinal     := optic affine
  -- def traversal0' := traversal0 A A B B
  def traversal   := optic traversing

  def setter      := optic mapping
  -- def setter'     := setter A A B B

  def grate       := optic closed
  def grate' (A B):= grate A A B B

  -- def fold        := ∀ ⦃P⦄ [affine P] [traversing P] [coerce_r P], optic' P A S
end defs

variables {S T A B C D X Y : Type}
variables {P : Type → Type → Type}

namespace iso
  def mk (g : S → A) (f : B → T) ⦃P⦄ [profunctor P] : P A B → P S T
  | p := profunctor.dimap g f p
end iso

namespace lens
  def mk_core  (g : S → A) (s : B → S → T) {P} [strong P] : P A B → P S T
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
  def mk_core (bsa : B → S → A) (bt : B → T) ⦃P⦄ [costrong P]
    : P A B → P  S T
  | p := profunctor.dimap id bt
          $ unsecond B
          $ profunctor.dimap (prod.elim bsa) prod.delta
          $ p
end colens

namespace prism
  def view (p : prism A B S T) : S → T ⊕ A :=
  concrete.prism.get $ p $ concrete.prism.id

  def update (p : prism A B S T) : B → T :=
  concrete.prism.review $ p $ concrete.prism.id

  def mk (g : S → T ⊕ A) (s : B → T) ⦃P⦄ [choice P]: P A B → P S T
  | f := dimap g (sum.elim id s) $ right _ $ f

end prism

def affinal.mk (f : S → T ⊕ A) (g : S → B → T) ⦃P⦄ [affine P] : P A B → P S T
| p := dimap (prod.intro id f) (function.uncurry $ sum.elim id ∘ g) $ second S $ right T p

namespace traversal
  def traversed_core (F : Type → Type) [traversable F] ⦃P⦄ [traversing P]
    : P S T → P (F S) (F T) :=
  representable.lift $ λ h fs, @sequence F _ (Rep P) _ _ (h <$> fs)

  def traversed (F : Type → Type) [traversable F] {S T : Type} : traversal S T (F S) (F T) :=
  traversed_core F

  def mk (f : concrete.traversal A B S T) ⦃P⦄ [traversing P] : P A B → P S T :=
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
  def setter.mk_core (f : (A → B) → S → T) ⦃P⦄ [mapping P] : P A B → P S T :=
  representable.lift $ λ g s, (λ ab, f ab s) <$> (function.dist_reader g)
end setter

namespace grate
  def mk (f : ((S → A) → B) → T) ⦃P⦄ [closed P] : P A B → P S T
  | p := profunctor.dimap (λ a (g : S → A), g a) f (closed_core.close (S → A) p)

  def out : grate A B S T → (((S → A) → B) → T)
  | g := g concrete.grate.id

  def zip_with {F : Type → Type} [functor F] : grate A B S T → (F A → B) → (F S → T)
  | g f := @g (costar F) _ f

  def distributed {F : Type → Type} [functor F] [distributive F] : grate A B (F A) (F B) :=
  mk (λ k, k <$> function.dist_reader id)

  def endomorphed : grate' A (A → A)
  | P c p := @closed_core.close P c.to_closed_core _ _ A p
end grate

-- idea1: get the elaborator to do it.
class has_lens_comp (l3 : out_param $ Type 1) (l1 l2 : Type 1) :=
(comp : l1 → l2 → l3)

namespace coe

instance iso_lens : has_coe (iso A B C D) (lens A B C D)             :=
begin refine {..}, intros x,  repeat {intro}, unfreezingI {apply x}, assumption end
instance iso_prism: has_coe (iso A B C D) (prism A B C D)            :=
begin refine {..}, intros x,  repeat {intro}, unfreezingI {apply x}, assumption end
instance lens_t0  : has_coe (lens A B C D) (affinal A B C D)      :=
begin refine {..}, intros x,  repeat {intro}, unfreezingI {apply x}, assumption end
instance prism_t0 : has_coe (prism A B C D) (affinal A B C D)     :=
begin refine {..}, intros x,  repeat {intro}, unfreezingI {apply x}, assumption end
instance t0_t     : has_coe (affinal A B C D) (traversal A B C D) :=
begin refine {..}, intros x,  repeat {intro}, unfreezingI {apply x}, assumption end
instance t_setter : has_coe (traversal A B C D) (setter A B C D)     :=
begin refine {..}, intros x,  repeat {intro}, unfreezingI {apply x}, assumption end
instance iso_grate: has_coe (iso A B C D) (grate A B C D)            :=
begin refine {..}, intros x,  repeat {intro}, unfreezingI {apply x}, assumption end

end coe

/-- We have `meet_triple π ρ σ` when `∀ P, (π P) × (ρ P) ≅ (σ P)`,
so eg `meet_triple strong choice affine`.
Ideally, the Lean elaborator would figure these out automatically as Haskell does.
This is used to get the definition of `compose` to work below.  -/
class meet_triple (π ρ σ : Pclass) :=
(fst : ∀ {P}, σ P → π P)
(snd : ∀ {P}, σ P → ρ P)

def compose {π ρ σ : Pclass} [t : meet_triple π ρ σ] :  optic ρ C D X Y → optic π A B C D → optic σ A B X Y
| o2 o1 P c p := @o2 P (meet_triple.snd π c) $ @o1 P (meet_triple.fst ρ c) $ p

instance mt_self {π} : meet_triple π π π := ⟨λ P, id,λ P, id⟩

instance mt_lp : meet_triple strong choice affine :=
⟨@profunctor.strong_of_affine, @profunctor.choice_of_affine⟩

instance mt_pl : meet_triple choice strong affine :=
⟨@profunctor.choice_of_affine, @profunctor.strong_of_affine⟩

def zip_with2 : grate A B S T → (A → A → B) → S → S → T
| g p := function.curry $ @g (costar prod.square) _ $ function.uncurry p

def both : traversal A B (A × A) (B × B) :=
@control.optic.traversal.traversed prod.square prod.square.is_trav A B

def fst : lens A B (A × C) (B × C) :=
begin intros P st x, unfreezingI {apply first, apply x}  end

def snd : lens A B (C × A) (C × B) :=
begin intros P st x, unfreezingI {apply second, apply x} end

def the : prism A B (option A) (option B) :=
prism.mk (λ s, option.cases_on s (sum.inl none) (sum.inr)) (some)

def does_it_compose : affinal A B (C × option A) (C × option B) :=
compose snd the

def does_it_compose2 : lens A B (C × D × A) (C × D × B) :=
compose snd snd

-- l ∈ {iso, lens, prism, traversal, colens, grate, traversal0}

-- class has_lens_comp :=
-- (comp : _ _)

-- def Optic_ (P) (A B S T) := optic P

-- @[reducible] def Optic (c : (Type → Type → Type) → Type 1) (A B S T : Type) :=
--   ∀ ⦃P⦄ [c P], optic P A B S T

-- def compose : optic P S T A B → optic P A B X Y → optic P S T X Y
-- | o1 o2 := o2 ∘ o1

-- def Iso := Optic profunctor
-- def Lens := Optic STRONG
-- def Prism := Optic CHOICE
-- def Traversal0 := Optic affine

-- constant XX : Lens S T A B
-- constant YY : Prism A B X Y

-- #check compose XX YY

-- def compl : traversal0 A B S T → traversal0 S T X Y → traversal0 A B X Y
-- | f g P 𝒜 x := begin unfreezingI {exact (g $ f $ x)} end

-- inductive Optic (A B S T : Type) : Type 1
-- | iso   (f : ∀ ⦃P⦄ [profunctor P], optic P A B S T)            : Optic
-- | lens  (f : ∀ ⦃P⦄ [profunctor P] [strong P], optic P A B S T) : Optic
-- | prism (f : ∀ ⦃P⦄ [profunctor P] [choice P], optic P A B S T) : Optic
-- | traversal0 (f : ∀ ⦃P⦄ [affine P], optic P A B S T) : Optic

-- @[reducible] def composeT  : Π (x :Optic A B S T) (y : Optic S T X Y), Type 1
-- | (Optic.iso f)  (Optic.iso g) := iso A B X Y
-- | (Optic.iso f)  (Optic.lens g) := lens A B X Y
-- | (Optic.lens f)  (Optic.iso g) := lens A B X Y
-- | (Optic.lens f)  (Optic.lens g) := lens A B X Y
-- | (Optic.prism f) (Optic.lens g) := traversal0 A B X Y
-- | _ _ := punit

-- def compose  : Π (x : Optic A B S T) (y : Optic S T X Y), composeT x y
-- := begin
--   intros f g,
--   cases f; cases g; try {
--     try {intros P pf x, unfreezingI {exact (g $ f $ x)}},
--     try {apply punit.star},
--   },
-- end

-- l1 A B C D → l2 C D X Y → (l3 l1 l2) A B X Y

-- def tlp (p: prism C D X Y) (l : lens A B C D) ⦃P⦄ [affine P] : optic P A B X Y
-- | x := p $ l $ x

-- instance tlpi : has_lens_comp (traversal0 A B X Y) (lens A B C D) (prism C D X Y) :=
-- {comp := λ x y, tlp y x }

/-
Idea:

Make a meet lattice over `C := (Type → Type → Type) → Type`.
Then define `Optic (c : C) A B S T := ∀ P [c], optic P A B S T`

Then we can define `composeT` as above but over all things.
Then it will just work

 -/

end optic
end control
