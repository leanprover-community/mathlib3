/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import control.functor

/-!
# Traversable type class

Type classes for traversing collections. The concepts and laws are taken from
<http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Traversable.html>

Traversable collections are a generalization of functors. Whereas
functors (such as `list`) allow us to apply a function to every
element, it does not allow functions which external effects encoded in
a monad. Consider for instance a functor `invite : email → io response`
that takes an email address, sends an email and waits for a
response. If we have a list `guests : list email`, using calling
`invite` using `map` gives us the following: `map invite guests : list
(io response)`.  It is not what we need. We need something of type `io
(list response)`. Instead of using `map`, we can use `traverse` to
send all the invites: `traverse invite guests : io (list response)`.
`traverse` applies `invite` to every element of `guests` and combines
all the resulting effects. In the example, the effect is encoded in the
monad `io` but any applicative functor is accepted by `traverse`.

For more on how to use traversable, consider the Haskell tutorial:
<https://en.wikibooks.org/wiki/Haskell/Traversable>

## Main definitions
  * `traversable` type class - exposes the `traverse` function
  * `sequence` - based on `traverse`,
    turns a collection of effects into an effect returning a collection
  * `is_lawful_traversable` - laws for a traversable functor
  * `applicative_transformation` - the notion of a natural transformation for applicative functors

## Tags

traversable iterator functor applicative

## References

 * "Applicative Programming with Effects", by Conor McBride and Ross Paterson,
   Journal of Functional Programming 18:1 (2008) 1-13, online at
   <http://www.soi.city.ac.uk/~ross/papers/Applicative.html>
 * "The Essence of the Iterator Pattern", by Jeremy Gibbons and Bruno Oliveira,
   in Mathematically-Structured Functional Programming, 2006, online at
   <http://web.comlab.ox.ac.uk/oucl/work/jeremy.gibbons/publications/#iterator>
 * "An Investigation of the Laws of Traversals", by Mauro Jaskelioff and Ondrej Rypacek,
   in Mathematically-Structured Functional Programming, 2012,
   online at <http://arxiv.org/pdf/1202.2919>
-/

open function (hiding comp)

universes u v w

section applicative_transformation

variables (F : Type u → Type v) [applicative F] [is_lawful_applicative F]
variables (G : Type u → Type w) [applicative G] [is_lawful_applicative G]

/-- A transformation between applicative functors.  It is a natural
transformation such that `app` preserves the `has_pure.pure` and
`functor.map` (`<*>`) operations. See
`applicative_transformation.preserves_map` for naturality. -/
structure applicative_transformation : Type (max (u+1) v w) :=
(app : Π α : Type u, F α → G α)
(preserves_pure' : ∀ {α : Type u} (x : α), app _ (pure x) = pure x)
(preserves_seq' : ∀ {α β : Type u} (x : F (α → β)) (y : F α), app _ (x <*> y) = app _ x <*> app _ y)

end applicative_transformation

namespace applicative_transformation

variables (F : Type u → Type v) [applicative F] [is_lawful_applicative F]
variables (G : Type u → Type w) [applicative G] [is_lawful_applicative G]

instance : has_coe_to_fun (applicative_transformation F G) (λ _, Π {α}, F α → G α) :=
⟨applicative_transformation.app⟩

variables {F G}

@[simp]
lemma app_eq_coe (η : applicative_transformation F G) : η.app = η := rfl

@[simp]
lemma coe_mk (f : Π (α : Type u), F α → G α) (pp ps) :
  ⇑(applicative_transformation.mk f pp ps) = f := rfl

protected
lemma congr_fun (η η' : applicative_transformation F G) (h : η = η') {α : Type u} (x : F α) :
  η x = η' x :=
congr_arg (λ η'' : applicative_transformation F G, η'' x) h

protected
lemma congr_arg (η : applicative_transformation F G) {α : Type u} {x y : F α} (h : x = y) :
  η x = η y :=
congr_arg (λ z : F α, η z) h

lemma coe_inj ⦃η η' : applicative_transformation F G⦄ (h : (η : Π α, F α → G α) = η') : η = η' :=
by { cases η, cases η', congr, exact h }

@[ext]
lemma ext ⦃η η' : applicative_transformation F G⦄ (h : ∀ (α : Type u) (x : F α), η x = η' x) :
  η = η' :=
by { apply coe_inj, ext1 α, exact funext (h α) }

lemma ext_iff {η η' : applicative_transformation F G} :
  η = η' ↔ ∀ (α : Type u) (x : F α), η x = η' x :=
⟨λ h α x, h ▸ rfl, λ h, ext h⟩

section preserves
variables (η : applicative_transformation F G)

@[functor_norm]
lemma preserves_pure : ∀ {α} (x : α), η (pure x) = pure x := η.preserves_pure'

@[functor_norm]
lemma preserves_seq :
  ∀ {α β : Type u} (x : F (α → β)) (y : F α), η (x <*> y) = η x <*> η y :=
η.preserves_seq'

@[functor_norm]
lemma preserves_map {α β} (x : α → β) (y : F α) : η (x <$> y) = x <$> η y :=
by rw [← pure_seq_eq_map, η.preserves_seq]; simp with functor_norm

lemma preserves_map' {α β} (x : α → β) : @η _ ∘ functor.map x = functor.map x ∘ @η _ :=
by { ext y, exact preserves_map η x y }

end preserves

/-- The identity applicative transformation from an applicative functor to itself. -/
def id_transformation : applicative_transformation F F :=
{ app := λ α, id,
  preserves_pure' := by simp,
  preserves_seq' := λ α β x y, by simp }

instance : inhabited (applicative_transformation F F) := ⟨id_transformation⟩

universes s t
variables {H : Type u → Type s} [applicative H] [is_lawful_applicative H]

/-- The composition of applicative transformations. -/
def comp (η' : applicative_transformation G H) (η : applicative_transformation F G) :
  applicative_transformation F H :=
{ app := λ α x, η' (η x),
  preserves_pure' := λ α x, by simp with functor_norm,
  preserves_seq' := λ α β x y, by simp with functor_norm }

@[simp]
lemma comp_apply (η' : applicative_transformation G H) (η : applicative_transformation F G)
  {α : Type u} (x : F α) :
  η'.comp η x = η' (η x) := rfl

lemma comp_assoc {I : Type u → Type t} [applicative I] [is_lawful_applicative I]
  (η'' : applicative_transformation H I)
  (η' : applicative_transformation G H)
  (η : applicative_transformation F G) :
  (η''.comp η').comp η = η''.comp (η'.comp η) := rfl

@[simp]
lemma comp_id (η : applicative_transformation F G) : η.comp id_transformation = η :=
ext $ λ α x, rfl

@[simp]
lemma id_comp (η : applicative_transformation F G) : id_transformation.comp η = η :=
ext $ λ α x, rfl

end applicative_transformation

open applicative_transformation

/-- A traversable functor is a functor along with a way to commute
with all applicative functors (see `sequence`).  For example, if `t`
is the traversable functor `list` and `m` is the applicative functor
`io`, then given a function `f : α → io β`, the function `functor.map f` is
`list α → list (io β)`, but `traverse f` is `list α → io (list β)`. -/
class traversable (t : Type u → Type u) extends functor t :=
(traverse : Π {m : Type u → Type u} [applicative m] {α β},
   (α → m β) → t α → m (t β))

open functor

export traversable (traverse)

section functions

variables {t : Type u → Type u}
variables {m : Type u → Type v} [applicative m]
variables {α β : Type u}


variables {f : Type u → Type u} [applicative f]

/-- A traversable functor commutes with all applicative functors. -/
def sequence [traversable t] : t (f α) → f (t α) := traverse id

end functions

/-- A traversable functor is lawful if its `traverse` satisfies a
number of additional properties.  It must send `id.mk` to `id.mk`,
send the composition of applicative functors to the composition of the
`traverse` of each, send each function `f` to `λ x, f <$> x`, and
satisfy a naturality condition with respect to applicative
transformations. -/
class is_lawful_traversable (t : Type u → Type u) [traversable t]
  extends is_lawful_functor t : Type (u+1) :=
(id_traverse : ∀ {α} (x : t α), traverse id.mk x = x )
(comp_traverse : ∀ {F G} [applicative F] [applicative G]
    [is_lawful_applicative F] [is_lawful_applicative G]
    {α β γ} (f : β → F γ) (g : α → G β) (x : t α),
  traverse (comp.mk ∘ map f ∘ g) x =
  comp.mk (map (traverse f) (traverse g x)))
(traverse_eq_map_id : ∀ {α β} (f : α → β) (x : t α),
  traverse (id.mk ∘ f) x = id.mk (f <$> x))
(naturality : ∀ {F G} [applicative F] [applicative G]
    [is_lawful_applicative F] [is_lawful_applicative G]
    (η : applicative_transformation F G) {α β} (f : α → F β) (x : t α),
  η (traverse f x) = traverse (@η _ ∘ f) x)

instance : traversable id := ⟨λ _ _ _ _, id⟩
instance : is_lawful_traversable id := by refine {..}; intros; refl

section

variables {F : Type u → Type v} [applicative F]

instance : traversable option := ⟨@option.traverse⟩

instance : traversable list := ⟨@list.traverse⟩

end

namespace sum

variables {σ : Type u}
variables {F : Type u → Type u}
variables [applicative F]

/-- Defines a `traverse` function on the second component of a sum type.
This is used to give a `traversable` instance for the functor `σ ⊕ -`. -/
protected def traverse {α β} (f : α → F β) : σ ⊕ α → F (σ ⊕ β)
| (sum.inl x) := pure (sum.inl x)
| (sum.inr x) := sum.inr <$> f x

end sum

instance {σ : Type u} : traversable.{u} (sum σ) := ⟨@sum.traverse _⟩
