/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/

import tactic.cache
import category.applicative

/-!
# Traversable type class

Type classes for traversing collections. The concepts and laws are taken from
http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Traversable.html

Traversable collections are a generalization of functors. Whereas
functors (such as `list`) allow us to apply a function to every
element, it does not allow functions which external effects encoded in
a monad. Consider for instance a functor `invite : email -> io response`
that takes an email address, sends an email and wait for a
response. If we have a list `guests : list email`, using calling
`invite` using `map` gives us the following: `map invite guests : list
(io response)`.  It is not what we need. We need something of type `io
(list response)`. Instead of using `map`, we can use `traverse` to
send all the invites: `traverse invite guests : io (list response)`.
`traverse` applies `invite` to every element of `guests` and combines
all the resulting effects. In the example, the effect is encoded in the
monad `io` but any applicative functor is accepted by `traverse`.

For more on how to use traversable, consider the Haskell tutorial:
https://en.wikibooks.org/wiki/Haskell/Traversable

## Main definitions
  * `traversable` type class - exposes the `traverse` function
  * `sequence` - based on `traverse`, turns a collection of effects into an effect returning a collection
  * is_lawful_traversable - laws

## Tags

traversable iterator functor applicative

## References

 * "Applicative Programming with Effects", by Conor McBride and Ross Paterson, Journal of Functional Programming 18:1 (2008) 1-13, online at http://www.soi.city.ac.uk/~ross/papers/Applicative.html.
 * "The Essence of the Iterator Pattern", by Jeremy Gibbons and Bruno Oliveira, in Mathematically-Structured Functional Programming, 2006, online at http://web.comlab.ox.ac.uk/oucl/work/jeremy.gibbons/publications/#iterator.
 * "An Investigation of the Laws of Traversals", by Mauro Jaskelioff and Ondrej Rypacek, in Mathematically-Structured Functional Programming, 2012, online at http://arxiv.org/pdf/1202.2919.
Synopsis


-/

open function (hiding comp)

universes u v w

section applicative_transformation

variables (F : Type u → Type v) [applicative F] [is_lawful_applicative F]
variables (G : Type u → Type w) [applicative G] [is_lawful_applicative G]

structure applicative_transformation : Type (max (u+1) v w) :=
(app : ∀ α : Type u, F α → G α)
(preserves_pure' : ∀ {α : Type u} (x : α), app _ (pure x) = pure x)
(preserves_seq' : ∀ {α β : Type u} (x : F (α → β)) (y : F α), app _ (x <*> y) = app _ x <*> app _ y)

end applicative_transformation

namespace applicative_transformation

variables (F : Type u → Type v) [applicative F] [is_lawful_applicative F]
variables (G : Type u → Type w) [applicative G] [is_lawful_applicative G]

instance : has_coe_to_fun (applicative_transformation F G) :=
{ F := λ _, Π {α}, F α → G α,
  coe := λ a, a.app }

variables {F G}
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

end applicative_transformation

open applicative_transformation

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

def sequence [traversable t] : t (f α) → f (t α) := traverse id

end functions

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

protected def traverse {α β} (f : α → F β) : σ ⊕ α → F (σ ⊕ β)
| (sum.inl x) := pure (sum.inl x)
| (sum.inr x) := sum.inr <$> f x

end sum

instance {σ : Type u} : traversable.{u} (sum σ) := ⟨@sum.traverse _⟩
