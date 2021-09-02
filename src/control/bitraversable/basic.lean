/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import control.bifunctor
import control.traversable.basic

/-!
# Bitraversable type class

Type class for traversing bifunctors. The concepts and laws are taken from
<https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

Simple examples of `bitraversable` are `prod` and `sum`. A more elaborate example is
to define an a-list as:

```
def alist (key val : Type) := list (key × val)
```

Then we can use `f : key → io key'` and `g : val → io val'` to manipulate the `alist`'s key
and value respectively with `bitraverse f g : alist key val → io (alist key' val')`

## Main definitions
  * bitraversable - exposes the `bitraverse` function
  * is_lawful_bitraversable - laws similar to is_lawful_traversable

## Tags

traversable bitraversable iterator functor bifunctor applicative

-/

universes u

class bitraversable (t : Type u → Type u → Type u)
  extends bifunctor t :=
(bitraverse : Π {m : Type u → Type u} [applicative m] {α α' β β'},
  (α → m α') → (β → m β') → t α β → m (t α' β'))
export bitraversable ( bitraverse )

def bisequence {t m} [bitraversable t] [applicative m] {α β} : t (m α) (m β) → m (t α β) :=
bitraverse id id

open functor

class is_lawful_bitraversable (t : Type u → Type u → Type u) [bitraversable t]
  extends is_lawful_bifunctor t :=
(id_bitraverse : ∀ {α β} (x : t α β), bitraverse id.mk id.mk x = id.mk x )
(comp_bitraverse : ∀ {F G} [applicative F] [applicative G]
    [is_lawful_applicative F] [is_lawful_applicative G]
    {α α' β β' γ γ'} (f : β → F γ) (f' : β' → F γ')
    (g : α → G β) (g' : α' → G β') (x : t α α'),
  bitraverse (comp.mk ∘ map f ∘ g) (comp.mk ∘ map f' ∘ g') x =
  comp.mk (bitraverse f f' <$> bitraverse g g' x) )
(bitraverse_eq_bimap_id : ∀ {α α' β β'} (f : α → β) (f' : α' → β') (x : t α α'),
   bitraverse (id.mk ∘ f) (id.mk ∘ f') x = id.mk (bimap f f' x))
(binaturality : ∀ {F G} [applicative F] [applicative G]
    [is_lawful_applicative F] [is_lawful_applicative G]
    (η : applicative_transformation F G) {α α' β β'}
    (f : α → F β) (f' : α' → F β') (x : t α α'),
  η (bitraverse f f' x) = bitraverse (@η _ ∘ f) (@η _ ∘ f') x)

export is_lawful_bitraversable ( id_bitraverse comp_bitraverse
                                 bitraverse_eq_bimap_id  )
open is_lawful_bitraversable

attribute [higher_order bitraverse_id_id] id_bitraverse
attribute [higher_order bitraverse_comp] comp_bitraverse
attribute [higher_order] binaturality bitraverse_eq_bimap_id

export is_lawful_bitraversable (bitraverse_id_id bitraverse_comp)
