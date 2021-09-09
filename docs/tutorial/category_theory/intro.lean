import category_theory.functor_category -- this transitively imports
-- category_theory.category
-- category_theory.functor
-- category_theory.natural_transformation

/-!
# An introduction to category theory in Lean

This is an introduction to the basic usage of category theory (in the mathematical sense) in Lean.
We cover how the basic theory of categories, functors and natural transformations is set up in Lean.
Most of the below is not hard to read off from the files `category_theory/category.lean`,
`category_theory/functor.lean` and `category_theory/natural_transformation.lean`.

## Overview

A category is a collection of objects, and a collection of morphisms (also known as arrows) between
the objects. The objects and morphisms have some extra structure and satisfy some axioms -- see the
[definition on Wikipedia](https://en.wikipedia.org/wiki/Category_%28mathematics%29#Definition) for
details.

One important thing to note is that a morphism in an abstract category may not be an actual function
between two types. In particular, there is new notation `⟶` , typed as `\h` or `\hom` in VS Code,
for a morphism. Nevertheless, in most of the "concrete" categories like `Top` and `Ab`, it is still
possible to write `f x` when `x : X` and `f : X ⟶ Y` is a morphism, as there is an automatic
coercion from morphisms to functions. (If the coercion doesn't fire automatically, sometimes it is
necessary to write `(f : X → Y) x`.)

In some fonts the `⟶` morphism arrow can be virtually indistinguishable from the standard function
arrow `→` . You may want to install the [Deja Vu Sans Mono](https://dejavu-fonts.github.io/) and put
that at the beginning of the `Font Family` setting in VSCode, to get a nice readable font with
excellent unicode coverage.

Another point of confusion can be universe issues. Following Lean's conventions for universe
polymorphism, the objects of a category might live in one universe `u` and the morphisms in another
universe `v`. Note that in many categories showing up in "set-theoretic mathematics", the morphisms
between two objects often form a set, but the objects themselves may or may not form a set. In Lean
this corresponds to the two possibilities `u=v` and `u=v+1`, known as `small_category` and
`large_category` respectively. In order to avoid proving the same statements for both small and
large categories, we usually stick to the general polymorphic situation with `u` and `v` independent
universes, and we do this below.

## Getting started with categories

The structure of a category on a type `C` in Lean is done using typeclasses; terms of `C` then
correspond to objects in the category. The convention in the category theory library is to use
universes prefixed with `u` (e.g. `u`, `u₁`, `u₂`) for the objects, and universes prefixed with `v`
for morphisms. Thus we have `C : Type u`, and if `X : C` and `Y : C` then morphisms `X ⟶ Y : Type v`
(note the non-standard arrow).

We set this up as follows:
-/

open category_theory

section category

variables (C : Type*) [category C]

variables {W X Y Z : C}
variables (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)

/-!
This says "let `C` be a category, let `W`, `X`, `Y`, `Z` be objects of `C`, and let `f : W ⟶ X`, `g
: X ⟶ Y` and `h : Y ⟶ Z` be morphisms in `C` (with the specified source and targets)".

Note that we sometimes need to explicitly tell Lean the universe that the morphisms live in,
by writing `category.{v} C`, because Lean cannot guess this from `C` alone.
However just writing `category C` is often fine: this allows a "free" universe level.

The order in which universes are introduced at the top of the file matters:
we put the universes for morphisms first (typically `v`, `v₁` and so on),
and then universes for objects (typically `u`, `u₁` and so on).
This ensures that in any new definition we make the universe variables for morphisms come first,
so that they can be explicitly specified while still allowing the universe levels of the
objects to be inferred automatically.

## Basic notation

In categories one has morphisms between objects, such as the identity morphism from an object to
itself. One can compose morphisms, and there are standard facts about the composition of a morphism
with the identity morphism, and the fact that morphism composition is associative. In Lean all of
this looks like the following:
-/

-- The identity morphism from `X` to `X` (remember that this is the `\h` arrow):
example : X ⟶ X := 𝟙 X -- type `𝟙` as `\bb1`

-- Function composition `h ∘ g`, a morphism from `X` to `Z`:
example : X ⟶ Z := g ≫ h

/-
Note in particular the order! The "maps on the right" convention was chosen; `g ≫ h` means "`g` then
`h`". Type `≫` with `\gg` in VS Code. Here are the theorems which ensure that we have a category.
-/

open category_theory.category

example : 𝟙 X ≫ g = g := id_comp g
example : g ≫ 𝟙 Y = g := comp_id g
example : (f ≫ g) ≫ h = f ≫ (g ≫ h) := assoc f g h
example : (f ≫ g) ≫ h = f ≫ g ≫ h := assoc f g h -- note \gg is right associative

-- All four examples above can also be proved with `simp`.

-- Monomorphisms and epimorphisms are predicates on morphisms and are implemented as typeclasses.
variables (f' : W ⟶ X) (h' : Y ⟶ Z)

example [mono g] : f ≫ g = f' ≫ g → f = f' := mono.right_cancellation f f'
example [epi g] : g ≫ h = g ≫ h' → h = h' := epi.left_cancellation h h'

end category -- end of section

/-!
## Getting started with functors

A functor is a map between categories. It is implemented as a structure. The notation for a functor
from `C` to `D` is `C ⥤ D`. Type `\func` in VS Code for the symbol. Here we demonstrate how to
evaluate functors on objects and on morphisms, how to show functors preserve the identity morphism
and composition of morphisms, how to compose functors, and show the notation `𝟭` for the identity
functor.
-/

section functor

variables (C : Type*) [category C]
variables (D : Type*) [category D]
variables (E : Type*) [category E]

variables {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

-- functors
variables (F : C ⥤ D) (G : D ⥤ E)

example : D := F.obj X -- functor F on objects
example : F.obj Y ⟶ F.obj Z := F.map g -- functor F on morphisms

-- A functor sends identity objects to identity objects
example : F.map (𝟙 X) = 𝟙 (F.obj X) := F.map_id X

-- and preserves compositions
example : F.map (f ≫ g) = (F.map f) ≫ (F.map g) := F.map_comp f g

-- The identity functor is `𝟭`, which you can write as `\sb1`.
example : C ⥤ C := 𝟭 C

-- The identity functor is (definitionally) the identity on objects and morphisms:
example : (𝟭 C).obj X = X := category_theory.functor.id_obj X
example : (𝟭 C).map f = f := category_theory.functor.id_map f

-- Composition of functors; note order:
example : C ⥤ E := F ⋙ G -- typeset with `\ggg`

-- Composition of the identity either way does nothing:
example : F ⋙ 𝟭 D = F := F.comp_id
example : 𝟭 C ⋙ F = F := F.id_comp

-- Composition of functors definitionally does the right thing on objects and morphisms:
example : (F ⋙ G).obj X = G.obj (F.obj X) := F.comp_obj G X -- or rfl
example : (F ⋙ G).map f = G.map (F.map f) := rfl -- or F.comp_map G X Y f

end functor -- end of section

/-!
One can also check that associativity of composition of functors is definitionally true,
although we've observed that relying on this can result in slow proofs. (One should
rather use the natural isomorphisms provided in `src/category_theory/whiskering.lean`.)

## Getting started with natural transformations

A natural transformation is a morphism between functors. If `F` and `G` are functors from `C` to `D`
then a natural transformation is a map `F X ⟶ G X` for each object `X : C` plus the theorem that if
`f : X ⟶ Y` is a morphism then the two routes from `F X` to `G Y` are the same. One might imagine
that this is now another layer of notation, but fortunately the `category_theory.functor_category`
import gives the type of functors from `C` to `D` a category structure, which means that we can just
use morphism notation for natural transformations.
-/

section nat_trans

variables {C : Type*} [category C] {D : Type*} [category D]

variables (X Y : C)

variable (f : X ⟶ Y)

variables (F G H : C ⥤ D)

variables (α : F ⟶ G) (β : G ⟶ H) -- natural transformations (note it's the usual `\hom` arrow here)

-- Composition of natural transformations is just composition of morphisms:
example : F ⟶ H := α ≫ β

-- Applying natural transformation to an object:
example (X : C) : F.obj X ⟶ G.obj X := α.app X

/- The diagram coming from g and α

    F(f)
F X ---> F Y
 |        |
 |α(X)    |α(Y)
 v        v
G X ---> G Y
    G(f)

commutes.
-/

example : F.map f ≫ α.app Y = (α.app X) ≫ G.map f := α.naturality f

end nat_trans -- section

/-!
## What next?

There are several lean files in the [category theory docs directory of
mathlib](https://github.com/leanprover-community/mathlib/tree/master/docs/tutorial/category_theory)
which give further examples of using the category theory library in Lean.
-/
