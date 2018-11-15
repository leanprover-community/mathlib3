# Maths in Lean : category theory

The `category` typeclass is defined in [category_theory/category.lean](https://github.com/leanprover/mathlib/blob/master/category_theory/category.lean).
It depends on the type of the objects, so for example we might write `category (Type u)` if we're talking about a category whose objects are types (in universe `u`).
Some care is needed with universes (see the section [Universes](##markdown-header-universes)), and end users may often prefer the abbreviations `small_category` and `large_category`.

Functors (which are a structure, not a typeclass) are defined in [category_theory/functor.lean](https://github.com/leanprover/mathlib/blob/master/category_theory/functor/default.lean),
along with identity functors and functor composition.

Natural transformations, and their compositions, are defined in [category_theory/natural_transformation.lean](https://github.com/leanprover/mathlib/blob/master/category_theory/natural_transformation.lean).

The category of functors and natural transformations between fixed categories `C` and `D`
is defined in [category_theory/functor_category.lean](https://github.com/leanprover/mathlib/blob/master/category_theory/functor_category.lean).

Cartesian products of categories, functors, and natural transformations appear in
 [category_theory/products.lean](https://github.com/leanprover/mathlib/blob/master/category_theory/products.lean). (Product in the sense of limits will appear elsewhere soon!)

 The category of types, and the hom pairing functor, are defined in  [category_theory/types.lean](https://github.com/leanprover/mathlib/blob/master/category_theory/types.lean).

## Universes

Unfortunately in a category theory library we have to deal with universes carefully. We have the following:

````
category.{u₁ v₁}     : Type (max (u₁+1) (v₁+1))
C                    : category.{u₁ v₁}
D                    : category.{u₂ v₂}
functor C D          : Type (max u₁ u₂ v₁ v₂)
F G                  : functor C D
nat_trans F G        : Type (max u₁ v₂)
functor.category C D : category.{(max u₁ u₂ v₁ v₂) (max u₁ v₂)}
````

Note then that if we specialise to small categories, where `uᵢ = vᵢ`, then
`functor.category C D : category.{(max u₁ u₂) (max u₁ u₂)}`, and so is again
a small category. If `C` is a small category and `D` is a large category
(i.e. `u₂ = v₂+1`), and `v₂ = v₁` then we have
`functor.category C D : category.{v₁+1 v₁}` so is again a large category.

Whenever you want to write code uniformly for small and large categories
(which you do by talking about categories whose universe levels `u` and `v`
are unrelated), you will find that Lean's `variable` mechanism doesn't always
work, and the following trick is often helpful:

````
variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟
````

Some care with using `section ... end` can be required to make sure these
included variables don't end up where they aren't wanted.

## Notation

### Categories

We use the `⟶` (`\hom`) arrow to denote sets of morphisms, as in `X ⟶ Y`.
This leaves the actual category implicit; it is inferred from the type of `X` and `Y` by typeclass inference.

We use `𝟙` (`\b1`) to denote identity morphisms, as in `𝟙 X`.

We use `≫` (`\gg`) to denote composition of morphisms, as in `f ≫ g`, which means "`f` followed by `g`".
You may prefer write composition in the usual convention, using `⊚` (`\oo` or `\circledcirc`), as in `f ⊚ g` which means "`g` followed by `f`". To do so you'll need to add this notation locally, via
```
local notation f ` ⊚ `:80 g:80 := category.comp g f
```

### Isomorphisms
We use `≅` for isomorphisms.

### Functors
We use `⥤` (`\func`) to denote functors, as in `C ⥤ D` for the type of functors from `C` to `D`.
(Unfortunately `⇒` is reserved in core: https://github.com/leanprover/lean/blob/master/library/init/relator.lean, so we can't use that here.)

We use `F.obj X` to denote the action of a functor on an object.
We use `F.map f` to denote the action of a functor on a morphism`.

Functor composition can be written as `F ⋙ G`.

### Natural transformations
We use `⟹` (`\nattrans` or `\==>`) to denote the type of natural transformations, e.g. `F ⟹ G`.
We use `⇔` (`\<=>`) to denote the type of natural isomorphisms.

We use `τ.app X` for the components of a natural transformation.

For vertical and horiztonal composition of natural transformations we "cutely" use `⊟` (`\boxminus`) and `◫` (currently untypeable, but we could ask for `\boxvert`).
