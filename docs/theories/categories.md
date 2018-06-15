# Maths in Lean : category theory

The `category` typeclass is defined in [category_theory/category.lean](https://github.com/leanprover/mathlib/blob/master/category_theory/category.lean).
It depends on the type of the objects, so for example we might write `category (Type u)` if we're talking about a category whose objects are types (in universe `u`).
Some care is needed with universes (see the section [Universes](##markdown-header-universes)), and end users may often prefer the abbreviations `small_category` and `large_category`.

Functors (which are a structure, not a typeclass) are defined in [category_theory/functor/default.lean](https://github.com/leanprover/mathlib/blob/master/category_theory/functor/default.lean),
along with identity functors and functor composition.

Natural transformations, and their compositions, are defined in [category_theory/natural_transformation.lean](https://github.com/leanprover/mathlib/blob/master/category_theory/natural_transformation.lean).

## Universes

Unfortunately in a category theory library we have to deal with universes carefully. We have the following:

````
category.{u₁ v₁}          : Type (max (u₁+1) (v₁+1))
C                         : category.{u₁ v₁}
D                         : category.{u₂ v₂}
Functor C D               : Type (max u₁ u₂ v₁ v₂)
F G                       : Functor C D
NaturalTransformation F G : Type (max u₁ v₂)
FunctorCategory C D       : category.{(max u₁ u₂ v₁ v₂) (max u₁ v₂)}
````

Note then that if we specialise to small categories, where `uᵢ = vᵢ`, then `FunctorCategory C D : category.{(max u₁ u₂) (max u₁ u₂)}`, and so is again a small category.
If `C` is a small category and `D` is a large category (i.e. `u₂ = v₂+1`), and `v₂ = v₁` then we have `FunctorCategory C D : category.{v₁+1 v₁}` so is again a large category.

Whenever you want to write code uniformly for small and large categories (which you do by talking about categories whose universe levels `u` and `v` are unrelated), you will find that
Lean's `variable` mechanism doesn't always work, and the following trick is often helpful:

````
variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟
````


## Notation

### Categories

We use the `⟶` (`\hom`) arrow to denote sets of morphisms, as in `X ⟶ Y`.
This leaves the actual category implicit; it is inferred from the type of X and Y by typeclass inference.

We use `𝟙` (`\b1`) to denote identity morphisms, as in `𝟙 X`.

We use `≫` (`\gg`) to denote composition of morphisms, as in `f ≫ g`, which means "`f` followed by `g`".
This is the opposite order than the usual convention (which is lame).  

### Isomorphisms
We use `≅` for isomorphisms.

### Functors
We use `↝` (`\leadsto` or `\lea` or `\r~`) to denote functors, as in `C ↝ D` for the type of functors from `C` to `D`.
Unfortunately Johannes reserved `⇒` (`\functor` or `\func`) in core: https://github.com/leanprover/lean/blob/master/library/init/relator.lean, so we can't use that here.
Perhaps this is unnecessary, and it's better to just write `Functor C D`.

Unfortunately, writing application of functors on objects and morphisms merely by function application is problematic.
To do either, we need to use a coercion to a function type, and we aren't allowed to do both this way.
Even doing one (probably application to objects) causes some serious problems to automation. I'll have one more go at this,
but in the meantime:

We use `+>` to denote the action of a functor on an object, as in `F +> X`.
We use `&>` to denote the action of a functor on a morphism, as in `F &> f`.

Functor composition can be written as `F ⋙ G`.

### Natural transformations
We use `⟹` (`\nattrans` or `\==>`) to denote the type of natural transformations, e.g. `F ⟹ G`.
We use `⇔` (`\<=>`) to denote the type of natural isomorphisms.

Unfortunately, while we'd like to write components of natural transformations via function application (e.g. `τ X`),
this requires coercions to function types, which I don't like.

For now we use the notation `τ @> X` for `τ.components X`.

For vertical and horiztonal composition of natural transformations we "cutely" use `⊟` (`\boxminus`) and `◫` (currently untypeable, but we could ask for `\boxvert`).
