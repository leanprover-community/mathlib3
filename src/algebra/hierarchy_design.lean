/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Eric Weiser
-/
import tactic.doc_commands

/-!
# Documentation of the algebraic hierarchy

A library note giving advice on modifying the algebraic hierarchy.
(It is not intended as a "tour".)

TODO: Add sections about interactions with topological typeclasses, and order typeclasses.

-/

/--
# The algebraic hierarchy

In any theorem proving environment,
there are difficult decisions surrounding the design of the "algebraic hierarchy".

There is a danger of exponential explosion in the number of gadgets,
especially once interactions between algebraic and order/topological/etc structures are considered.

In mathlib, we try to avoid this by only introducing new algebraic typeclasses either
1. when there is "real mathematics" to be done with them, or
2. when there is a meaninful gain in simplicity by factoring out a common substructure.

(As examples, at this point we don't have `loop`, or `unital_magma`,
but we do have `lie_submodule` and `topological_field`!
We also have `group_with_zero`, as an exemplar of point 2.)

Generally in mathlib we use the extension mechanism (so `comm_ring` extends `ring`)
rather than mixins (e.g. with separate `ring` and `comm_mul` classes),
in part because of the potential blow-up in term sizes described at
https://www.ralfj.de/blog/2019/05/15/typeclasses-exponential-blowup.html
However there is tension here, as it results in considerable duplication in the API,
particularly in the interaction with order structures.

This library note is not intended as a design document
justifying and explaining the history of mathlib's algebraic hierarchy!
Instead it is intended as a developer's guide, for contributors wanting to extend
(either new leaves, or new intermediate classes) the algebraic hierarchy as it exists.

(Ideally we would have both a tour guide to the existing hierarchy,
and an account of the design choices.
See https://arxiv.org/abs/1910.09336 for an overview of mathlib as a whole,
with some attention to the algebraic hierarchy and
https://leanprover-community.github.io/mathlib-overview.html
for a summary of what is in mathlib today.)

## Instances

When adding a new typeclass `Z` to the algebraic hierarchy
one should attempt to add the following constructions and results,
when applicable:

* Instances transferred elementwise to products, like `prod.monoid`.
  See `algebra.group.prod` for more examples.
  ```
  instance prod.Z [Z M] [Z N] : Z (M × N) := ...
  ```
* Instances transferred elementwise to pi types, like `pi.monoid`.
  See `algebra.group.pi` for more examples.
  ```
  instance pi.Z [∀ i, Z $ f i] : Z (Π i : I, f i) := ...
  ```
* Instances transferred to `opposite M`, like `opposite.monoid`.
  See `algebra.opposites` for more examples.
  ```
  instance opposite.Z [Z M] : Z (opposite M) := ...
  ```
* Instances transferred to `ulift M`, like `ulift.monoid`.
  See `algebra.group.ulift` for more examples.
  ```
  instance ulift.Z [Z M] : Z (ulift M) := ...
  ```
* Definitions for transferring the proof fields of instances along
  injective or surjective functions that agree on the data fields,
  like `function.injective.monoid` and `function.surjective.monoid`.
  We make these definitions `@[reducible]`, see note [reducible non-instances].
  See `algebra.group.inj_surj` for more examples.
  ```
  @[reducible]
  def function.injective.Z [Z M₂] (f : M₁ → M₂) (hf : injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) : Z M₁ := ...

  @[reducible]
  def function.surjective.Z [Z M₁] (f : M₁ → M₂) (hf : surjective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) : Z M₂ := ...
  ```
* Instances transferred elementwise to `finsupp`s, like `finsupp.semigroup`.
  See `data.finsupp.pointwise` for more examples.
  ```
  instance finsupp.Z [Z β] : Z (α →₀ β) := ...
  ```
* Instances transferred elementwise to `set`s, like `set.monoid`.
  See `algebra.pointwise` for more examples.
  ```
  instance set.Z [Z α] : Z (set α) := ...
  ```
* Definitions for transferring the entire structure across an equivalence, like `equiv.monoid`.
  See `data.equiv.transfer_instance` for more examples. See also the `transport` tactic.
  ```
  def equiv.Z (e : α ≃ β) [Z β] : Z α := ...
  /- When there is a new notion of `Z`-equiv: -/
  def equiv.Z_equiv (e : α ≃ β) [Z β] : by { letI := equiv.Z e, exact α ≃Z β } := ...
  ```

## Subobjects

When a new typeclass `Z` adds new data fields,
you should also create a new `sub_Z` `structure` with a `carrier` field.

This can be a lot of work; for now try to closely follow the existing examples
(e.g. `submonoid`, `subring`, `subalgebra`).
We would very much like to provide some automation here, but a prerequisite will be making
all the existing APIs more uniform.

If `Z` extends `Y`, then `sub_Z` should usually extend `sub_Y`.

When `Z` adds only new proof fields to an existing structure `Y`,
you should provide instances transferring
`Z α` to `Z (sub_Y α)`, like `submonoid.to_comm_monoid`.
Typically this is done using the `function.injective.Z` definition mentioned above.
```
instance sub_Y.to_Z [Z α] : Z (sub_Y α) :=
coe_injective.Z coe ...
```

## Morphisms and equivalences

## Category theory

For many algebraic structures, particularly ones used in representation theory, algebraic geometry,
etc., we also define "bundled" versions, which carry `category` instances.

These bundled versions are usually named in camel case,
so for example we have `AddCommGroup` as a bundled `add_comm_group`,
and `TopCommRing` (which bundles together `comm_ring`, `topological_space`, and `topological_ring`).

These bundled versions have many appealing features:
* a uniform notation for morphisms `X ⟶ Y`
* a uniform notation (and definition) for isomorphisms `X ≅ Y`
* a uniform API for subobjects, via the partial order `subobject X`
* interoperability with unbundled structures, via coercions to `Type`
  (so if `G : AddCommGroup`, you can treat `G` as a type,
  and it automatically has an `add_comm_group` instance)
  and lifting maps `AddCommGroup.of G`, when `G` is a type with an `add_comm_group` instance.

If, for example you do the work of proving that a typeclass `Z` has a good notion of tensor product,
you are strongly encouraged to provide the corresponding `monoidal_category` instance
on a bundled version.
This ensures that the API for tensor products is complete, and enables use of general machinery.
Similarly if you prove universal properties, or adjunctions, you are encouraged to state these
using categorical language!

One disadvantage of the bundled approach is that we can only speak of morphisms between
objects living in the same type-theoretic universe.
In practice this is rarely a problem.

# Making a pull request

With so many moving parts, how do you actually go about changing the algebraic hierarchy?

We're still evolving how to handle this, but the current suggestion is:

* If you're adding a new "leaf" class, the requirements are lower,
  and an initial PR can just add whatever is immediately needed.
* A new "intermediate" class, especially low down in the hierarchy,
  needs to be careful about leaving gaps.

In a perfect world, there would be a group of simultaneous PRs that basically cover everything!
(Or at least an expectation that PRs may not be merged immediately while waiting on other
PRs that fill out the API.)

However "perfect is the enemy of good", and it would also be completely reasonable
to add a TODO list in the main module doc-string for the new class,
briefly listing the parts of the API which still need to be provided.
Hopefully this document makes it easy to assemble this list.

Another alternative to a TODO list in the doc-strings is adding github issues.


-/
library_note "the algebraic hierarchy"

/--
Some definitions that define objects of a class cannot be instances, because they have an
explicit argument that does not occur in the conclusion. An example is `preorder.lift` that has a
function `f : α → β` as an explicit argument to lift a preorder on `β` to a preorder on `α`.

If these definitions are used to define instances of this class *and* this class is an argument to
some other type-class so that type-class inference will have to unfold these instances to check
for definitional equality, then these definitions should be marked `@[reducible]`.

For example, `preorder.lift` is used to define `units.preorder` and `partial_order.lift` is used
to define `units.partial_order`. In some cases it is important that type-class inference can
recognize that `units.preorder` and `units.partial_order` give rise to the same `has_le` instance.
For example, you might have another class that takes `[has_le α]` as an argument, and this argument
sometimes comes from `units.preorder` and sometimes from `units.partial_order`.
Therefore, `preorder.lift` and `partial_order.lift` are marked `@[reducible]`.
-/
library_note "reducible non-instances"
