# Maths in lean : Topological Spaces.

The `topological_space` typeclass is defined in mathlib,
in `topology/basic.lean`. There are over 4500
lines of code in `topology` at the time of writing,
covering the basics of topological spaces, continuous functions,
topological groups and rings, and infinite sums. These docs
are just concerned with the contents of the `topological_space.lean`
file.

### The basic typeclass.

The `topological_space` typeclass is an inductive type, defined
as a structure on a type `α` in the obvious way: there is an `is_open`
predicate, telling us when `U : set α` is open, and then the axioms
for a topology (pedantic note: the axiom that the empty set is open
is omitted, as it follows from the fact that a union of open sets
is open, applied to the empty union!).

Note that there are two ways of formalising the axiom that an arbitrary
union of open sets is open: one could either ask that given a set
of open sets, their union is open, or one could ask that given
a function from some index set `I` to the set of open sets, the union
of the values of the function is open. Mathlib goes for the first
one, so the axiom is

```lean
is_open_sUnion : ∀(s : set (set α)), (∀t∈s, is_open t) → is_open (⋃₀ s)
```

and then the index set version is a lemma:

```lean
lemma is_open_Union {f : ι → set α} (h : ∀i, is_open (f i)) : is_open (⋃i, f i)
```

Note the naming conventions, standard across mathlib, that `sUnion`
is a union over sets and `Union` (with a capital U) is a union over
the image of a function on an indexing set. The capital U's are
to indicate a union of arbitrary size, as opposed to `union`, which
indicates a union of two sets:

```lean
lemma is_open_union (h₁ : is_open s₁) (h₂ : is_open s₂) : is_open (s₁ ∪ s₂)
```

The predicate `is_closed`, and functions `interior`, `closure`, and
`frontier` (closure minus interior,
sometimes called boundary in mathematics) are defined, and basic
properties about them are proved. For example

```lean
import topology.basic
open topological_space
variables {X : Type} [topological_space X] {U V C D Y Z : set X}

example : is_closed C → is_closed D → is_closed (C ∪ D) := is_closed_union

example : is_open ( -C) ↔ is_closed C := is_open_compl_iff

example : is_open U → is_closed C → is_open (U - C) := is_open_diff

example : interior Y = Y ↔ is_open Y := interior_eq_iff_open

example : Y ⊆ Z → interior Y ⊆ interior Z := interior_mono

example : is_open Y ↔ ∀ x ∈ Y, ∃ U ⊆ Y, is_open U ∧ x ∈ U := is_open_iff_forall_mem_open

example : closure Y = Y ↔ is_closed Y := closure_eq_iff_is_closed

example : closure Y = - interior (- Y) := closure_eq_compl_interior_compl
```

### Filters

In mathlib, unlike the typical approach in a mathematics textbook, extensive
use is made of filters as a tool in the theory of topological spaces. Let
us briefly review the notion of a filter in mathematics. A filter on a set
`X` is a non-empty collection `F` of subsets of `X` satisfying the following
two axioms:

1) if `U ∈ F` and `U ⊆ V`, then `V ∈ F`; and
2) if `U, V ∈ F` then there exists `W ∈ F` with `W ⊆ U ∩ V`.

Informally, one can think of `F` as the set of "big" subsets of `X`. For example, if `X` is a set and `F` is the set of subsets `Y` of `X` such that `X - Y` is finite, then `F` is a filter. This is called the _cofinite filter_ on `X`.

Note that if `F` is a filter that contains the empty set, then it contains all subsets of `X` by the first axiom. This filter is sometimes called "bottom" (we will see why a little later on). Some references demand that the empty set is not allowed to be in a filter -- Lean does not have this restriction. A filter not containing the empty set is sometimes called a "proper filter".

If `X` is a topological space, and `x ∈ X`, then the _neighbourhood filter_ `nhds x` of `x` is the set of subsets `Y` of `X` such that `x` is in the interior of `Y`. One checks easily that this is a filter (technical point: to see that this is actually the definition of `nhds x` in mathlib, it helps to know that the set of all filters on a type is a complete lattice, partially ordered using `F ≤ G` iff `G ⊆ F`, so the definition, which involves an inf, is actually a union; also, the definition I give is not literally the definition in mathlib, but `lemma nhds_sets` says that their definition is the one here. Note also that this is why the filter with the most sets is called bottom!).

Why are we interested in these filters? Well, given a map `f` from `ℕ` to a topological space `X`, one can check that the resulting sequence `f 0`, `f 1`, `f 2`... tends to `x ∈ F` if and only if the pre-image of any element in the filter `nhds x` is in the cofinite filter on `ℕ` -- this is just another way of saying that given any open set `U` containing `x`, there exists `N` such that for all `n ≥ N`, `f n ∈ U`. So filters provide a way of thinking about limits.

The _principal filter_ `principal Y` attached to a subset `Y` of a set `X` is the collection of all subsets of `X` that contain `Y`. So it's not difficult to convince yourself that the following results should be true:

```lean
example : interior Y = {x | nhds x ≤ filter.principal Y} := interior_eq_nhds

example : is_open Y ↔ ∀ y ∈ Y, Y ∈ (nhds y).sets := is_open_iff_mem_nhds
```

### Compactness with filters

As a consequence of the filter-centric approach, some definitions in mathlib
look rather strange to a mathematician who is not used to this approach.
We have already seen a definition using filters
for what it means for a sequence to tend to a limit. The definition
of compactness is also written in filter-theoretic terms:

```lean
/-- A set `s` is compact if every filter that contains `s` also meets every
  neighborhood of some `a ∈ s`. -/
def compact (Y : set X) := ∀F, F ≠ ⊥ → F ≤ principal Y → ∃y∈Y, F ⊓ nhds y ≠ ⊥
```

Translated, this says that a subset `Y` of a topological space `X` is compact if for every proper filter `F` on `X`, if `Y` is an element of `F` then there's an element `y` of `Y` such that the smallest filter containing both F and the neighbourhood filter of `y` is not the filter of all subsets of `X` either. This should be thought of as being the correct general analogue of the Bolzano-Weierstrass theorem, that in a compact subspace of `ℝ^n`, any sequence has a convergent subsequence.

One might ask why this definition of compactness has been chosen, rather than the standard one about open covers having finite subcovers. The reasons for this are in some sense computer-scientific rather than mathematical -- the issue should not be what definition is ultimately chosen (indeed the developers should feel free to choose whatever definition they like as long as it is logically equivalent to the usual one, and they might have reasons related to non-mathematical points such as running times), the issue should be how to prove that the inbuilt definition is equivalent to the one you want to use in practice. And fortunately, we have

```lean
example : compact Y ↔
  (∀ cov : set (set X), (∀ U ∈ cov, is_open U) → Y ⊆ ⋃₀ cov →
    ∃ fincov ⊆ cov, set.finite fincov ∧ Y ⊆ ⋃₀ fincov) := compact_iff_finite_subcover
```

so the Lean definition is equivalent to the standard one.

### Hausdorff spaces

In Lean they chose the terminology `t2_space` to mean Hausdorff (perhaps because it is shorter!).

```lean
class t2_space (X : Type) [topological_space X] :=
(t2 : ∀x y, x ≠ y → ∃U V : set X, is_open U ∧ is_open V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅)
```

Of course Hausdorffness is what we need to ensure that limits are unique, but because limits are defined using filters this statements ends up reading as follows:

```lean
lemma tendsto_nhds_unique [t2_space X] {f : β → X} {l : filter β} {x y : X}
  (hl : l ≠ ⊥) (hx : tendsto f l (nhds x)) (hb : tendsto f l (nhds y)) : x = y
```

Note that actually this statement is more general than the classical statement that if a sequence tends to two limits in a Hausdorff space then the limits are the same, because it applies to any non-trivial filter on any set rather than just the cofinite filter on the natural numbers.

### Bases for topologies.

If `X` is a _set_, and `S` is a collection of subsets of `X`, then one can
consider the topology "generated by" `S`, which (as is typical in these
situations) can be defined in two ways: firstly as the intersection
of all the topologies on `X` containing `S` (where we are here identifying
a topology with the underlying collection of open sets), or more constructively
as the sets "generated by" `S` using the axioms of a topological space.
Unsurprisingly, it is this latter definition which is used in Lean, as the
open sets are naturally an inductive type; the open sets are called
`generate_open S` and the topology is `generate_from S`.

The definition of a basis for a topology in mathlib includes an axiom
that the topology is generated from the basis in the sense above, which may make
it hard to prove for an end user that a given set satisfies the definition
directly. However again we have a theorem which reduces us to checking
the two usual axioms for a basis:

```lean
example (B : set (set X)) (h_open : ∀ V ∈ B, is_open V)
  (h_nhds : ∀ (x : X) (U : set X), x ∈ U → is_open U → ∃ V ∈ B, x ∈ V ∧ V ⊆ U) :
is_topological_basis B :=
is_topological_basis_of_open_of_nhds h_open h_nhds
```

### Other things

There are other things involving filters, there are separable, first-countable
and second-countable spaces, product spaces, subspace and quotient
topologies (and more generally pull-back and push-forward of a topology)
and things like t1 and t3 spaces.

## File organization

The following "core" modules form a linear chain of imports. A theorem involving concepts defined in several of these files should be found in the last such file in this ordering.

* `basic`
  Topological spaces. Open and closed subsets, interior, closure and frontier (boundary). Neighborhood filters. Limit of a filter. Locally finite families. Continuity and continuity at a point.
* `order`
  The complete lattice structure on topologies on a fixed set. Induced and coinduced topologies.
* `maps`
  Open and closed maps. "Inducing" maps. Embeddings, open embeddings and closed embeddings. Quotient maps.
* `constructions`
  Building new topological spaces from old ones: products, sums, subspaces and quotients.
* `subset_properties`
  Compactness. Clopen subsets, irreducibility and connectedness. Totally disconnected and totally separated sets and spaces.
* `separation`
  Separation axioms T₀ through T₄, also known as Kolmogorov, Tychonoff or Fréchet, Hausdorff, regular, and normal spaces respectively.

The remaining directories and files, in no particular order:

* `algebra`
  Topological spaces with compatible algebraic or ordered structure.
* `category`
  The categories of topological spaces, uniform spaces, etc.
* `instances`
  Specific topological spaces such as the real numbers and the complex numbers.
* `metric_space`
  The theory of metric spaces; but some notions one might expect to find here are instead generalized to uniform spaces.
* `sheaves`
  Presheaves on a topological space.
* `uniform_space`
  The theory of uniform spaces, including notions such as completeness, uniform continuity and totally bounded sets.
* `bases`
  Bases for filters and topological spaces. Separable, first countable and second countable spaces.
* `bounded_continuous_function`
  Bounded continuous functions from a topological space to a metric space.
* `compact_open`
  The compact-open topology on the space of continuous maps between two topological spaces.
* `continuous_on`
  Neighborhoods within a subset. Continuity on a subset, and continuity within a subset at a point.
* `dense_embedding`
  Embeddings and other functions with dense image.
* `homeomorph`
  Homeomorphisms between topological spaces.
* `list`
  Topologies on lists and vectors.
* `local_homeomorph`
  Homeomorphisms between open subsets of topological spaces.
* `opens`
  The complete lattice of open subsets of a topological space. The types of closed and nonempty compact subsets.
* `sequences`
  Sequential closure and sequential spaces. Sequentially continuous functions.
* `stone_cech`
  The Stone-Čech compactification of a topological space.
