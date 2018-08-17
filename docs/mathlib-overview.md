# An overview of mathlib

This is an overview of mathlib as it was on 12th August 2018.

A mathematician might be surprised about what is currently in mathlib, because it does not really correspond to how mathematics is built up in a standard undergraduate mathematics degree. For example, there is currently no basic theory of matrices, in particular no link between matrices and linear maps, no proof that det(AB)=det(A)det(B), and so on; such things are often taught very early in a mathematics degree. On the other hand there is the theory of localisation of rings at multiplicative sets, and the theory of measure spaces, which are typically taught in a third or higher year course. Why is this? The reason is that we do not want to have to prove the same thing more than once, and this changes the way that mathematics is built. What are the reasons that the link between matrices and linear maps is stressed early on in a mathematics degree? Perhaps it is for pedagogical reasons -- abstract vector spaces are a useful concept in statistics and applied mathematics, and introducing them via concrete examples such as real 3-space is probably good for pedagogical reasons. But neither pedagogy nor applications outside pure mathematics are particularly high on mathlib's agenda.

The approach taken by mathlib is far more akin to that of Bourbaki, a group of French mathematicians who wrote many volumes of mathematics with the ultimate goal of building it from scratch. Mathlib is doing exactly the same thing. Bourbaki stressed working in the maximal generality -- for example, you will not find a proof of the open mapping theorem for Banach spaces over the reals in Bourbaki, you will find it proved for Banach spaces over an arbitrary complete field; this means that number theorists can apply the theorem to Banach spaces over the p-adic numbers, for example (and nowadays in p-adic analysis they do just that). To give another example, the theory of Cauchy sequences is set up for sequences taking values in a general ring equipped with an absolute value function to a linearly ordered field. All of this theory is set up before the real numbers are even defined -- indeed the point of setting up the theory in this generality is precisely so that the real numbers can be defined as equivalence classes of Cauchy sequences of rationals, once one has proved that the rationals are a ring and a linearly ordered field, and defined an absolute value function from the rationals to the rationals. This approach would be a pedagogical nightmare.

This design decision has consequences, which were also consequences for Bourbaki. In an attempt to unify various proofs and work in the maximal generality, Bourbaki introduced notions such as filters. Very little is said about the notion of a filter in a typical undergraduate mathematics degree, but using filters unifies various notions of a limit, and there is a 70 kilobyte file (long for mathlib standards) `order/filter.lean` proving lots of basic results about filters and setting up a very general notion of limit via the `tendsto` function. This has consequences which might seem strange for mathematicians. For example the definition of a compact topological space is expressed in terms of filters. Does this mean that to work with compact topological spaces in Lean, a mathematician has to learn all about filters? No it does not! Because after introducing a definition in mathlib, the authors often then prove all the absolutely fundamental basic results about the definition as part of what is called the "interface" or the "API" to the definition. For example, in the mathlib file `analysis/topology/topological_space.lean`, in the section called `compact`, the lemma `compact_iff_finite_subcover` is proved, which shows that a subset of a topological space is compact if and only if every open cover has a finite subcover. Indeed, part of the art of writing mathlib is to make sure that every definition has a robust API to go with it, so that mathematicians can use the definition the way they want to.

[Editor's note: my impression is that one place where mathematicians really play fast and loose is when it comes to manipulating finite sets; mathematicians have a robust intuitive feeling for how one can manipulate them and often do things such as re-arranging finite sums in a way which mathlib currently struggles to emulate; however the interface is being actively worked upon, and will get better over time. Another place where beginners seem to struggle is that mathematicians often move between natural, integer, rational, real and complex numbers without any comment; all of these types are different in Lean and one has to explicitly move from one type to another, and there is currently a "knack" to making this happen seamlessly in Lean.]

# What is currently in mathlib?

Because of the nature of the way mathematics is being built here, as already mentioned above, mathematicians might find what is in mathlib surprising. However, as it grows, it will begin to reflect more accurately what mathematicians actually care about. Many of the key definitions in mathlib come with robust API's, but mathematicians need to be clear what this means. A basic robust API for the theory of groups does not mean Sylow's theorems or even the first isomorphism theorem. It means simply that users have easy access to the definition and basic properties of groups such as `(a b)^(-1) = b^(-1) a^(-1)`, or that `a c = b c -> a = b`. The harder stuff comes later.

Note that mathlib is currently being actively developed, and new things tend to appear on almost a weekly basis. In particular, the list below might get out of date very quickly.


### Algebra

There is a robust API for groups, rings, commutative rings, and fields, as well as modules over rings. There are also robust APIs for weaker objects such as monoids and semirings. There is also a robust API for several different classes of orderings, such as ordered groups, ordered fields and so on. Most of this theory is developed either in core Lean or in `mathlib/algebra/`.

Within the `group_theory` directory there is some more advanced group theory. For example the theory of cosets, subgroups, and quotients, the theory of group actions, free groups, and the definition of the signature of a permutation for an element of a symmetric group.

Within the `linear_algebra` directory there are basic constructions for modules, for example maps between modules, submodules and quotient modules, as well as a theory of multivariate polynomials over rings. The theory of polynomials in one variable is developed much further, in `data/polynomial.lean`.

Within the `ring_theory` directory there is the theory of ideals, including prime and maximal ideals, plus an API for quotient rings. There is also an API for localisation, including definitions and universal properties.

In the future it would be good to have some of the theory of finite-dimensional vector spaces and matrices, and this would open the door to some more advanced algebra such as algebraic number theory and representation theory of finite groups.

### Analysis

As well as definitions of the real and complex numbers (and also non-negative reals, plus a type for "extended" non-negative reals obtained by adding +infinity), there is a general theory of limits (sometimes written in the language of filters, but with an API which enables mathematicians to use them the way they would normally). Much of this is in the directories `data/real/` and `analysis/`, with a little more in `data/analysis/`. Within `analysis/measure_theory/` there is an API for Borel spaces and measure spaces, including Lebesgue measure. 

It would be nice in the future to have some basic facts about power series, for example that they are continuous within their radius of convergence. There is also nothing at all about differentiability.

### Topology

Surprisingly located in `analysis/topology/`, the basic topology files contain an API for topological spaces and continuous maps, as well as the theory of uniform spaces and (in `analysis/`) metric spaces. There is also an API for topological groups and rings (as well as topological monoids and various other things it was appropriate to include), as well as a very general theory of limits (via filters) and a basic API for infinite sums.

### Category theory

Because the categories that mathematicians want to work with are often not sets, there are technical foundational issues here. The category theory library for mathematicians is in `category_theory/` and currently only has a few basic definitions (functors, natural transformations), which have been hard won. Do not confuse this with the `category/` directory in mathlib, which is mostly for functional programming tools, using category theory in the computer scientist's sense of endofunctors of the category of types.

### Number theory

There is very little here beyond APIs for naturals, integers and rationals, because a general theory of number fields needs basic results about finite-dimensional vector spaces and Noetherian rings and modules, neither of which are present, and basic analytic number theory will need some basic differential and integral calculus, which is also not present. The delicate result that the power function is Diophantine is proved -- this is a key step in Matiyesevich's resolution of Hilbert's 10th problem. Along the way a basic theory of Pell's equation is developed, involving developing some arithmetic of the ring `Z[sqrt(d)]` for d a non-square.

### Other mathematical theories and objects.

Basic propositional logic is in `logic/`.

The `order/` directory contains the theories of lattices and complete lattices, boolean algebras, filters and Galois connections, which are not often run into in a mathematics degree, although they are the sorts of things which need to be developed if one is to develop mathematics a la Bourbaki. Ordinals and cardinals, as well as a model of ZFC inside Lean, are in `set_theory/`.

`computability/` is stuff like the halting problem. 


### Programming

The directory `data/equiv/` contains an API for the concept of two objects being in bijection with one another. The directories `data/list/`, `data/set` and `data/sigma` contain more advanced APIs for lists, sets and sigma types than are given in core Lean. Also in `data/` is more advanced APIs for booleans, characters, finite sets, multisets (that is, finite sets where elements can appear with multiplicity greater than one) and subtype, amongst many other things which form part of the general programming framework. These are not necessary immediately upon getting started, but become useful when building more complicated proofs, definitions, or tactics. There is also `category/`, with a few extras on monads and category theory as used in functional programming.

### Tactics
`meta/` and `tactic/` contain new tactics defined in mathlib, and are beyond the scope of this overview. See the [documentation](https://github.com/leanprover/mathlib/blob/master/docs/tactics.md) and [test cases](https://github.com/leanprover/mathlib/tree/master/tests).

