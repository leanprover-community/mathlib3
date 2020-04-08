# An overview of mathlib

Note that mathlib is currently being actively developed, and new things tend to appear on almost a weekly basis. In particular, the list below might get out of date very quickly. This page was last updated on 27th December 2019.


### Algebra

Groups. Subgroups, quotients, cosets, centralizers, free groups, abelianisation, Sylow 1.
Rings. primes and irreducibles, characteristic of a ring, ideals, fields, Euclidean domains, principal ideal domains, unique factorization domains, Noetherian rings. Ordered rings and fields. Polynomials and power series. Localisation.
Modules over a ring, direct sums and limits, tensor products.
Lie algebras (definition and basic properties).
Fields: minimal polynomials, finite extensions, algebraic extensions, splitting fields, perfect closure, finite fields.
Vector spaces, bases, finite-dimensional spaces, matrices, linear maps, dual spaces, bilinear and sesquilinear forms.

### Number theory

The [naturals](https://github.com/leanprover-community/mathlib/blob/master/docs/theories/naturals.md), the integers, the rationals.
Primes, uniqueness of factorization. GCDs. Congruences and modular arithmetic. Z is an ED/PID/UFD. Sums of two and four squares, Pell’s equation in cases needed for Matiyasevich’s theorem (d=a^2-1). Euler’s Totient function. Quadratic reciprocity.
[p-adic numbers](https://github.com/leanprover-community/mathlib/blob/master/docs/theories/padics.md). Hensel’s Lemma.

### Analysis

The reals and complex numbers.
Basic theory of differentiation of functions of one and several variables. The Intermediate Value Theorem, Rolle's theorem, the Mean Value Theorem. The chain rule, product rule, mean value theorem, C^n and C^infty functions.
Sups and Infs. Sequences and sums. Sum of a geometric progression, exp and log, trig and inverse trig functions, basic properties (double angle formulae etc). Pi, and proof that it’s between 3.141 and 3.142
The complex numbers are algebraically closed.
Definition of real manifold, manifolds with corners. Vector bundles, tangent bundle.

### Topology

Metric spaces. Cauchy sequences, Hausdorff distance and Gromov-Hausdorff distance. Completions. Lipschitz continuous functions.
Uniform spaces, uniform continuity, completions.
Topological spaces, open and closed sets, compact sets, connected sets. Separation axioms T0 to T4. Topological groups, rings, fields. Continuous maps, homeomorphisms, the compact-open topology. Sequences, sequential spaces, sequentially continuous functions. The Stone-Cech compactification. Topological fibre bundles. Baire theorem. Normed vector spaces, operator norm.
Presheaves on a topological space, stalks.

[See here for more details information about topology in mathlib](https://github.com/leanprover-community/mathlib/blob/master/docs/theories/topology.md).

### Measure theory.

Sigma algebras, measure spaces, Borel measurable functions, probability spaces, the Lebesgue integral, L^1 spaces, the Bochner integral, the Giry monad (i.e. measures on a measurable space form a measurable space).

### Category theory

Categories, small and large categories.
Functors, full and faithful functors, natural transformations, the Yoneda lemma. Equivalence of categories, sums, products, limits, adjoints. Monoidal categories.
The category of commutative rings, the category of modules over a ring, the category of measurable spaces.

[See here for more detailed information about category theory in mathlib](https://github.com/leanprover-community/mathlib/blob/master/docs/theories/category_theory.md).

### Other mathematical theories and objects.

Ordinals and cardinals. A model of ZFC.
Continued fractions. Turing machines, the Halting problem.
Conway games. The Fibonacci sequence. The hyperreals. Cubing a cube.

