/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.algebra.polynomial
import topology.continuous_function.basic

/-!
# Constructions relating polynomial functions and continuous functions.

This file is just a stub at the moment, but will grow with subsequent PRs
giving abstract statements of the Weierstrass approximation theorem,
and the Stone-Weierstrass theorem.
-/

namespace polynomial

variables {R : Type*} [semiring R] [topological_space R] [topological_semiring R]

/--
Every polynomial with coefficients in a topological semiring gives a (bundled) continuous function.
-/
def as_continuous_map (p : polynomial R) : C(R, R) :=
⟨λ x : R, p.eval x, by continuity⟩

/--
A polynomial as a continuous function,
with domain restricted to some subset of the semiring of coefficients.

(This is particularly useful when restricting to compact sets, e.g. `[0,1]`.)
-/
def as_continuous_map_on (p : polynomial R) (X : set R) : C(X, R) :=
⟨λ x : X, p.as_continuous_map x, by continuity⟩

end polynomial
