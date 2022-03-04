/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import analysis.normed_space.dual
import analysis.normed_space.star.basic
import analysis.complex.basic
import analysis.inner_product_space.adjoint

/-!
# Von Neumann algebras

We give the "abstract" and "concrete" definitions of a von Neumann algebra.
We still have a major project ahead of us to show the equivalence between these definitions!

An abstract von Neumann algebra `wstar_algebra M` is a C^* algebra with a Banach space predual,
per Sakai (1971).

A concrete von Neumann algebra `von_neumann_algebra H` (where `H` is a Hilbert space)
is a *-closed subalgebra of bounded operators on `H` which is equal to its double commutant.

We'll also need to prove the von Neumann double commutant theorem,
that the concrete definition is equivalent to a *-closed subalgebra which is weakly closed.
-/

universes u v

/--
Sakai's definition of a von Neumann algebra as a C^* algebra with a Banach space predual.

So that we can unambiguously talk about these "abstract" von Neumann algebras
in parallel with the "concrete" ones (weakly closed *-subalgebras of B(H)),
we name this definition `wstar_algebra`.
-/
class wstar_algebra (M : Type u) [normed_ring M] [star_ring M] [cstar_ring M]
  [module ℂ M] [normed_algebra ℂ M] [star_module ℂ M] :=
(exists_predual : ∃ (X : Type u) [normed_group X] [normed_space ℂ X] [complete_space X],
  nonempty (normed_space.dual ℂ X ≃ₗᵢ⋆[ℂ] M))

open_locale inner_product

/--
The double commutant definition of a von Neumann algebra,
as a *-closed subalgebra of bounded operators on a Hilbert space,
which is equal to its double commutant.

Note that this definition is parameterised by the Hilbert space
on which the algebra faithfully acts, as is standard in the literature.
See `wstar_algebra` for the abstract notion (a C^*-algebra with Banach space predual).

Note this is a bundled structure, parameterised by the Hilbert space `H`,
rather than a typeclass on the type of elements.
Thus we can't say that the bounded operators `H →L[ℂ] H` form a `von_neumann_algebra`
(although we will later construct the instance `wstar_algebra (H →L[ℂ] H)`),
and instead will use `⊤ : von_neumann_algebra H`.
-/
@[nolint has_inhabited_instance]
structure von_neumann_algebra (H : Type u) [inner_product_space ℂ H] [complete_space H] extends
  M : star_subalgebra ℂ (H →L[ℂ] H) :=
(double_commutant : centralizer (centralizer (M : set (H →L[ℂ] H))) = M)

/--
Forgetting that a von Neumann algebra is equal to its double commutant
(equivalently, is closed in the weak and strong operator topologies),
and just remembering the underlying *-subalgebra.
-/
add_decl_doc von_neumann_algebra.to_star_subalgebra
