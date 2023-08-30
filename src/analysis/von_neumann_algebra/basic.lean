/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import analysis.normed_space.dual
import analysis.normed_space.star.basic
import analysis.complex.basic
import analysis.inner_product_space.adjoint
import algebra.star.subalgebra

/-!
# Von Neumann algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

Note that for now we only assert the mere existence of predual, rather than picking one.
This may later prove problematic, and need to be revisited.
Picking one may cause problems with definitional unification of different instances.
One the other hand, not picking one means that the weak-* topology
(which depends on a choice of predual) must be defined using the choice,
and we may be unhappy with the resulting opaqueness of the definition.
-/
class wstar_algebra (M : Type u) [normed_ring M] [star_ring M] [cstar_ring M]
  [module ℂ M] [normed_algebra ℂ M] [star_module ℂ M] :=
(exists_predual : ∃ (X : Type u) [normed_add_comm_group X] [normed_space ℂ X] [complete_space X],
  nonempty (normed_space.dual ℂ X ≃ₗᵢ⋆[ℂ] M))

-- TODO: Without this, `von_neumann_algebra` times out. Why?
set_option old_structure_cmd true

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
@[nolint has_nonempty_instance]
structure von_neumann_algebra (H : Type u)
  [normed_add_comm_group H] [inner_product_space ℂ H] [complete_space H] extends
  star_subalgebra ℂ (H →L[ℂ] H) :=
(centralizer_centralizer' :
  set.centralizer (set.centralizer carrier) = carrier)

/--
Consider a von Neumann algebra acting on a Hilbert space `H` as a *-subalgebra of `H →L[ℂ] H`.
(That is, we forget that it is equal to its double commutant
or equivalently that it is closed in the weak and strong operator topologies.)
-/
add_decl_doc von_neumann_algebra.to_star_subalgebra

namespace von_neumann_algebra
variables {H : Type u} [normed_add_comm_group H] [inner_product_space ℂ H] [complete_space H]

instance : set_like (von_neumann_algebra H) (H →L[ℂ] H) :=
⟨von_neumann_algebra.carrier, λ S T h, by cases S; cases T; congr'⟩

instance : star_mem_class (von_neumann_algebra H) (H →L[ℂ] H) :=
{ star_mem := λ s a, s.star_mem' }

instance : subring_class (von_neumann_algebra H) (H →L[ℂ] H) :=
{ add_mem := add_mem',
  mul_mem := mul_mem',
  one_mem := one_mem',
  zero_mem := zero_mem' ,
  neg_mem := λ s a ha, show -a ∈ s.to_star_subalgebra, from neg_mem ha }

@[simp] lemma mem_carrier {S : von_neumann_algebra H} {x : H →L[ℂ] H}:
  x ∈ S.carrier ↔ x ∈ (S : set (H →L[ℂ] H)) := iff.rfl

@[ext] theorem ext {S T : von_neumann_algebra H} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
set_like.ext h

@[simp] lemma centralizer_centralizer (S : von_neumann_algebra H) :
  set.centralizer (set.centralizer (S : set (H →L[ℂ] H))) = S := S.centralizer_centralizer'

/-- The centralizer of a `von_neumann_algebra`, as a `von_neumann_algebra`.-/
def commutant (S : von_neumann_algebra H) : von_neumann_algebra H :=
{ carrier := set.centralizer (S : set (H →L[ℂ] H)),
  centralizer_centralizer' := by rw S.centralizer_centralizer,
  .. star_subalgebra.centralizer ℂ (S : set (H →L[ℂ] H)) (λ a (ha : a ∈ S), (star_mem ha : _)) }

@[simp] lemma coe_commutant (S : von_neumann_algebra H) :
  ↑S.commutant = set.centralizer (S : set (H →L[ℂ] H)) := rfl

@[simp] lemma mem_commutant_iff {S : von_neumann_algebra H} {z : H →L[ℂ] H} :
  z ∈ S.commutant ↔ ∀ g ∈ S, g * z = z * g :=
iff.rfl

@[simp] lemma commutant_commutant (S : von_neumann_algebra H) :
  S.commutant.commutant = S :=
set_like.coe_injective S.centralizer_centralizer'

end von_neumann_algebra
