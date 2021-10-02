/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import topology.basic
import topology.constructions
import topology.algebra.ordered.basic

/-!
# Topological lattices

In this file we define mixin classes `has_continuous_inf` and `has_continuous_sup`. We define the
class `topological_lattice` as a topological space and lattice `L` extending `has_continuous_inf`
and `has_continuous_sup`.

## References

* [Gierz et al, A Compendium of Continuous Lattices][GierzEtAl1980]

## Tags

topological, lattice
-/

/--
Let `L` be a topological space and let `L×L` be equipped with the product topology and let
`⊓:L×L → L` be an infimum. Then `L` is said to have *(jointly) continuous infimum* if the map
`⊓:L×L → L` is continuous.
-/
class has_continuous_inf (L : Type*) [topological_space L] [has_inf L] : Prop :=
(continuous_inf : continuous (λ p : L × L, p.1 ⊓ p.2))

/--
Let `L` be a topological space and let `L×L` be equipped with the product topology and let
`⊓:L×L → L` be a supremum. Then `L` is said to have *(jointly) continuous supremum* if the map
`⊓:L×L → L` is continuous.
-/
class has_continuous_sup (L : Type*) [topological_space L] [has_sup L] : Prop :=
(continuous_sup : continuous (λ p : L × L, p.1 ⊔ p.2))

/--
Let `L` be a topological space with a supremum. If the order dual has a continuous infimum then the
supremum is continuous.
-/
@[priority 100] -- see Note [lower instance priority]
instance has_continuous_inf_dual_has_continuous_sup
  (L : Type*) [topological_space L] [has_sup L] [h: has_continuous_inf (order_dual L)] :
  has_continuous_sup  L :=
{ continuous_sup :=
    @has_continuous_inf.continuous_inf (order_dual L) _ _ h }

/--
Let `L` be a lattice equipped with a topology such that `L` has continuous infimum and supremum.
Then `L` is said to be a *topological lattice*.
-/
class topological_lattice (L : Type*) [topological_space L] [lattice L]
  extends has_continuous_inf L, has_continuous_sup L

variables {L : Type*} [topological_space L]
variables {X : Type*} [topological_space X]

@[continuity] lemma continuous_inf [has_inf L] [has_continuous_inf L] :
  continuous (λp:L×L, p.1 ⊓ p.2) :=
has_continuous_inf.continuous_inf

@[continuity] lemma continuous.inf [has_inf L] [has_continuous_inf L]
  {f g : X → L} (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x ⊓ g x) :=
continuous_inf.comp (hf.prod_mk hg : _)

@[continuity] lemma continuous_sup [has_sup L] [has_continuous_sup L] :
  continuous (λp:L×L, p.1 ⊔ p.2) :=
has_continuous_sup.continuous_sup

@[continuity] lemma continuous.sup [has_sup L] [has_continuous_sup L]
  {f g : X → L} (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x ⊔ g x) :=
continuous_sup.comp (hf.prod_mk hg : _)
