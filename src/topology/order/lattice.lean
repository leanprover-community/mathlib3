/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import topology.order.basic
import topology.constructions

/-!
# Topological lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define mixin classes `has_continuous_inf` and `has_continuous_sup`. We define the
class `topological_lattice` as a topological space and lattice `L` extending `has_continuous_inf`
and `has_continuous_sup`.

## References

* [Gierz et al, A Compendium of Continuous Lattices][GierzEtAl1980]

## Tags

topological, lattice
-/

open filter
open_locale topology

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

@[priority 100] -- see Note [lower instance priority]
instance order_dual.has_continuous_sup
  (L : Type*) [topological_space L] [has_inf L] [has_continuous_inf L] : has_continuous_sup Lᵒᵈ :=
{ continuous_sup := @has_continuous_inf.continuous_inf L _ _ _ }

@[priority 100] -- see Note [lower instance priority]
instance order_dual.has_continuous_inf
  (L : Type*) [topological_space L] [has_sup L] [has_continuous_sup L] : has_continuous_inf Lᵒᵈ :=
{ continuous_inf := @has_continuous_sup.continuous_sup L _ _ _ }

/--
Let `L` be a lattice equipped with a topology such that `L` has continuous infimum and supremum.
Then `L` is said to be a *topological lattice*.
-/
class topological_lattice (L : Type*) [topological_space L] [lattice L]
  extends has_continuous_inf L, has_continuous_sup L

@[priority 100] -- see Note [lower instance priority]
instance order_dual.topological_lattice
  (L : Type*) [topological_space L] [lattice L] [topological_lattice L] :
  topological_lattice Lᵒᵈ := {}

@[priority 100] -- see Note [lower instance priority]
instance linear_order.topological_lattice {L : Type*} [topological_space L] [linear_order L]
  [order_closed_topology L] : topological_lattice L :=
{ continuous_inf := continuous_min, continuous_sup := continuous_max }

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

lemma filter.tendsto.sup_right_nhds' {ι β} [topological_space β] [has_sup β] [has_continuous_sup β]
  {l : filter ι} {f g : ι → β} {x y : β}
  (hf : tendsto f l (𝓝 x)) (hg : tendsto g l (𝓝 y)) :
  tendsto (f ⊔ g) l (𝓝 (x ⊔ y)) :=
(continuous_sup.tendsto _).comp (tendsto.prod_mk_nhds hf hg)

lemma filter.tendsto.sup_right_nhds {ι β} [topological_space β] [has_sup β] [has_continuous_sup β]
  {l : filter ι} {f g : ι → β} {x y : β}
  (hf : tendsto f l (𝓝 x)) (hg : tendsto g l (𝓝 y)) :
  tendsto (λ i, f i ⊔ g i) l (𝓝 (x ⊔ y)) :=
hf.sup_right_nhds' hg

lemma filter.tendsto.inf_right_nhds' {ι β} [topological_space β] [has_inf β] [has_continuous_inf β]
  {l : filter ι} {f g : ι → β} {x y : β}
  (hf : tendsto f l (𝓝 x)) (hg : tendsto g l (𝓝 y)) :
  tendsto (f ⊓ g) l (𝓝 (x ⊓ y)) :=
(continuous_inf.tendsto _).comp (tendsto.prod_mk_nhds hf hg)

lemma filter.tendsto.inf_right_nhds {ι β} [topological_space β] [has_inf β] [has_continuous_inf β]
  {l : filter ι} {f g : ι → β} {x y : β}
  (hf : tendsto f l (𝓝 x)) (hg : tendsto g l (𝓝 y)) :
  tendsto (λ i, f i ⊓ g i) l (𝓝 (x ⊓ y)) :=
hf.inf_right_nhds' hg
