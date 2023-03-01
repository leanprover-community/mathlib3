/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/

import combinatorics.simple_graph.coloring

/-!
# Graph partitions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module provides an interface for dealing with partitions on simple graphs. A partition of
a graph `G`, with vertices `V`, is a set `P` of disjoint nonempty subsets of `V` such that:

* The union of the subsets in `P` is `V`.

* Each element of `P` is an independent set. (Each subset contains no pair of adjacent vertices.)

Graph partitions are graph colorings that do not name their colors.  They are adjoint in the
following sense. Given a graph coloring, there is an associated partition from the set of color
classes, and given a partition, there is an associated graph coloring from using the partition's
subsets as colors.  Going from graph colorings to partitions and back makes a coloring "canonical":
all colors are given a canonical name and unused colors are removed.  Going from partitions to
graph colorings and back is the identity.

## Main definitions

* `simple_graph.partition` is a structure to represent a partition of a simple graph

* `simple_graph.partition.parts_card_le` is whether a given partition is an `n`-partition.
  (a partition with at most `n` parts).

* `simple_graph.partitionable n` is whether a given graph is `n`-partite

* `simple_graph.partition.to_coloring` creates colorings from partitions

* `simple_graph.coloring.to_partition` creates partitions from colorings

## Main statements

* `simple_graph.partitionable_iff_colorable` is that `n`-partitionability and
  `n`-colorability are equivalent.

-/

universes u v

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/--
A `partition` of a simple graph `G` is a structure constituted by
* `parts`: a set of subsets of the vertices `V` of `G`
* `is_partition`: a proof that `parts` is a proper partition of `V`
* `independent`: a proof that each element of `parts` doesn't have a pair of adjacent vertices
-/
structure partition :=
(parts : set (set V))
(is_partition : setoid.is_partition parts)
(independent : ∀ (s ∈ parts), is_antichain G.adj s)

/-- Whether a partition `P` has at most `n` parts. A graph with a partition
satisfying this predicate called `n`-partite. (See `simple_graph.partitionable`.) -/
def partition.parts_card_le {G : simple_graph V} (P : G.partition) (n : ℕ) : Prop :=
∃ (h : P.parts.finite), h.to_finset.card ≤ n

/-- Whether a graph is `n`-partite, which is whether its vertex set
can be partitioned in at most `n` independent sets. -/
def partitionable (n : ℕ) : Prop :=
∃ (P : G.partition), P.parts_card_le n

namespace partition
variables {G} (P : G.partition)

/-- The part in the partition that `v` belongs to -/
def part_of_vertex (v : V) : set V :=
classical.some (P.is_partition.2 v)

lemma part_of_vertex_mem (v : V) : P.part_of_vertex v ∈ P.parts :=
by { obtain ⟨h, -⟩ := (P.is_partition.2 v).some_spec.1, exact h, }

lemma mem_part_of_vertex (v : V) : v ∈ P.part_of_vertex v :=
by { obtain ⟨⟨h1, h2⟩, h3⟩ := (P.is_partition.2 v).some_spec, exact h2.1 }

lemma part_of_vertex_ne_of_adj {v w : V} (h : G.adj v w) :
  P.part_of_vertex v ≠ P.part_of_vertex w :=
begin
  intro hn,
  have hw := P.mem_part_of_vertex w,
  rw ←hn at hw,
  exact P.independent _ (P.part_of_vertex_mem v) (P.mem_part_of_vertex v) hw (G.ne_of_adj h) h,
end

/-- Create a coloring using the parts themselves as the colors.
Each vertex is colored by the part it's contained in. -/
def to_coloring : G.coloring P.parts :=
coloring.mk (λ v, ⟨P.part_of_vertex v, P.part_of_vertex_mem v⟩) $ λ _ _ hvw,
by { rw [ne.def, subtype.mk_eq_mk], exact P.part_of_vertex_ne_of_adj hvw }

/-- Like `simple_graph.partition.to_coloring` but uses `set V` as the coloring type. -/
def to_coloring' : G.coloring (set V) :=
coloring.mk P.part_of_vertex $ λ _ _ hvw, P.part_of_vertex_ne_of_adj hvw

lemma to_colorable [fintype P.parts] : G.colorable (fintype.card P.parts) :=
P.to_coloring.to_colorable

end partition

variables {G}

/-- Creates a partition from a coloring. -/
@[simps]
def coloring.to_partition {α : Type v} (C : G.coloring α) : G.partition :=
{ parts := C.color_classes,
  is_partition := C.color_classes_is_partition,
  independent := begin
    rintros s ⟨c, rfl⟩,
    apply C.color_classes_independent,
  end }

/-- The partition where every vertex is in its own part. -/
@[simps] instance : inhabited (partition G) := ⟨G.self_coloring.to_partition⟩

lemma partitionable_iff_colorable {n : ℕ} :
  G.partitionable n ↔ G.colorable n :=
begin
  split,
  { rintro ⟨P, hf, h⟩,
    haveI : fintype P.parts := hf.fintype,
    rw set.finite.card_to_finset at h,
    apply P.to_colorable.mono h, },
  { rintro ⟨C⟩,
    refine ⟨C.to_partition, C.color_classes_finite, le_trans _ (fintype.card_fin n).le⟩,
    generalize_proofs h,
    haveI : fintype C.color_classes := C.color_classes_finite.fintype,
    rw h.card_to_finset,
    exact C.card_color_classes_le },
end

end simple_graph
