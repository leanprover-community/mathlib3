/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/

import combinatorics.simple_graph.coloring

/-!
# Graph partitions

This module provides an interface for dealing with partitions on simple graphs. A partition of
a graph `G`, with vertices `V`, is a set `P` of disjoint nonempty subsets of `V` such that:

* The union of the subsets in `P` is `V`.

* * Each element of `P` is an independent set. (Each subset contains no pair of adjacent vertices.)

Graph partitions are graph colorings that do not name their colors.  They are adjoint in the
following sense. Given a graph coloring, there is an associated partition from the set of color
classes, and given a partition, there is an associated graph coloring from using the partition's
subsets as colors.  Going from graph colorings to partitions and back makes a coloring "canonical":
all colors are given a canonical name and unused colors are removed.  Going from partitions to
graph colorings and back is the identity.

## Main definitions

* `partition` is a structure to represent a partition of a simple graph

* `partition.to_coloring` and `partition.to_coloring'` are functions that create colorings from
  partitions

* `coloring.to_partition` is a function that creates a partition from a coloring

## Todo

* Define k-partite graphs

* Prove that k-partite graphs are k-colorable and vice-versa

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

/-- Whether a graph can be partitioned in at most `n` parts. -/
def partitionable (n : ℕ) : Prop :=
∃ (P : G.partition), nonempty (P.parts ↪ fin n)

namespace partition
variables {G} (P : G.partition)

/-- Whether a partition `P` has at most `n` parts. -/
def parts_card_le (n : ℕ) : Prop := ∃ (h : P.parts.finite), h.to_finset.card ≤ n

/-- Get the part `v` belongs to in the partition. -/
def part_of_vertex (v : V) : set V :=
classical.some (P.is_partition.2 v)

lemma part_of_vertex_mem (v : V) : P.part_of_vertex v ∈ P.parts :=
begin
  obtain ⟨h, -⟩ := (P.is_partition.2 v).some_spec.1,
  exact h,
end

lemma mem_part_of_vertex (v : V) : v ∈ P.part_of_vertex v :=
begin
  obtain ⟨⟨h1, h2⟩, h3⟩ := (P.is_partition.2 v).some_spec,
  exact h2.1,
end

lemma part_of_vertex_ne_of_adj {v w : V} (h : G.adj v w) :
  P.part_of_vertex v ≠ P.part_of_vertex w :=
begin
  have aa := P.is_partition.2,
  intro hn,
  have hw := P.mem_part_of_vertex w,
  rw ←hn at hw,
  have h1 := P.independent _ (P.part_of_vertex_mem v) _ (P.mem_part_of_vertex v),
  exact h1 w hw (G.ne_of_adj h) h,
end

/-- Creates a coloring using colors of type `set V`. -/
def to_coloring : G.coloring (set V) :=
coloring.mk P.part_of_vertex
begin
  intros _ _ hvw,
  exact P.part_of_vertex_ne_of_adj hvw,
end

/-- Creates a coloring using colors of type `P.parts`. -/
def to_coloring' : G.coloring P.parts :=
coloring.mk (λ v, ⟨P.part_of_vertex v, P.part_of_vertex_mem v⟩)
begin
  intros _ _ hvw,
  rw [ne.def, subtype.mk_eq_mk],
  exact P.part_of_vertex_ne_of_adj hvw,
end

lemma to_colorable [fintype P.parts] : G.colorable (fintype.card P.parts) :=
coloring.to_colorable P.to_coloring'

def from_coloring_to_embedding {α : Type v} (C : G.coloring α) : P.parts ↪ α := sorry

end partition

namespace coloring

/-- Creates a partition from a coloring. -/
def coloring.to_partition {α : Type v} (C : G.coloring α) : G.partition :=
begin
  let parts : set (set V) := C.color_classes,
  have is_partition : setoid.is_partition parts,
    { by apply coloring.color_classes_is_partition, },
  have independent : ∀ (s ∈ parts), is_antichain G.adj s,
    { by apply coloring.color_classes_is_independent, },
  exact partition.mk parts is_partition independent,
end

instance : inhabited (partition G) := ⟨coloring.to_partition G G.self_coloring⟩

lemma partitionable_iff_colorable {n : ℕ} :
  G.partitionable n ↔ G.colorable n :=
begin
  split,
  { intro h,
    cases h with P h,
    obtain ⟨f⟩ := h,
    have C := partition.to_coloring' P,
    use G.recolor_of_embedding f C, },
  { rintro ⟨C⟩,
    have P := coloring.to_partition G C,
    use [P, P.from_coloring_to_embedding C], },
end

end coloring

end simple_graph
