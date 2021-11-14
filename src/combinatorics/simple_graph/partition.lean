/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/

import combinatorics.simple_graph.coloring

universes u v

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

structure partition :=
(parts : set (set V))
(is_partition : setoid.is_partition parts)
(independent : ∀ (s ∈ parts), is_antichain G.adj s)

namespace partition
variables {G} (P : G.partition)

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

def to_coloring : G.coloring (set V) :=
coloring.mk P.part_of_vertex
begin
  intros _ _ hvw,
  exact P.part_of_vertex_ne_of_adj hvw,
end

def to_coloring' : G.coloring P.parts :=
coloring.mk (λ v, ⟨P.part_of_vertex v, P.part_of_vertex_mem v⟩)
begin
  intros _ _ hvw,
  rw [ne.def, subtype.mk_eq_mk],
  exact P.part_of_vertex_ne_of_adj hvw,
end

lemma to_colorable [fintype P.parts] : G.colorable (fintype.card P.parts) :=
coloring.to_colorable P.to_coloring'

def from_coloring {α : Type v} (C : G.coloring α) : G.partition :=
begin
  let parts : set (set V) := C.color_classes,
  have is_partition : setoid.is_partition parts,
    { by apply coloring.color_classes_is_partition, },
  have independent : ∀ (s ∈ parts), is_antichain G.adj s,
    { by apply coloring.color_classes_is_independent, },
  exact partition.mk parts is_partition independent,
end

end partition

end simple_graph
