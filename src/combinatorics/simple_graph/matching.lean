/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Arthur Paulino
-/
import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.degree_sum

/-!
# Matchings

The idea of a matching refers to the pairing of adjacent vertices. In this approach we're
representing a matching as a subgraph that contains all vertices of a graph.

## Main definitions

* A *matching* `M` on a simple graph `G` is a subgraph of `G`, such that every vertex of `G` is a
  vertex of `M` and no two edges of `M` share an endpoint.

* A *perfect matching* on a simple graph is a matching in which every vertex forms an edge.

## Todo

* Lemma stating that the existence of a perfect matching on `G` implies that
  the cardinality of `V` is even (assuming it's finite)

* Hall's Marriage Theorem (see combinatorics.hall)

* Tutte's Theorem

* https://github.com/leanprover-community/mathlib/pull/5156#discussion_r532906131
-/

universe u

namespace simple_graph
variables {V : Type u} {G : simple_graph V} (M : subgraph G)

namespace matching

/--
The subgraph `M` of `G` is a matching on `G` if every vertex only forms at most one edge of `M`.
-/
def is_matching : Prop := ∀ (v w w': V), M.adj v w → M.adj v w' → w = w'

/--
`M` is a perfect matching on `G` if it's a matching on `G` and if every vertex forms an edge of `M`.
-/
def is_perfect : Prop := is_matching M ∧ M.support = set.univ

lemma is_perfect_iff :
  is_perfect M ↔ ∀ (v : V), ∃! (w : V), M.adj v w :=
begin
  simp only [is_matching, is_perfect, exists_unique],
  split,
  { intros h v,
    cases h with h hu,
    have hu' := set.mem_univ v,
    rw [← hu, subgraph.mem_support] at hu',
    cases hu' with w hvw,
    use [w, hvw],
    intros w' hvw',
    specialize h v w w' hvw hvw',
    simp only [h], },
  { intro h,
    split,
    { intros v w w' hvw hvw',
      specialize h v,
      cases h with x h,
      cases h with _ hy,
      have hxw := hy w hvw,
      have hxw' := hy w' hvw',
      simp only [hxw, hxw'], },
    { rw set.eq_univ_iff_forall,
      intro v,
      specialize h v,
      cases h with w h,
      cases h with hvw h,
      rw subgraph.mem_support,
      use w,
      exact hvw, }, },
end

end matching

end simple_graph
