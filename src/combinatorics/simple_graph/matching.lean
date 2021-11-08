/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Arthur Paulino
-/
import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.degree_sum

/-!
# Matchings

## Main definitions

TODO:
  - Lemma stating that the existence of a perfect matching on `G` implies that
    the cardinality of `V` is even (assuming it's finite)
  - Hall's Marriage Theorem (see combinatorics.hall)
  - Tutte's Theorem
  - consider coercions instead of type definition for `matching`:
    https://github.com/leanprover-community/mathlib/pull/5156#discussion_r532935457
  - consider expressing `matching_verts` as union:
    https://github.com/leanprover-community/mathlib/pull/5156#discussion_r532906131
-/
open finset
universe u

namespace simple_graph
variables {V : Type u} {G : simple_graph V} (M : subgraph G)

/--
A *matching* `M` on a simple graph `G` is a subgraph of `G`, such that every vertex of `G` is a
vertex of `M` and no two edges of `M` share an endpoint.
-/
def is_matching : Prop := ∀ (v w w': V), M.adj v w → M.adj v w' → w = w'

/--
A *perfect matching* on a simple graph is a matching in which every vertex forms an edge.
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

open_locale big_operators

lemma is_perfect_degree_sum (hp: is_perfect M) [fintype V] [decidable_rel M.adj] :
  ∑ v, M.degree v = fintype.card V :=
begin
  simp only [subgraph.degree, subgraph.neighbor_set],
  rw is_perfect_iff at hp,
  sorry,
end

lemma is_perfect_then_even_card_vertices (hp: is_perfect M)
  [fintype V] [fintype M.edge_set] [decidable_rel M.adj]:
  even (fintype.card V) :=
begin
  rw even,
  use fintype.card M.edge_set,
  rw ← is_perfect_degree_sum M hp,
  simp [← sum_degrees_eq_twice_card_edges], -- breakpoint
end

end simple_graph
