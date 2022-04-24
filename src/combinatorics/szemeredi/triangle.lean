/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.clique

/-!
# Triangles in graphs

This file defines triangles in simple graphs.

A triangle is a `3`-clique, namely a set of three vertices that are all adjacent.

## Main declarations

* `simple_graph.triangle_free_far`: Predicate for a graph to have enough triangles that one must
  remove a lot of edges to remove all of them. This is the crux of the Triangle Removal lemma.

## TODO

* Generalise `triangle_free_far` to other graphs, to state and prove the Graph Removal Lemma.
-/

open finset fintype
open_locale classical

lemma is_n_clique.not_clique_free {α : Type*} {G : simple_graph α} {n : ℕ} {s : finset α}
  (hG : G.is_n_clique n s) : ¬ G.clique_free n := λ h, h _ hG

namespace simple_graph
variables {α 𝕜 : Type*} [fintype α] [linear_ordered_field 𝕜] {G H : simple_graph α} {ε δ : 𝕜}
  {n : ℕ} {s : finset α}

/-- A simple graph is `ε`-triangle-free far if one must remove at least `ε * (card α)^2` edges to
make it triangle-free. -/
def triangle_free_far (G : simple_graph α) (ε : 𝕜) : Prop :=
∀ ⦃H⦄, H ≤ G → H.clique_free 3 → ε * (card α^2 : ℕ) ≤ G.edge_finset.card - H.edge_finset.card

lemma triangle_free_far.mono (hε : G.triangle_free_far ε) (h : δ ≤ ε) : G.triangle_free_far δ :=
λ I hIG hI, (mul_le_mul_of_nonneg_right h $ nat.cast_nonneg _).trans $ hε hIG hI

lemma triangle_free_far.clique_finset_nonempty' (hH : H ≤ G) (hG : G.triangle_free_far ε)
  (hcard : (G.edge_finset.card - H.edge_finset.card : 𝕜) < ε * (card α ^ 2 : ℕ)) :
  (H.clique_finset 3).nonempty :=
nonempty_of_ne_empty $ H.clique_finset_eq_empty_iff.not.2 $ λ hH', (hG hH hH').not_lt hcard

variables [nonempty α]

lemma triangle_free_far.nonpos (h₀ : G.triangle_free_far ε) (h₁ : G.clique_free 3) : ε ≤ 0 :=
begin
  have := h₀ le_rfl h₁,
  rw sub_self at this,
  exact nonpos_of_mul_nonpos_right this (nat.cast_pos.2 $ sq_pos_of_pos fintype.card_pos),
end

lemma clique_free.not_triangle_free_far (hG : G.clique_free 3) (hε : 0 < ε) :
  ¬ G.triangle_free_far ε :=
λ h, (h.nonpos hG).not_lt hε

lemma triangle_free_far.not_clique_free (hG : G.triangle_free_far ε) (hε : 0 < ε) :
  ¬ G.clique_free 3 :=
λ h, (hG.nonpos h).not_lt hε

lemma triangle_free_far.clique_finset_nonempty (hG : G.triangle_free_far ε) (hε : 0 < ε) :
  (G.clique_finset 3).nonempty :=
nonempty_of_ne_empty $ G.clique_finset_eq_empty_iff.not.2 $ hG.not_clique_free hε

end simple_graph
