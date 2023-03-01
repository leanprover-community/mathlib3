/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.clique

/-!
# Triangles in graphs

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A *triangle* in a simple graph is a `3`-clique, namely a set of three vertices that are
pairwise adjacent.

This module defines and proves properties about triangles in simple graphs.

## Main declarations

* `simple_graph.far_from_triangle_free`: Predicate for a graph to have enough triangles that, to
  remove all of them, one must one must remove a lot of edges. This is the crux of the Triangle
  Removal lemma.

## TODO

* Generalise `far_from_triangle_free` to other graphs, to state and prove the Graph Removal Lemma.
* Find a better name for `far_from_triangle_free`. Added 4/26/2022. Remove this TODO if it gets old.
-/

open finset fintype nat
open_locale classical

namespace simple_graph
variables {α 𝕜 : Type*} [fintype α] [linear_ordered_field 𝕜] {G H : simple_graph α} {ε δ : 𝕜}
  {n : ℕ} {s : finset α}

/-- A simple graph is *`ε`-triangle-free far* if one must remove at least `ε * (card α)^2` edges to
make it triangle-free. -/
def far_from_triangle_free (G : simple_graph α) (ε : 𝕜) : Prop :=
G.delete_far (λ H, H.clique_free 3) $ ε * (card α^2 : ℕ)

lemma far_from_triangle_free_iff :
  G.far_from_triangle_free ε ↔
    ∀ ⦃H⦄, H ≤ G → H.clique_free 3 → ε * (card α^2 : ℕ) ≤ G.edge_finset.card - H.edge_finset.card :=
delete_far_iff

alias far_from_triangle_free_iff ↔ far_from_triangle_free.le_card_sub_card _

lemma far_from_triangle_free.mono (hε : G.far_from_triangle_free ε) (h : δ ≤ ε) :
  G.far_from_triangle_free δ :=
hε.mono $ mul_le_mul_of_nonneg_right h $ cast_nonneg _

lemma far_from_triangle_free.clique_finset_nonempty' (hH : H ≤ G) (hG : G.far_from_triangle_free ε)
  (hcard : (G.edge_finset.card - H.edge_finset.card : 𝕜) < ε * (card α ^ 2 : ℕ)) :
  (H.clique_finset 3).nonempty :=
nonempty_of_ne_empty $ H.clique_finset_eq_empty_iff.not.2 $ λ hH',
  (hG.le_card_sub_card hH hH').not_lt hcard

variables [nonempty α]

lemma far_from_triangle_free.nonpos (h₀ : G.far_from_triangle_free ε) (h₁ : G.clique_free 3) :
  ε ≤ 0 :=
begin
  have := h₀ (empty_subset _),
  rw [coe_empty, finset.card_empty, cast_zero, delete_edges_empty_eq] at this,
  exact nonpos_of_mul_nonpos_left (this h₁) (cast_pos.2 $ sq_pos_of_pos fintype.card_pos),
end

lemma clique_free.not_far_from_triangle_free (hG : G.clique_free 3) (hε : 0 < ε) :
  ¬ G.far_from_triangle_free ε :=
λ h, (h.nonpos hG).not_lt hε

lemma far_from_triangle_free.not_clique_free (hG : G.far_from_triangle_free ε) (hε : 0 < ε) :
  ¬ G.clique_free 3 :=
λ h, (hG.nonpos h).not_lt hε

lemma far_from_triangle_free.clique_finset_nonempty (hG : G.far_from_triangle_free ε) (hε : 0 < ε) :
  (G.clique_finset 3).nonempty :=
nonempty_of_ne_empty $ G.clique_finset_eq_empty_iff.not.2 $ hG.not_clique_free hε

end simple_graph
