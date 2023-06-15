/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.double_counting
import combinatorics.simple_graph.clique
import data.nat.parity
import data.sym.card

/-!
# Triangles in graphs

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A *triangle* in a simple graph is a `3`-clique, namely a set of three vertices that are
pairwise adjacent.

This module defines and proves properties about triangles in simple graphs.

## Main declarations

* `simple_graph.edge_disjoint_triangles`: Predicate for a graph whose triangles are edge-disjoint.
* `simple_graph.locally_linear`: Predicate for each edge in a graph to be in a unique triangle.
* `simple_graph.far_from_triangle_free`: Predicate for a graph to have enough triangles that, to
  remove all of them, one must one must remove a lot of edges. This is the crux of the Triangle
  Removal lemma.

## TODO

* Generalise `far_from_triangle_free` to other graphs, to state and prove the Graph Removal Lemma.
* Find a better name for `far_from_triangle_free`. Added 4/26/2022. Remove this TODO if it gets old.
-/

namespace finset
variables {α : Type*} [decidable_eq α]

lemma insert_comm (a b : α) (s : finset α) : insert a (insert b s) = insert b (insert a s) :=
coe_injective $ by { push_cast, exact set.insert_comm _ _ _ }

end finset

namespace simple_graph
variables {V : Type*}

@[simp] lemma edge_set_top : (⊤ : simple_graph V).edge_set = {e : sym2 V | ¬ e.is_diag} :=
by ext x; induction x using sym2.ind; simp

@[simp] lemma edge_finset_top [fintype V] [decidable_eq V] [fintype (⊤ : simple_graph V).edge_set] :
  (⊤ : simple_graph V).edge_finset = finset.univ.filter (λ e, ¬ e.is_diag) :=
by ext x; induction x using sym2.ind; simp

end simple_graph

open finset fintype (card) nat

namespace simple_graph
variables {α β 𝕜 : Type*} [linear_ordered_field 𝕜] {G H : simple_graph α} {ε δ : 𝕜} {n : ℕ}
  {s : finset α}

section locally_linear

/-- A graph has edge-disjoint triangles if each edge belongs to at most one triangle. -/
def edge_disjoint_triangles (G : simple_graph α) : Prop :=
(G.clique_set 3).pairwise $ λ x y, (x ∩ y : set α).subsingleton

/-- A graph is locally linear if each edge belongs to exactly one triangle. -/
def locally_linear (G : simple_graph α) : Prop :=
G.edge_disjoint_triangles ∧ ∀ ⦃x y⦄, G.adj x y → ∃ s, G.is_n_clique 3 s ∧ x ∈ s ∧ y ∈ s

protected lemma locally_linear.edge_disjoint_triangles :
  G.locally_linear → G.edge_disjoint_triangles :=
and.left

lemma edge_disjoint_triangles.mono (h : G ≤ H) (hH : H.edge_disjoint_triangles) :
  G.edge_disjoint_triangles :=
hH.mono $ clique_set_mono h

@[simp] lemma edge_disjoint_triangles_bot : (⊥ : simple_graph α).edge_disjoint_triangles :=
by simp [edge_disjoint_triangles]

@[simp] lemma locally_linear_bot : (⊥ : simple_graph α).locally_linear := by simp [locally_linear]

lemma edge_disjoint_triangles.map (f : α ↪ β) (hG : G.edge_disjoint_triangles) :
  (G.map f).edge_disjoint_triangles :=
begin
  rw [edge_disjoint_triangles, clique_set_map (bit1_lt_bit1.2 zero_lt_one),
    ((finset.map_injective f).inj_on _).pairwise_image],
  classical,
  rintro s hs t ht hst,
  dsimp [function.on_fun],
  rw [←coe_inter, ←map_inter, coe_map, coe_inter],
  exact (hG hs ht hst).image _,
end

lemma locally_linear.map (f : α ↪ β) (hG : G.locally_linear) : (G.map f).locally_linear :=
begin
  refine ⟨hG.1.map _, _⟩,
  rintro _ _ ⟨a, b, h, rfl, rfl⟩,
  obtain ⟨s, hs, ha, hb⟩ := hG.2 h,
  exact ⟨s.map f, hs.map, mem_map_of_mem _ ha, mem_map_of_mem _ hb⟩,
end

@[simp] lemma locally_linear_comap {G : simple_graph β} {e : α ≃ β} :
  (G.comap e).locally_linear ↔ G.locally_linear :=
begin
  refine ⟨λ h, _, _⟩,
  { rw [←comap_map_eq e.symm.to_embedding G, comap_symm, map_symm],
    exact h.map _ },
  { rw [←equiv.coe_to_embedding, ←map_symm],
    exact locally_linear.map _ }
end

variables [decidable_eq α]

lemma edge_disjoint_triangles_iff_mem_sym2_subsingleton :
  G.edge_disjoint_triangles ↔
    ∀ ⦃e : sym2 α⦄, ¬e.is_diag → {s ∈ G.clique_set 3 | e ∈ (s : finset α).sym2}.subsingleton :=
begin
  have : ∀ a b, a ≠ b → {s ∈ (G.clique_set 3 : set (finset α)) | ⟦(a, b)⟧ ∈ (s : finset α).sym2}
    = {s | G.adj a b ∧ ∃ c, G.adj a c ∧ G.adj b c ∧ s = {a, b, c}},
  { rintro a b hab,
    ext s,
    simp only [mem_sym2_iff, sym2.mem_iff, forall_eq_or_imp, forall_eq, set.sep_and,
      set.mem_inter_iff, set.mem_sep_iff, mem_clique_set_iff, set.mem_set_of_eq,
      and_and_and_comm _ (_ ∈ _), and_self, is_3_clique_iff],
    split,
    { rintro ⟨⟨c, d, e, hcd, hce, hde, rfl⟩, hab⟩,
      simp only [mem_insert, mem_singleton] at hab,
      obtain ⟨rfl | rfl | rfl, rfl | rfl | rfl⟩ := hab;
      simp only [*, adj_comm, true_and, ne.def, eq_self_iff_true, not_true] at *;
      refine ⟨c, _⟩ <|> refine ⟨d, _⟩ <|> refine ⟨e, _⟩; simp [*, pair_comm, insert_comm] },
    { rintro ⟨hab, c, hac, hbc, rfl⟩,
      refine ⟨⟨a, b, c, _⟩, _⟩; simp [*] } },
  split,
  { rw sym2.forall,
    rintro hG a b hab,
    simp only [sym2.is_diag_iff_proj_eq] at hab,
    rw this _ _ (sym2.mk_is_diag_iff.not.2 hab),
    rintro _ ⟨hab, c, hac, hbc, rfl⟩ _ ⟨-, d, had, hbd, rfl⟩,
    refine hG.eq _ _ (set.nontrivial.not_subsingleton ⟨a, _, b, _, hab.ne⟩);
    simp [is_3_clique_triple_iff, *] },
  { simp only [edge_disjoint_triangles, is_3_clique_iff, set.pairwise, mem_clique_set_iff, ne.def,
      forall_exists_index, and_imp, ←@set.not_nontrivial_iff _ (_ ∩ _), not_imp_not, set.nontrivial,
      set.mem_inter_iff, mem_coe],
    rintro hG _ a b c hab hac hbc rfl _ d e f hde hdf hef rfl g hg₁ hg₂ h hh₁ hh₂ hgh,
    refine hG (sym2.mk_is_diag_iff.not.2 hgh)_ _; simp [is_3_clique_triple_iff, *] }
end

alias edge_disjoint_triangles_iff_mem_sym2_subsingleton ↔
  edge_disjoint_triangles.mem_sym2_subsingleton _

variables [fintype α] [decidable_rel G.adj]

instance : decidable G.edge_disjoint_triangles :=
decidable_of_iff ((G.clique_finset 3 : set (finset α)).pairwise $ λ x y, (x ∩ y).card ≤ 1) $
  by simpa only [coe_clique_finset, edge_disjoint_triangles, finset.card_le_one, ←coe_inter]

instance : decidable G.locally_linear := and.decidable

lemma edge_disjoint_triangles.card_edge_finset_le (hG : G.edge_disjoint_triangles) :
  3 * (G.clique_finset 3).card ≤ G.edge_finset.card :=
begin
  rw [mul_comm, ←mul_one G.edge_finset.card],
  refine card_mul_le_card_mul (λ s e, e ∈ s.sym2) _ (λ e he, _),
  { simp only [is_3_clique_iff, mem_clique_finset_iff, mem_sym2_iff,
      forall_exists_index, and_imp],
    rintro _ a b c hab hac hbc rfl,
    have : finset.card ({⟦(a, b)⟧, ⟦(a, c)⟧, ⟦(b, c)⟧} : finset $ sym2 α) = 3,
    { refine card_eq_three.2 ⟨_, _, _, _, _, _, rfl⟩; simp [hab.ne, hac.ne, hbc.ne] },
    rw ←this,
    refine card_mono _,
    simp [insert_subset, *] },
  { simpa only [card_le_one, mem_bipartite_below, and_imp, set.subsingleton, set.mem_sep_iff,
      mem_clique_finset_iff, mem_clique_set_iff]
      using hG.mem_sym2_subsingleton (G.not_is_diag_of_mem_edge_set $ mem_edge_finset.1 he) }
end

lemma locally_linear.card_edge_finset (hG : G.locally_linear) :
  G.edge_finset.card = 3 * (G.clique_finset 3).card :=
begin
  refine hG.edge_disjoint_triangles.card_edge_finset_le.antisymm' _,
  rw [←mul_comm, ←mul_one (finset.card _)],
  refine card_mul_le_card_mul (λ e s, e ∈ s.sym2) _ _,
  { simpa [sym2.forall, nat.succ_le_iff, card_pos, finset.nonempty] using hG.2 },
  simp only [mem_clique_finset_iff, is_3_clique_iff, forall_exists_index, and_imp],
  rintro _ a b c hab hac hbc rfl,
  refine (card_mono _).trans _,
  { exact {⟦(a, b)⟧, ⟦(a, c)⟧, ⟦(b, c)⟧} },
  { simp only [subset_iff, sym2.forall, mem_sym2_iff, le_eq_subset, mem_bipartite_below, mem_insert,
      mem_edge_finset, mem_singleton, and_imp, mem_edge_set, sym2.mem_iff, forall_eq_or_imp,
      forall_eq, quotient.eq, sym2.rel_iff],
    rintro d e hde (rfl | rfl | rfl) (rfl | rfl | rfl); simp [*] at * },
  { exact (card_insert_le _ _).trans (succ_le_succ $ (card_insert_le _ _).trans_eq $
      by rw card_singleton) }
end

end locally_linear

variables (G ε) [fintype α] [decidable_eq α] [decidable_rel G.adj] [decidable_rel H.adj]

/-- A simple graph is *`ε`-triangle-free far* if one must remove at least `ε * (card α)^2` edges to
make it triangle-free. -/
def far_from_triangle_free : Prop := G.delete_far (λ H, H.clique_free 3) $ ε * (card α^2 : ℕ)

variables {G ε}

lemma far_from_triangle_free_iff :
  G.far_from_triangle_free ε ↔
    ∀ ⦃H : simple_graph _⦄ [decidable_rel H.adj], by exactI
      H ≤ G → H.clique_free 3 → ε * (card α^2 : ℕ) ≤ G.edge_finset.card - H.edge_finset.card :=
delete_far_iff

alias far_from_triangle_free_iff ↔ far_from_triangle_free.le_card_sub_card _

lemma far_from_triangle_free.mono (hε : G.far_from_triangle_free ε) (h : δ ≤ ε) :
  G.far_from_triangle_free δ :=
hε.mono $ mul_le_mul_of_nonneg_right h $ cast_nonneg _

@[simp] lemma far_from_triangle_free_of_nonpos (hε : ε ≤ 0) : G.far_from_triangle_free ε :=
λ H _ _, (mul_nonpos_of_nonpos_of_nonneg hε $ nat.cast_nonneg _).trans $ nat.cast_nonneg _

lemma far_from_triangle_free.clique_finset_nonempty' (hH : H ≤ G) (hG : G.far_from_triangle_free ε)
  (hcard : (G.edge_finset.card - H.edge_finset.card : 𝕜) < ε * (card α ^ 2 : ℕ)) :
  (H.clique_finset 3).nonempty :=
nonempty_of_ne_empty $ H.clique_finset_eq_empty_iff.not.2 $ λ hH',
  (hG.le_card_sub_card hH hH').not_lt hcard

private lemma far_from_triangle_free_of_disjoint_triangles_aux {tris : finset (finset α)}
  (htris : tris ⊆ G.clique_finset 3)
  (pd : (tris : set (finset α)).pairwise (λ x y, (x ∩ y : set α).subsingleton)) (hHG : H ≤ G)
  (hH : H.clique_free 3) : tris.card ≤ G.edge_finset.card - H.edge_finset.card :=
begin
  rw [←card_sdiff (edge_finset_mono hHG), ←card_attach],
  by_contra' hG,
  have : ∀ ⦃t⦄, t ∈ tris → ∃ x y, x ∈ t ∧ y ∈ t ∧ x ≠ y ∧ ⟦(x, y)⟧ ∈ G.edge_finset \ H.edge_finset,
  { intros t ht,
    by_contra' h,
    refine hH t _,
    simp only [not_and, mem_sdiff, not_not, mem_edge_finset, mem_edge_set] at h,
    obtain ⟨x, y, z, xy, xz, yz, rfl⟩ := is_3_clique_iff.1 (G.mem_clique_finset_iff.1 $ htris ht),
    rw is_3_clique_triple_iff,
    refine ⟨h _ _ _ _ xy.ne xy, h _ _ _ _ xz.ne xz, h _ _ _ _ yz.ne yz⟩; simp },
  choose fx fy hfx hfy hfne fmem using this,
  let f : {x // x ∈ tris} → sym2 α := λ t, ⟦(fx t.2, fy t.2)⟧,
  have hf : ∀ x, x ∈ tris.attach → f x ∈ G.edge_finset \ H.edge_finset := λ x hx, fmem _,
  obtain ⟨⟨t₁, ht₁⟩, -, ⟨t₂, ht₂⟩, -, tne, t : ⟦_⟧ = ⟦_⟧⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to hG hf,
  dsimp at t,
  have i := pd ht₁ ht₂ (subtype.val_injective.ne tne),
  rw sym2.eq_iff at t,
  cases t,
  { exact hfne _ (i ⟨hfx ht₁, t.1.symm ▸ hfx ht₂⟩ ⟨hfy ht₁, t.2.symm ▸ hfy ht₂⟩) },
  { exact hfne _ (i ⟨hfx ht₁, t.1.symm ▸ hfy ht₂⟩ ⟨hfy ht₁, t.2.symm ▸ hfx ht₂⟩) }
end

/-- If there are `ε * (card α)^2` disjoint triangles, then the graph is `ε`-far from being
triangle-free. -/
lemma far_from_triangle_free_of_disjoint_triangles (tris : finset (finset α))
  (htris : tris ⊆ G.clique_finset 3)
  (pd : (tris : set (finset α)).pairwise (λ x y, (x ∩ y : set α).subsingleton))
  (tris_big : ε * (card α ^ 2 : ℕ) ≤ tris.card) :
  G.far_from_triangle_free ε :=
begin
  rw far_from_triangle_free_iff,
  introsI H _ hG hH,
  rw ←nat.cast_sub (card_le_of_subset $ edge_finset_mono hG),
  exact tris_big.trans
    (nat.cast_le.2 $ far_from_triangle_free_of_disjoint_triangles_aux htris pd hG hH),
end

protected lemma edge_disjoint_triangles.far_from_triangle_free (hG : G.edge_disjoint_triangles)
  (tris_big : ε * (card α ^ 2 : ℕ) ≤ (G.clique_finset 3).card) : G.far_from_triangle_free ε :=
far_from_triangle_free_of_disjoint_triangles _ subset.rfl (by simpa using hG) tris_big

variables [nonempty α]

lemma far_from_triangle_free.lt_half (hG : G.far_from_triangle_free ε) : ε < 2⁻¹ :=
begin
  by_contra' hε,
  have := hG.le_card_sub_card bot_le (clique_free_bot $ by norm_num),
  simp only [set.to_finset_card (edge_set ⊥), fintype.card_of_finset, edge_set_bot, cast_zero,
    finset.card_empty, tsub_zero] at this,
  have hε₀ : 0 < ε := hε.trans_lt' (by norm_num),
  rw inv_pos_le_iff_one_le_mul (zero_lt_two' 𝕜) at hε,
  refine (this.trans $ le_mul_of_one_le_left (by positivity) hε).not_lt _,
  rw [mul_assoc, mul_lt_mul_left hε₀],
  norm_cast,
  refine (mul_le_mul_left' (card_mono $ edge_finset_mono le_top) _).trans_lt _,
  rw [edge_finset_top, filter_not, card_sdiff (subset_univ _), card_univ, sym2.card],
  simp_rw [sym2.is_diag_iff_mem_range_diag, univ_filter_mem_range, mul_tsub,
    nat.mul_div_cancel' (card α).even_mul_succ_self.two_dvd],
  rw [card_image_of_injective _ sym2.diag_injective, card_univ, mul_add_one, two_mul, sq,
    add_tsub_add_eq_tsub_right],
  exact tsub_lt_self (mul_pos fintype.card_pos fintype.card_pos) fintype.card_pos,
end

lemma far_from_triangle_free.lt_one (hG : G.far_from_triangle_free ε) : ε < 1 :=
hG.lt_half.trans $ by norm_num

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
