/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .regularity_lemma
import .triangle

/-!
# Triangle counting lemma
-/

open finset fintype
open_locale big_operators

variables {α : Type*} (G : simple_graph α)

namespace simple_graph

noncomputable def triangle_removal_bound (ε : ℝ) : ℝ :=
(1 - ε/2) * (ε/4)^3 * (ε/(4 * szemeredi_bound ε 0))^3

variables [fintype α] [decidable_eq α]

open_locale classical

@[simps]
def reduced_graph (ε : ℝ) (P : finpartition (univ : finset α)) : simple_graph α :=
{ adj := λ x y, G.adj x y ∧
    ∃ U V ∈ P.parts, x ∈ U ∧ y ∈ V ∧ U ≠ V ∧ G.is_uniform (ε/4) U V ∧ ε/2 ≤ G.edge_density U V,
  symm := λ x y,
  begin
    rintro ⟨xy, U, V, UP, VP, xU, yV, UV, GUV, εUV⟩,
    refine ⟨G.symm xy, V, U, VP, UP, yV, xU, UV.symm, GUV.symm, _⟩,
    rwa edge_density_comm,
  end,
  loopless := λ x ⟨h, _⟩, G.loopless x h }

variables {G}

lemma reduced_graph_le {ε : ℝ} {P : finpartition (univ : finset α)} :
  reduced_graph G ε P ≤ G :=
λ x y ⟨h, _⟩, h

@[mono] lemma edge_set_subset_of_le {G G' : simple_graph α} (h : G ≤ G') :
  G.edge_set ⊆ G'.edge_set :=
begin
  refine sym2.ind _,
  intros x y h',
  apply h h',
end

@[mono] lemma edge_finset_subset_of_le {G G' : simple_graph α} (h : G ≤ G') :
  G.edge_finset ⊆ G'.edge_finset :=
set.to_finset_mono.2 (edge_set_subset_of_le h)

lemma double_edge_finset_card_eq :
  2 * G.edge_finset.card = (univ.filter (λ (xy : α × α), G.adj xy.1 xy.2)).card :=
begin
  rw [finset.card_eq_sum_ones (finset.filter _ _), sum_partition (sym2.rel.setoid α),
    @sum_const_nat _ _ 2, mul_comm],
  { congr' 2,
    ext x,
    apply sym2.induction_on x,
    simp only [mem_image, true_and, exists_prop, mem_filter, mem_univ, mem_edge_finset,
      mem_edge_set, prod.exists, sym2.eq_iff],
    intros x y,
    refine ⟨λ h, ⟨x, y, h, or.inl ⟨rfl, rfl⟩⟩, _⟩,
    rintro ⟨_, _, h, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩,
    { apply h },
    { apply G.symm h } },
  refine sym2.ind _,
  simp only [mem_image, true_and, and_imp, filter_congr_decidable, exists_prop, mem_filter, mul_one,
    algebra.id.smul_eq_mul, forall_exists_index, mem_univ, sum_const, prod.exists,
    filter_filter],
  rintro x y x' y' h q,
  suffices : filter (λ (a : α × α), G.adj a.fst a.snd ∧ ⟦a⟧ = ⟦(x, y)⟧) univ = {(x',y'), (y',x')},
  { rw [this, card_insert_of_not_mem, card_singleton],
    simp only [mem_singleton, prod.mk.inj_iff, not_and_distrib],
    left,
    apply G.ne_of_adj h },
  ext ⟨i, j⟩,
  simp only [true_and, mem_filter, mem_insert, mem_univ, mem_singleton],
  rw ←q,
  split,
  { rw sym2.eq_iff,
    rintro ⟨_, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩;
    simp },
  rw prod.mk.inj_iff,
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩),
  { exact ⟨h, rfl⟩ },
  { exact ⟨G.symm h, sym2.eq_swap⟩, }
end

lemma reduced_double_edges {ε : ℝ} {P : finpartition (univ : finset α)} :
  univ.filter (λ (xy : α × α), G.adj xy.1 xy.2) \
    univ.filter (λ (xy : α × α), (reduced_graph G ε P).adj xy.1 xy.2) ⊆
      (P.non_uniform_pairs G (ε/4)).bUnion (λ UV, UV.1.product UV.2) ∪
        P.parts.bUnion (λ U, U.off_diag) ∪
          (P.parts.off_diag.filter (λ (UV : _ × _), G.edge_density UV.1 UV.2 < ε/2)).bUnion
            (λ UV, (UV.1.product UV.2)) :=
begin
  rintro ⟨x, y⟩,
  simp only [mem_sdiff, mem_filter, mem_univ, true_and, reduced_graph_adj, not_and, not_exists,
    not_le, mem_bUnion, mem_union, exists_prop, mem_product, prod.exists, mem_off_diag, and_imp,
    or.assoc, and.assoc, P.mem_non_uniform_pairs],
  intros h h',
  replace h' := h' h,
  obtain ⟨U, hU, hx⟩ := P.exists_mem (mem_univ x),
  obtain ⟨V, hV, hy⟩ := P.exists_mem (mem_univ y),
  rcases eq_or_ne U V with rfl | hUV,
  { exact or.inr (or.inl ⟨U, hU, hx, hy, G.ne_of_adj h⟩) },
  by_cases G.is_uniform (ε/4) U V,
  { exact or.inr (or.inr ⟨U, V, hU, hV, hUV, h' _ _ hU hV hx hy hUV h, hx, hy⟩ ) },
  { exact or.inl ⟨U, V, hU, hV, hUV, h, hx, hy⟩ },
end

-- lemma reduced_edges {ε : ℝ} {P : finpartition (univ : finset α)} :
--   G.edge_finset \ (reduced_graph G ε P).edge_finset ⊆
--     (P.non_uniform_pairs G (ε/4)).bUnion (λ UV, (UV.1.product UV.2).image quotient.mk) ∪
--       P.parts.bUnion (λ U, U.off_diag.image quotient.mk) ∪
--         (P.parts.off_diag.filter (λ (UV : _ × _), G.edge_density UV.1 UV.2 < ε/2)).bUnion
--           (λ UV, (UV.1.product UV.2).image quotient.mk) :=
-- begin
--   refine sym2.ind _,
--   simp only [mem_sdiff, mem_edge_finset, mem_edge_set, reduced_graph_adj, not_and, mem_bUnion,
--     mem_union, exists_prop, mem_filter, and_imp, mem_image, prod.exists, mem_product, mem_off_diag,
--     P.mem_non_uniform_pairs, not_exists, not_le, and_assoc],
--   intros x y h h',
--   replace h' := h' h,
--   obtain ⟨U, hU, hx⟩ := P.exists_mem (mem_univ x),
--   obtain ⟨V, hV, hy⟩ := P.exists_mem (mem_univ y),
--   rcases eq_or_ne U V with rfl | hUV,
--   { exact or.inl (or.inr ⟨U, hU, x, y, hx, hy, G.ne_of_adj h, rfl⟩) },
--   by_cases G.is_uniform (ε/4) U V,
--   { exact or.inr ⟨U, V, hU, hV, hUV, h' _ _ hU hV hx hy hUV h, x, y, hx, hy, rfl⟩ },
--   { exact or.inl (or.inl ⟨U, V, hU, hV, hUV, h, x, y, hx, hy, rfl⟩) },
-- end

-- We will break up the sum more later
lemma non_uniform_killed_card {ε : ℝ} {P : finpartition (univ : finset α)} :
  (((P.non_uniform_pairs G (ε/4)).bUnion (λ UV, UV.1.product UV.2)).card : ℝ) ≤
    (∑ i in P.non_uniform_pairs G ε, i.1.card * i.2.card : ℝ) :=
begin
  norm_cast,
end

lemma reduced_edges_card_aux₁ {ε : ℝ} {P : finpartition (univ : finset α)} :
  2 * (G.edge_finset.card - (reduced_graph G ε P).edge_finset.card : ℝ) ≤ sorry :=
begin
  have i : univ.filter (λ (xy : α × α), (G.reduced_graph ε P).adj xy.1 xy.2) ⊆
    univ.filter (λ (xy : α × α), G.adj xy.1 xy.2),
  { apply monotone_filter_right,
    rintro ⟨x,y⟩,
    apply reduced_graph_le },
  rw mul_sub,
  norm_cast,
  rw double_edge_finset_card_eq,
  rw double_edge_finset_card_eq,
  rw [←nat.cast_sub (card_le_of_subset i), ←card_sdiff i],

  -- let i : (reduced_graph G ε P).edge_finset ≤ _ := edge_finset_subset_of_le reduced_graph_le,
end

-- lemma triangle_removal (ε : ℝ)
--   (hG : (G.edge_finset.card : ℝ) ≤ (card α)^3 * triangle_removal_bound ε) :
--   ∃ (G' ≤ G),
--     (G.edge_finset.card - G'.edge_finset.card : ℝ) ≤ (card α)^2 * ε
--       ∧ G'.no_triangles :=
-- sorry

-- theorem szemeredi_regularity' :
--   ∀ {ε : ℝ} (l : ℕ), 0 < ε → ∃ (L : ℕ),
--     ∀ (α : Type*) [fintype α] (G : simple_graph α), by exactI
--       l ≤ card α →
--         ∃ (P : finpartition univ),
--           P.is_equipartition ∧ l ≤ P.parts.card ∧ P.parts.card ≤ L ∧ P.is_uniform G ε :=

lemma thing (i j : ℕ) :
  j ≤ i → j * (j - 1) * (i / j + 1) ^ 2 ≤ 4 * i ^ 2 :=
begin
  intro h,
  have : 4 * i^2 = (2 * i)^2,
  { ring },
  rw this,
  apply (nat.mul_le_mul_right _ (nat.mul_le_mul_left _ (nat.sub_le _ _))).trans _,
  rw ←sq,
  rw ←mul_pow,
  apply nat.pow_le_pow_of_le_left,
  rw [mul_add, mul_one, two_mul],
  apply add_le_add (nat.mul_div_le i j) h,
end

lemma thing2 (i j : ℕ) :
  j * (j - 1) * (i / j + 1) ^ 2 ≤ (i + j) ^ 2 :=
begin
  apply (nat.mul_le_mul_right _ (nat.mul_le_mul_left _ (nat.sub_le _ _))).trans _,
  rw ←sq,
  rw ←mul_pow,
  apply nat.pow_le_pow_of_le_left,
  rw [mul_add, mul_one],
  apply add_le_add_right (nat.mul_div_le i j),
end

lemma sum_irreg_pairs_le_of_uniform {ε : ℝ} (hε : 0 ≤ ε)
  (P : finpartition univ) (hP : P.is_equipartition) (hG : P.is_uniform G ε) :
  (∑ i in P.non_uniform_pairs G ε, i.1.card * i.2.card : ℝ) ≤ ε * (card α + P.parts.card)^2 :=
begin
  refine (sum_le_of_forall_le (P.non_uniform_pairs G ε) (λ i, (i.1.card * i.2.card : ℝ))
    ((card α / P.parts.card + 1)^2 : ℕ) _).trans _,
  { simp only [prod.forall, finpartition.mem_non_uniform_pairs, and_imp],
    rintro U V hU hV hUV -,
    rw [sq, ←nat.cast_mul, nat.cast_le],
    exact nat.mul_le_mul (hP.card_part_le_average_add_one hU) (hP.card_part_le_average_add_one hV) },
  rw nsmul_eq_mul,
  apply (mul_le_mul_of_nonneg_right hG (nat.cast_nonneg _)).trans,
  rw [mul_right_comm _ ε, mul_comm ε],
  apply mul_le_mul_of_nonneg_right _ hε,
  norm_cast,
  apply thing2 _ _,
end

lemma triangle_removal_2 (ε : ℝ) (hε : 0 < ε) :
  ∃ (δ : ℝ), 0 < δ ∧ ∀ (α : Type*) [fintype α] (G : simple_graph α), by exactI
    G.triangle_free_far ε →
      δ * (card α)^3 ≤ G.triangle_finset.card :=
begin
  let l := ⌊4/ε⌋₊,
  let ε' : ℝ := ε/4,
  have hε' : 0 < ε/4 := by linarith,
  obtain ⟨L, hL⟩ := szemeredi_regularity' l hε',
  let δ : ℝ := sorry,
  -- have hδ' : 4 / ε < δ, sorry,
  have hδ : 0 < δ, sorry,
  have hδ₂ : δ * l ^ 3 < 1, sorry,
  refine ⟨δ, hδ, _⟩,
  introsI α hα G hG,
  casesI is_empty_or_nonempty α with i i,
  { simp [fintype.card_eq_zero] },
  cases lt_or_le (card α) l with hl hl,
  { have : (card α : ℝ)^3 < l^3 :=
      pow_lt_pow_of_lt_left (nat.cast_lt.2 hl) (nat.cast_nonneg _) (by norm_num),
    apply (mul_le_mul_of_nonneg_left this.le hδ.le).trans,
    apply hδ₂.le.trans,
    simp only [nat.one_le_cast],
    apply hG.triangle_finset_card_pos hε },
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := hL α G hl,

end

#exit

--   (hG : (G.edge_finset.card : ℝ) ≤ (card α)^3 * triangle_removal_bound ε (card α)) :
--   ∃ (G' ≤ G),
--     (G.edge_finset.card - G'.edge_finset.card : ℝ) ≤ (card α)^2 * ε
--       ∧ ∀ x y z, ¬ G.is_triangle x y z :=
-- sorry

end simple_graph

def contains_3AP (s : set ℕ) := ∃ a d, 0 < d ∧ a ∈ s ∧ a + d ∈ s ∧ a + 2*d ∈ s

theorem roth {δ : ℝ} (hδ : 0 < δ) : ∃ N, ∀ s ⊆ range N, δ * N ≤ s.card → contains_3AP s :=
begin

end
