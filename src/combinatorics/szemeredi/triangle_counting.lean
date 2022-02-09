/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .regularity_lemma
import combinatorics.simple_graph.subgraph

/-!
# Triangle counting lemma
-/

open finset fintype
open_locale big_operators

variables {α : Type*} (G : simple_graph α)

namespace simple_graph

/-- A `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
def is_n_clique (n : ℕ) (s : finset α) : Prop := s.card = n ∧ (s : set α).pairwise G.adj

instance [decidable_eq α] [decidable_rel G.adj] {n} {s : finset α} :
  decidable (G.is_n_clique n s) :=
decidable_of_iff (s.card = n ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.adj x y)
  (by simp [simple_graph.is_n_clique, set.pairwise])

/-- `G` has no triangles. -/
def no_triangles := ∀ t, ¬ G.is_n_clique 3 t

lemma bot_no_triangles : (⊥ : simple_graph α).no_triangles :=
begin
  rintro t ⟨ht₁, ht₂⟩,
  have : 1 < t.card,
  { rw ht₁,
    norm_num },
  rw finset.one_lt_card at this,
  obtain ⟨x, hx, y, hy, hxy⟩ := this,
  apply ht₂ hx hy hxy,
end

section triangle_finset
variables [fintype α] [decidable_eq α] [decidable_rel G.adj]

/-- The triangles in a graph as a finset. -/
def triangle_finset : finset (finset α) :=
(powerset_len 3 univ).filter $ G.is_n_clique 3

lemma mem_triangle_finset (s : finset α) :
  s ∈ G.triangle_finset ↔ s.card = 3 ∧ (s : set α).pairwise G.adj :=
by simp [triangle_finset, mem_powerset_len, is_n_clique]

lemma mem_triangle_finset' (s : finset α) :
  s ∈ G.triangle_finset ↔ G.is_n_clique 3 s :=
G.mem_triangle_finset s

lemma mem_triangle_finset'' (x y z : α) :
  {x, y, z} ∈ G.triangle_finset ↔ G.adj x y ∧ G.adj x z ∧ G.adj y z :=
begin
  rw [mem_triangle_finset],
  simp only [coe_insert, coe_singleton, set.pairwise_insert_of_symmetric G.symm,
    set.pairwise_singleton, true_and, set.mem_insert_iff, set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, ne.def],
  split,
  { rintro ⟨h, yz, xy, xz⟩,
    have : x ≠ y ∧ x ≠ z ∧ y ≠ z,
    { refine ⟨_, _, _⟩;
      { rintro rfl,
        simp only [insert_idem, insert_singleton_comm, insert_singleton_self_eq] at h,
        apply ne_of_lt _ h,
        rw nat.lt_succ_iff,
        apply card_insert_le _ _ } },
    tauto },
  rintro ⟨xy, xz, yz⟩,
  refine ⟨_, λ _, yz, λ _, xy, λ _, xz⟩,
  rw card_eq_three,
  exact ⟨_, _, _, G.ne_of_adj xy, G.ne_of_adj xz, G.ne_of_adj yz, rfl⟩,
end

lemma mem_triangle_finset''' {s : finset α} :
  s ∈ G.triangle_finset ↔ ∃ x y z, G.adj x y ∧ G.adj x z ∧ G.adj y z ∧ s = {x,y,z} :=
begin
  split,
  { intro h,
    obtain ⟨x, y, z, -, -, -, rfl⟩ := card_eq_three.1 ((G.mem_triangle_finset s).1 h).1,
    refine ⟨x, y, z, _⟩,
    rw mem_triangle_finset'' at h,
    tauto },
  rintro ⟨x, y, z, _, _, _, rfl⟩,
  rw mem_triangle_finset'',
  tauto
end

lemma triangle_finset_empty_iff : G.triangle_finset = ∅ ↔ G.no_triangles :=
by simp only [mem_triangle_finset, eq_empty_iff_forall_not_mem, no_triangles, is_n_clique]

end triangle_finset

open_locale classical

section triangle_free_far
variables [fintype α]

/-- A simple graph is `ε`-triangle-free far if one must remove a density of `ε` edges to make it
triangle-free. -/
def triangle_free_far (G : simple_graph α) (ε : ℝ) : Prop :=
∀ G' ≤ G, G'.no_triangles → ε * (card α)^2 ≤ (G.edge_finset.card - G'.edge_finset.card : ℝ)

lemma has_triangle_of_few_edges_removed {ε : ℝ} {G' : simple_graph α} (hG' : G' ≤ G)
  (hG : G.triangle_free_far ε)
  (hcard : (G.edge_finset.card - G'.edge_finset.card : ℝ) < ε * card α^2) :
  ∃ t, t ∈ G'.triangle_finset :=
begin
  apply nonempty_of_ne_empty,
  rw [ne.def, triangle_finset_empty_iff],
  intro hG'',
  apply not_le_of_lt hcard (hG _ hG' hG''),
end

lemma eps_eq_zero_of_no_triangles [nonempty α] {ε : ℝ} (hε : 0 ≤ ε) (hG : G.triangle_free_far ε)
  (hG' : G.no_triangles) :
  ε = 0 :=
begin
  have := hG G le_rfl hG',
  simp only [sub_self] at this,
  apply (nonpos_of_mul_nonpos_right this (sq_pos_of_ne_zero _ _)).antisymm hε,
  simp only [nat.cast_ne_zero, ←pos_iff_ne_zero, fintype.card_pos],
end

end triangle_free_far

noncomputable def bad_vertices (ε : ℝ) (X Y : finset α) :=
X.filter (λ x, ((Y.filter (G.adj x)).card : ℝ) < (G.edge_density X Y - ε) * Y.card)

lemma of_mem_bad_vertices {ε : ℝ} {X Y : finset α} :
  ∀ x ∈ G.bad_vertices ε X Y, ((Y.filter (G.adj x)).card : ℝ) ≤ (G.edge_density X Y - ε) * Y.card :=
λ x hx, (mem_filter.1 hx).2.le

lemma bad_vertices_eq {ε : ℝ} {X Y : finset α} :
  relation.pairs_finset G.adj (G.bad_vertices ε X Y) Y ⊆
    (G.bad_vertices ε X Y).bUnion (λ x, (Y.filter (G.adj x)).image (λ y, (x,y))) :=
begin
  rintro ⟨x, y⟩,
  simp only [mem_bUnion, mem_image, exists_prop, mem_filter, prod.mk.inj_iff,
    exists_eq_right_right, relation.mem_pairs_finset'],
  rintro ⟨hx, hy, hxy⟩,
  refine ⟨x, hx, ⟨hy, hxy⟩, rfl⟩,
end

lemma pairs_card_bad_le {ε : ℝ} {X Y : finset α} :
  ((relation.pairs_finset G.adj (G.bad_vertices ε X Y) Y).card : ℝ) ≤
    (G.bad_vertices ε X Y).card * Y.card * (G.edge_density X Y - ε) :=
begin
  refine (nat.cast_le.2 (card_le_of_subset G.bad_vertices_eq)).trans _,
  refine (nat.cast_le.2 card_bUnion_le).trans _,
  rw nat.cast_sum,
  simp_rw [card_image_of_injective _ (prod.mk.inj_left _)],
  apply (sum_le_sum G.of_mem_bad_vertices).trans,
  rw [sum_const, nsmul_eq_mul, mul_comm (_ - _), mul_assoc],
end

lemma edge_density_bad_vertices {ε : ℝ} {X Y : finset α} (hε : 0 ≤ ε)
  (dXY : 2 * ε ≤ G.edge_density X Y) :
  G.edge_density (G.bad_vertices ε X Y) Y ≤ G.edge_density X Y - ε :=
begin
  rw [edge_density_eq_edge_count_div_card, edge_count],
  refine div_le_of_nonneg_of_le_mul (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)) _ _,
  { apply sub_nonneg_of_le,
    linarith },
  rw mul_comm,
  apply G.pairs_card_bad_le,
end

@[simp] lemma edge_density_empty_left (s : finset α) : G.edge_density ∅ s = 0 :=
by simp [edge_density_eq_edge_count_div_card]

@[simp] lemma edge_density_empty_right (s : finset α) : G.edge_density s ∅ = 0 :=
by simp [edge_density_eq_edge_count_div_card]

lemma nonempty_of_edge_density_ne_zero_left {s t : finset α} :
  G.edge_density s t ≠ 0 → s.nonempty :=
begin
  rw nonempty_iff_ne_empty,
  rintro h rfl,
  exact h (edge_density_empty_left _ _),
end

lemma nonempty_of_edge_density_ne_zero_right {s t : finset α} :
  G.edge_density s t ≠ 0 → t.nonempty :=
begin
  rw nonempty_iff_ne_empty,
  rintro h rfl,
  exact h (edge_density_empty_right _ _),
end

lemma few_bad_vertices {X Y : finset α} {ε : ℝ} (hε₀ : 0 ≤ ε) (hε : ε ≤ 1)
  (dXY : 2 * ε ≤ G.edge_density X Y) (uXY : G.is_uniform ε X Y) :
  ((G.bad_vertices ε X Y).card : ℝ) ≤ X.card * ε :=
begin
  by_contra,
  rw not_le at h,
  have := G.edge_density_bad_vertices hε₀ dXY,
  have := uXY (G.bad_vertices ε X Y) (filter_subset _ _) Y set.subset.rfl h.le
    (mul_le_of_le_one_right (nat.cast_nonneg _) hε),
  rw abs_sub_lt_iff at this,
  linarith,
end

-- A subset of the triangles constructed in a weird way to make them easy to count
lemma triangle_split_helper {X Y Z : finset α} {ε : ℝ} :
  (X \ (G.bad_vertices ε X Y ∪ G.bad_vertices ε X Z)).bUnion
    (λ x, (((Y.filter (G.adj x)).product (Z.filter (G.adj x))).filter
      (λ (yz : _ × _), G.adj yz.1 yz.2)).image (prod.mk x)) ⊆
  (X.product (Y.product Z)).filter
    (λ (xyz : α × α × α), G.adj xyz.1 xyz.2.1 ∧ G.adj xyz.1 xyz.2.2 ∧ G.adj xyz.2.1 xyz.2.2) :=
begin
  rintro ⟨x, y, z⟩,
  simp only [mem_filter, mem_product, mem_bUnion, mem_sdiff, exists_prop, mem_union,
    mem_image, prod.exists, and_assoc, exists_imp_distrib, and_imp, prod.mk.inj_iff],
  rintro x hx - y z hy xy hz xz yz rfl rfl rfl,
  exact ⟨hx, hy, hz, xy, xz, yz⟩,
end

lemma good_vertices_triangle_card {X Y Z : finset α} {ε : ℝ} (hε : 0 ≤ ε)
  (dXY : 2 * ε ≤ G.edge_density X Y)
  (dXZ : 2 * ε ≤ G.edge_density X Z)
  (dYZ : 2 * ε ≤ G.edge_density Y Z)
  (uYZ : G.is_uniform ε Y Z) (x : α)
  (hx : x ∈ X \ (G.bad_vertices ε X Y ∪ G.bad_vertices ε X Z))  :
  ε^3 * Y.card * Z.card ≤ ((((Y.filter (G.adj x)).product (Z.filter (G.adj x))).filter
      (λ (yz : _ × _), G.adj yz.1 yz.2)).image (prod.mk x)).card :=
begin
  simp only [mem_sdiff, bad_vertices, mem_union, not_or_distrib, mem_filter, not_and_distrib,
    not_lt] at hx,
  rw [←or_and_distrib_left, and_or_distrib_left] at hx,
  simp only [false_or, and_not_self, mul_comm ((_ : ℝ) - _)] at hx,
  rcases hx with ⟨hx, hxY, hxZ⟩,
  have hY : (Y.card : ℝ) * ε ≤ (filter (G.adj x) Y).card,
  { exact (mul_le_mul_of_nonneg_left (by linarith) (nat.cast_nonneg _)).trans hxY },
  have hZ : (Z.card : ℝ) * ε ≤ (filter (G.adj x) Z).card,
  { exact (mul_le_mul_of_nonneg_left (by linarith) (nat.cast_nonneg _)).trans hxZ },
  rw card_image_of_injective _ (prod.mk.inj_left _),
  have := uYZ _ (filter_subset (G.adj x) _) _ (filter_subset (G.adj x) _) hY hZ,
  have : ε ≤ G.edge_density (filter (G.adj x) Y) (filter (G.adj x) Z),
  { rw abs_sub_lt_iff at this,
    linarith },
  refine le_trans _ (mul_le_of_nonneg_of_le_div (nat.cast_nonneg _)
    (by exact_mod_cast (nat.zero_le _)) this),
  refine eq.trans_le _ (mul_le_mul_of_nonneg_left
    (mul_le_mul hY hZ (mul_nonneg (nat.cast_nonneg _) hε) (nat.cast_nonneg _)) hε),
  ring,
end

-- can probably golf things by relaxing < to ≤
lemma triangle_counting {X Y Z : finset α} {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
  (dXY : 2 * ε ≤ G.edge_density X Y) (uXY : G.is_uniform ε X Y)
  (dXZ : 2 * ε ≤ G.edge_density X Z) (uXZ : G.is_uniform ε X Z)
  (dYZ : 2 * ε ≤ G.edge_density Y Z) (uYZ : G.is_uniform ε Y Z) :
  (1 - 2 * ε) * ε^3 * X.card * Y.card * Z.card ≤
    ((X.product $ Y.product Z).filter $ λ (xyz : α × α × α),
      G.adj xyz.1 xyz.2.1 ∧ G.adj xyz.1 xyz.2.2 ∧ G.adj xyz.2.1 xyz.2.2).card :=
begin
  have h₁ : ((G.bad_vertices ε X Y).card : ℝ) ≤ X.card * ε := G.few_bad_vertices hε₀.le hε₁ dXY uXY,
  have h₂ : ((G.bad_vertices ε X Z).card : ℝ) ≤ X.card * ε := G.few_bad_vertices hε₀.le hε₁ dXZ uXZ,
  let X' := X \ (G.bad_vertices ε X Y ∪ G.bad_vertices ε X Z),
  have : X'.bUnion _ ⊆ (X.product (Y.product Z)).filter
    (λ (xyz : α × α × α), G.adj xyz.1 xyz.2.1 ∧ G.adj xyz.1 xyz.2.2 ∧ G.adj xyz.2.1 xyz.2.2),
  { apply triangle_split_helper },
  refine le_trans _ (nat.cast_le.2 (card_le_of_subset this)),
  rw [card_bUnion, nat.cast_sum],
  { have := λ x hx, G.good_vertices_triangle_card hε₀.le dXY dXZ dYZ uYZ x hx,
    apply le_trans _ (le_sum_of_forall_le X' _ _ this),
    rw nsmul_eq_mul,
    have hX' : (1 - 2 * ε) * X.card ≤ X'.card,
    { have i : G.bad_vertices ε X Y ∪ G.bad_vertices ε X Z ⊆ X,
      { apply union_subset (filter_subset _ _) (filter_subset _ _) },
      rw [sub_mul, one_mul, card_sdiff i, nat.cast_sub (card_le_of_subset i), sub_le_sub_iff_left,
        mul_assoc, mul_comm ε, two_mul],
      refine (nat.cast_le.2 (card_union_le _ _)).trans _,
      rw nat.cast_add,
      refine add_le_add h₁ h₂ },
    refine le_trans (le_of_eq (by ring)) (mul_le_mul_of_nonneg_right hX' _),
    exact mul_nonneg (mul_nonneg (pow_nonneg hε₀.le _) (nat.cast_nonneg _)) (nat.cast_nonneg _) },
  rintro x hx y hy t,
  rw disjoint_left,
  simp only [prod.forall, mem_image, not_exists, exists_prop, mem_filter, prod.mk.inj_iff,
    exists_imp_distrib, and_imp, not_and, mem_product, or.assoc],
  rintro - - - - - - _ _ _ rfl rfl _ _ _ _ _ _ _ rfl _,
  exact t rfl,
end

variables [fintype α]

lemma triangle_counting2 {X Y Z : finset α} {ε : ℝ}
  (dXY : 2 * ε ≤ G.edge_density X Y) (uXY : G.is_uniform ε X Y) (hXY : disjoint X Y)
  (dXZ : 2 * ε ≤ G.edge_density X Z) (uXZ : G.is_uniform ε X Z) (hXZ : disjoint X Z)
  (dYZ : 2 * ε ≤ G.edge_density Y Z) (uYZ : G.is_uniform ε Y Z) (hYZ : disjoint Y Z) :
  (1 - 2 * ε) * ε^3 * X.card * Y.card * Z.card ≤ G.triangle_finset.card :=
begin
  cases le_or_lt ε 0 with hε₀ hε₀,
  { apply le_trans _ (nat.cast_nonneg _),
    rw [mul_assoc, mul_assoc],
    refine mul_nonpos_of_nonpos_of_nonneg _ (by exact_mod_cast (nat.zero_le _)),
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (pow_bit1_nonpos_iff.2 hε₀) },
  cases lt_or_le 1 ε with hε₁ hε₁,
  { apply le_trans _ (nat.cast_nonneg _),
    rw [mul_assoc, mul_assoc, mul_assoc],
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (mul_nonneg (pow_nonneg hε₀.le _) (by exact_mod_cast (nat.zero_le _))) },
  apply (G.triangle_counting hε₀ hε₁ dXY uXY dXZ uXZ dYZ uYZ).trans _,
  rw nat.cast_le,
  refine card_le_card_of_inj_on (λ xyz, {xyz.1, xyz.2.1, xyz.2.2}) _ _,
  { rintro ⟨x, y, z⟩,
    simp only [and_imp, mem_filter, mem_product],
    intros hx hy hz xy xz yz,
    rw mem_triangle_finset'',
    exact ⟨xy, xz, yz⟩ },
  rintro ⟨x₁, y₁, z₁⟩ h₁ ⟨x₂, y₂, z₂⟩ h₂ t,
  simp only [mem_filter, mem_product] at h₁ h₂,
  apply dumb_thing hXY hXZ hYZ t;
  tauto
end

@[simps]
def reduced_graph (ε : ℝ) (P : finpartition (univ : finset α)) : simple_graph α :=
{ adj := λ x y, G.adj x y ∧
    ∃ U V ∈ P.parts, x ∈ U ∧ y ∈ V ∧ U ≠ V ∧ G.is_uniform (ε/8) U V ∧ ε/4 ≤ G.edge_density U V,
  symm := λ x y,
  begin
    rintro ⟨xy, U, UP, V, VP, xU, yV, UV, GUV, εUV⟩,
    refine ⟨G.symm xy, V, VP, U, UP, yV, xU, UV.symm, GUV.symm, _⟩,
    rwa edge_density_comm,
  end,
  loopless := λ x ⟨h, _⟩, G.loopless x h }

variables {G}

lemma reduced_graph_le {ε : ℝ} {P : finpartition (univ : finset α)} : reduced_graph G ε P ≤ G :=
λ x y ⟨h, _⟩, h

lemma triangle_free_far_of_disjoint_triangles_aux
  (tris : finset (finset α)) (htris : tris ⊆ G.triangle_finset)
  (pd : (tris : set (finset α)).pairwise (λ x y, (x ∩ y).card ≤ 1)) :
  ∀ (G' ≤ G), G'.no_triangles → tris.card ≤ G.edge_finset.card - G'.edge_finset.card :=
begin
  intros G' hG hG',
  rw [←card_sdiff (edge_finset_mono hG), ←card_attach],
  by_contra,
  push_neg at h,
  have : ∀ t ∈ tris, ∃ x y ∈ t, x ≠ y ∧ ⟦(x, y)⟧ ∈ G.edge_finset \ G'.edge_finset,
  { intros t ht,
    by_contra i,
    suffices : t ∈ G'.triangle_finset,
    { rw ←triangle_finset_empty_iff at hG',
      simpa [hG'] using this },
    simp only [not_exists, exists_prop, not_and, mem_sdiff, not_not, mem_edge_finset,
      exists_and_distrib_left, ne.def, mem_edge_set] at i,
    obtain ⟨x, y, z, xy, xz, yz, rfl⟩ := (mem_triangle_finset''' _).1 (htris ht),
    rw mem_triangle_finset'',
    refine ⟨i _ _ _ (G.ne_of_adj xy) xy _, i _ _ _ (G.ne_of_adj xz) xz _,
      i _ _ _ (G.ne_of_adj yz) yz _⟩;
    simp },
  choose fx hfx fy hfy hfne fmem using this,
  let f : {x // x ∈ tris} → sym2 α := λ t, ⟦(fx _ t.2, fy _ t.2)⟧,
  have hf : ∀ x ∈ tris.attach, f x ∈ G.edge_finset \ G'.edge_finset := λ x hx, fmem _ _,
  obtain ⟨⟨t₁, ht₁⟩, -, ⟨t₂, ht₂⟩, -, tne, t : ⟦_⟧ = ⟦_⟧⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to h hf,
  have : t₁ ≠ t₂,
  { simpa using tne },
  dsimp at t,
  have i := pd ht₁ ht₂ this,
  simp only [finset.card_le_one_iff, mem_inter, and_imp] at i,
  rw sym2.eq_iff at t,
  cases t,
  { exact hfne _ _ (i (hfx t₁ ht₁) (t.1.symm ▸ hfx t₂ ht₂) (hfy t₁ ht₁) (t.2.symm ▸ hfy t₂ ht₂)) },
  { exact hfne _ _ (i (hfx t₁ ht₁) (t.1.symm ▸ hfy t₂ ht₂) (hfy t₁ ht₁) (t.2.symm ▸ hfx t₂ ht₂)) }
end

lemma triangle_free_far_of_disjoint_triangles {ε : ℝ}
  (tris : finset (finset α)) (htris : tris ⊆ G.triangle_finset)
  (pd : (tris : set (finset α)).pairwise (λ x y, (x ∩ y).card ≤ 1))
  (tris_big : ε * card α ^ 2 ≤ tris.card) :
  G.triangle_free_far ε :=
begin
  intros G' hG hG',
  rw ←nat.cast_sub (card_le_of_subset (edge_finset_mono hG)),
  apply tris_big.trans
    (nat.cast_le.2 (triangle_free_far_of_disjoint_triangles_aux tris htris pd G' hG hG')),
end

lemma reduced_double_edges {ε : ℝ} {P : finpartition (univ : finset α)} :
  univ.filter (λ (xy : α × α), G.adj xy.1 xy.2) \
    univ.filter (λ (xy : α × α), (reduced_graph G ε P).adj xy.1 xy.2) ⊆
      (P.non_uniform_pairs G (ε/8)).bUnion (λ UV, UV.1.product UV.2) ∪
        P.parts.bUnion (λ U, U.off_diag) ∪
          (P.parts.off_diag.filter (λ (UV : _ × _), G.edge_density UV.1 UV.2 < ε/4)).bUnion
            (λ UV, (UV.1.product UV.2).filter (λ xy, G.adj xy.1 xy.2)) :=
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
  by_cases h₂ : G.is_uniform (ε/8) U V,
  { exact or.inr (or.inr ⟨U, V, hU, hV, hUV, h' _ hU _ hV hx hy hUV h₂, hx, hy, h⟩) },
  { exact or.inl ⟨U, V, hU, hV, hUV, h₂, hx, hy⟩ }
end

-- We will break up the sum more later
lemma non_uniform_killed_card {ε : ℝ} {P : finpartition (univ : finset α)} :
  (((P.non_uniform_pairs G ε).bUnion (λ UV, UV.1.product UV.2)).card : ℝ) ≤
    (∑ i in P.non_uniform_pairs G ε, i.1.card * i.2.card : ℝ) :=
begin
  norm_cast,
  simp_rw ←card_product,
  exact card_bUnion_le,
end

lemma internal_killed_card [nonempty α]
  {P : finpartition (univ : finset α)} (hP : P.is_equipartition) :
  ((P.parts.bUnion (λ U, U.off_diag)).card : ℝ) ≤ card α * (card α + P.parts.card) / P.parts.card :=
begin
  have : (P.parts.bUnion (λ U, U.off_diag)).card ≤
    P.parts.card * (card α / P.parts.card) * (card α / P.parts.card + 1),
  { rw mul_assoc,
    apply card_bUnion_le_card_mul,
    intros U hU,
    suffices : (U.card - 1) * U.card ≤ card α / P.parts.card * (card α / P.parts.card + 1),
    { rwa [nat.mul_sub_right_distrib, one_mul, ←off_diag_card] at this },
    have := hP.card_part_le_average_add_one hU,
    apply nat.mul_le_mul ((nat.sub_le_sub_right this 1).trans _) this,
    simp only [nat.add_succ_sub_one, add_zero] },
  refine (nat.cast_le.2 this).trans _,
  have i : (_ : ℝ) ≠ 0 := nat.cast_ne_zero.2 (P.parts_nonempty $
    univ_nonempty.ne_empty).card_pos.ne',
  rw [mul_div_assoc, div_add_same i, nat.cast_mul, nat.cast_add_one],
  refine mul_le_mul _ _ (nat.cast_add_one_pos _).le (nat.cast_nonneg _),
  { rw [nat.cast_le, mul_comm],
    apply nat.div_mul_le_self },
  apply add_le_add_right,
  apply nat.cast_div_le,
end

-- this is stated with ε but might need to be applied with ε/2 or something
lemma sparse_card {P : finpartition (univ : finset α)} (hP : P.is_equipartition) {ε : ℝ}
  (hε : 0 ≤ ε) :
  (((P.parts.off_diag.filter (λ (UV : _ × _), G.edge_density UV.1 UV.2 < ε)).bUnion
            (λ UV, (UV.1.product UV.2).filter (λ xy, G.adj xy.1 xy.2))).card : ℝ) ≤
  ε * (card α + P.parts.card)^2 :=
begin
  refine (nat.cast_le.2 card_bUnion_le).trans _,
  rw nat.cast_sum,
  change ∑ x in _, G.edge_count _ _ ≤ _,
  have : ∀ UV ∈ P.parts.off_diag.filter (λ (UV : _ × _), G.edge_density UV.1 UV.2 < ε),
    G.edge_count UV.1 UV.2 ≤ ε * (UV.1.card * UV.2.card),
  { rintro ⟨U, V⟩,
    simp only [and_imp, mem_off_diag, mem_filter, ne.def,
      simple_graph.edge_density_eq_edge_count_div_card],
    intros hU hV hUV e,
    apply le_of_lt,
    rwa [←div_lt_iff],
    exact mul_pos (nat.cast_pos.2 (P.nonempty_of_mem_parts hU).card_pos)
      (nat.cast_pos.2 (P.nonempty_of_mem_parts hV).card_pos) },
  apply (sum_le_sum this).trans,
  refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (λ i hi _, _)).trans _,
  { exact mul_nonneg hε (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)) },
  rw ←mul_sum,
  apply mul_le_mul_of_nonneg_left _ hε,
  refine (sum_le_of_forall_le P.parts.off_diag (λ i, (i.1.card * i.2.card : ℝ))
    ((card α / P.parts.card + 1)^2 : ℕ) _).trans _,
  { simp only [prod.forall, finpartition.mem_non_uniform_pairs, and_imp, mem_off_diag],
    rintro U V hU hV -,
    rw [sq, ←nat.cast_mul, nat.cast_le],
    exact nat.mul_le_mul (hP.card_part_le_average_add_one hU)
      (hP.card_part_le_average_add_one hV) },
  rw [nsmul_eq_mul, ←nat.cast_mul, ←nat.cast_add, ←nat.cast_pow, nat.cast_le, off_diag_card,
    nat.mul_sub_right_distrib],
  apply (nat.sub_le _ _).trans,
  rw [←sq, ←mul_pow],
  apply nat.pow_le_pow_of_le_left,
  rw [mul_add, mul_one],
  apply add_le_add_right,
  apply nat.mul_div_le,
end

lemma triangle_free_far.not_no_triangles [nonempty α] {ε : ℝ} (hG : G.triangle_free_far ε)
  (hε : 0 < ε) : ¬ G.no_triangles :=
λ hG', hε.ne' (eps_eq_zero_of_no_triangles G hε.le hG hG')

lemma triangle_free_far.triangle_finset_card_pos {ε : ℝ} [nonempty α] (hG : G.triangle_free_far ε)
  (hε : 0 < ε) : 0 < G.triangle_finset.card :=
begin
  rw [finset.card_pos, nonempty_iff_ne_empty, ne.def, triangle_finset_empty_iff],
  apply hG.not_no_triangles hε,
end

lemma sum_irreg_pairs_le_of_uniform [nonempty α] {ε : ℝ} (hε : 0 < ε)
  (P : finpartition univ) (hP : P.is_equipartition) (hG : P.is_uniform G ε) :
  (∑ i in P.non_uniform_pairs G ε, i.1.card * i.2.card : ℝ) < ε * (card α + P.parts.card)^2 :=
begin
  refine (sum_le_of_forall_le (P.non_uniform_pairs G ε) (λ i, (i.1.card * i.2.card : ℝ))
    ((card α / P.parts.card + 1)^2 : ℕ) _).trans_lt _,
  { simp only [prod.forall, finpartition.mem_non_uniform_pairs, and_imp],
    rintro U V hU hV hUV -,
    rw [sq, ←nat.cast_mul, nat.cast_le],
    exact nat.mul_le_mul (hP.card_part_le_average_add_one hU)
      (hP.card_part_le_average_add_one hV) },
  rw nsmul_eq_mul,
  refine (mul_le_mul_of_nonneg_right hG (nat.cast_nonneg _)).trans_lt _,
  rw [mul_right_comm _ ε, mul_comm ε],
  apply mul_lt_mul_of_pos_right _ hε,
  norm_cast,
  apply nat.thing2 _ _,
  exact (P.parts_nonempty $ univ_nonempty.ne_empty).card_pos,
end

lemma sum_irreg_pairs_le_of_uniform' [nonempty α] {ε : ℝ} (hε : 0 < ε)
  (P : finpartition univ) (hP : P.is_equipartition) (hG : P.is_uniform G ε) :
  (((P.non_uniform_pairs G ε).bUnion (λ UV, UV.1.product UV.2)).card : ℝ) < 4 * ε * (card α)^2 :=
begin
  apply non_uniform_killed_card.trans_lt,
  apply (sum_irreg_pairs_le_of_uniform hε P hP hG).trans_le,
  suffices : ε * ((card α) + P.parts.card)^2 ≤ ε * (card α + card α)^2,
  { exact this.trans (le_of_eq (by ring)) },
  apply mul_le_mul_of_nonneg_left _ hε.le,
  refine pow_le_pow_of_le_left (by exact_mod_cast (nat.zero_le _)) _ _,
  exact add_le_add_left (nat.cast_le.2 P.card_parts_le_card) _,
end

lemma sum_sparse {ε : ℝ} (hε : 0 ≤ ε)
  (P : finpartition univ) (hP : P.is_equipartition) :
  (((P.parts.off_diag.filter (λ (UV : _ × _), G.edge_density UV.1 UV.2 < ε)).bUnion
            (λ UV, (UV.1.product UV.2).filter (λ xy, G.adj xy.1 xy.2))).card : ℝ) ≤
              4 * ε * (card α)^2 :=
begin
  refine (sparse_card hP hε).trans _,
  suffices : ε * ((card α) + P.parts.card)^2 ≤ ε * (card α + card α)^2,
  { exact this.trans (le_of_eq (by ring)) },
  apply mul_le_mul_of_nonneg_left _ hε,
  refine pow_le_pow_of_le_left (by exact_mod_cast (nat.zero_le _)) _ _,
  exact add_le_add_left (nat.cast_le.2 P.card_parts_le_card) _,
end

lemma internal_killed_card' [nonempty α] {ε : ℝ} (hε : 0 < ε)
  {P : finpartition (univ : finset α)} (hP : P.is_equipartition) (hP' : 4 / ε ≤ P.parts.card) :
  ((P.parts.bUnion (λ U, U.off_diag)).card : ℝ) ≤ ε / 2 * (card α)^2 :=
begin
  apply (internal_killed_card hP).trans,
  rw div_le_iff,
  have : (card α : ℝ) + P.parts.card ≤ 2 * card α,
  { rw two_mul,
    apply add_le_add_left,
    exact nat.cast_le.2 P.card_parts_le_card },
  apply (mul_le_mul_of_nonneg_left this (nat.cast_nonneg _)).trans,
  suffices : 1 ≤ (ε/4) * P.parts.card,
  { rw [mul_left_comm, ←sq],
    convert mul_le_mul_of_nonneg_left this (mul_nonneg zero_le_two (sq_nonneg (card α))) using 1;
    ring },
  rwa [←div_le_iff', one_div_div],
  { linarith },
  rw nat.cast_pos,
  exact (P.parts_nonempty $ univ_nonempty.ne_empty).card_pos
end

/-- An explicit form for the constant in the triangle removal lemma. -/
noncomputable def triangle_removal_bound (ε : ℝ) : ℝ :=
min (1 / (2 * ⌈4/ε⌉₊^3)) ((1 - ε/4) * (ε/(16 * szemeredi_bound (ε/8) ⌈4/ε⌉₊))^3)

lemma triangle_removal_bound_pos {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
  0 < triangle_removal_bound ε :=
begin
  apply lt_min,
  { rw one_div_pos,
    refine mul_pos zero_lt_two (pow_pos _ _),
    rw [nat.cast_pos, nat.lt_ceil, nat.cast_zero],
    exact div_pos zero_lt_four hε },
  { refine mul_pos (by linarith) (pow_pos (div_pos hε (mul_pos (by norm_num) _)) _),
    rw nat.cast_pos,
    exact (initial_bound_pos _ _).trans_le (initial_bound_le_szemeredi_bound _ _) }
end

lemma triangle_removal_bound_mul_cube_lt {ε : ℝ} (hε : 0 < ε) :
  (triangle_removal_bound ε) * ⌈4/ε⌉₊^3 < 1 :=
begin
  have : triangle_removal_bound ε ≤ _ := min_le_left _ _,
  apply (mul_le_mul_of_nonneg_right this (pow_nonneg (nat.cast_nonneg _) _)).trans_lt,
  rw [←div_div_eq_div_mul, div_mul_cancel],
  { norm_num },
  apply ne_of_gt (pow_pos _ _),
  rw [nat.cast_pos, nat.lt_ceil, nat.cast_zero],
  exact div_pos zero_lt_four hε
end

lemma annoying_thing {n k : ℕ} (hk : 0 < k) (hn : k ≤ n) : n < 2 * k * (n / k) :=
begin
  rw [mul_assoc, two_mul, ←add_lt_add_iff_right (n % k), add_right_comm, add_assoc,
    nat.mod_add_div n k, add_comm, add_lt_add_iff_right],
  apply (nat.mod_lt n hk).trans_le,
  have : 1 ≤ n / k,
  { rwa [nat.le_div_iff_mul_le _ _ hk, one_mul] },
  simpa using nat.mul_le_mul_left k this,
end

lemma card_bound [nonempty α] {ε : ℝ} {X : finset α} {P : finpartition (univ : finset α)}
  (hP₁ : P.is_equipartition)
  (hP₃ : P.parts.card ≤ szemeredi_bound (ε / 8) ⌈4/ε⌉₊) (hX : X ∈ P.parts) :
  (card α : ℝ) / (2 * szemeredi_bound (ε / 8) ⌈4/ε⌉₊) ≤ X.card :=
begin
  refine le_trans _ (nat.cast_le.2 (hP₁.average_le_card_part hX)),
  rw div_le_iff',
  { norm_cast,
    apply (annoying_thing (P.parts_nonempty $ univ_nonempty.ne_empty).card_pos
      P.card_parts_le_card).le.trans,
    apply nat.mul_le_mul_right,
    exact nat.mul_le_mul_left _ hP₃ },
  refine mul_pos zero_lt_two _,
  rw nat.cast_pos,
  apply (initial_bound_pos _ _).trans_le (initial_bound_le_szemeredi_bound _ _)
end

lemma triangle_removal_aux [nonempty α] {ε : ℝ}
  (hε : 0 < ε) (hε₁ : ε ≤ 1)
  {P : finpartition univ}
  (hP₁ : P.is_equipartition)
  (hP₃ : P.parts.card ≤ szemeredi_bound (ε / 8) ⌈4/ε⌉₊)
  {t : finset α} (ht : t ∈ (G.reduced_graph ε P).triangle_finset) :
  triangle_removal_bound ε * ↑(card α) ^ 3 ≤ ↑(G.triangle_finset.card) :=
begin
  rw [mem_triangle_finset, card_eq_three] at ht,
  obtain ⟨⟨x, y, z, xy, xz, yz, rfl⟩, ht⟩ := ht,
  simp only [coe_insert, coe_singleton] at ht,
  have hx : x ∈ ({x,y,z} : set α) := or.inl rfl,
  have hy : y ∈ ({x,y,z} : set α) := or.inr (or.inl rfl),
  have hz : z ∈ ({x,y,z} : set α) := or.inr (or.inr rfl),
  have hxy : (G.reduced_graph ε P).adj x y := ht hx hy xy,
  have hxz : (G.reduced_graph ε P).adj x z := ht hx hz xz,
  have hyz : (G.reduced_graph ε P).adj y z := ht hy hz yz,
  obtain ⟨xy, X, hX, Y, hY, xX, yY, nXY, uXY, dXY⟩ := hxy,
  obtain ⟨xz, X', hX', Z, hZ, xX', zZ, nXZ, uXZ, dXZ⟩ := hxz,
  cases P.disjoint.elim hX hX' (not_disjoint_iff.2 ⟨x, xX, xX'⟩),
  obtain ⟨yz, Y', hY', Z', hZ', yY', zZ', nYZ, uYZ, dYZ⟩ := hyz,
  cases P.disjoint.elim hY hY' (not_disjoint_iff.2 ⟨y, yY, yY'⟩),
  cases P.disjoint.elim hZ hZ' (not_disjoint_iff.2 ⟨z, zZ, zZ'⟩),
  have dXY := P.disjoint hX hY nXY,
  have dXZ := P.disjoint hX hZ nXZ,
  have dYZ := P.disjoint hY hZ nYZ,
  have : 2 * (ε/8) = ε/4, by ring,
  have i := triangle_counting2 G (by rwa this) uXY dXY (by rwa this) uXZ dXZ (by rwa this) uYZ dYZ,
  apply le_trans _ i,
  rw [this, triangle_removal_bound],
  refine (mul_le_mul_of_nonneg_right (min_le_right (_:ℝ) _) (pow_nonneg _ _)).trans _,
  apply nat.cast_nonneg,
  rw [mul_assoc, ←mul_pow, div_mul_eq_mul_div, (show (16:ℝ) = 8 * 2, by norm_num), mul_assoc (8:ℝ),
    ←div_mul_div, mul_pow, ←mul_assoc],
  suffices : ((card α : ℝ) / (2 * szemeredi_bound (ε / 8) ⌈4 / ε⌉₊)) ^ 3 ≤ X.card * Y.card * Z.card,
  { refine (mul_le_mul_of_nonneg_left this (mul_nonneg _ _)).trans _,
    { linarith },
    { apply pow_nonneg,
      apply div_nonneg hε.le,
      norm_num },
    apply le_of_eq,
    ring },
  rw [pow_succ, sq, mul_assoc],
  refine mul_le_mul (card_bound hP₁ hP₃ hX) _ (mul_nonneg _ _) (nat.cast_nonneg _),
  refine mul_le_mul (card_bound hP₁ hP₃ hY) (card_bound hP₁ hP₃ hZ) _ (nat.cast_nonneg _),
  all_goals
  { exact div_nonneg (nat.cast_nonneg _) (mul_nonneg (by norm_num) $ nat.cast_nonneg _) }
end

end simple_graph
