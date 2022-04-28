import .clique .degree_sum
import algebra.big_operators

open_locale big_operators

namespace simple_graph

variables {V : Type*} {G : simple_graph V}

/- recall that "triangle free" means `G.clique_free 3` -/

lemma common_neighbors_of_triangle_free (htf : G.clique_free 3)
  {u v : V} (huv : G.adj u v) :
  G.common_neighbors u v = ∅ :=
begin
  classical,
  ext w,
  simp only [mem_common_neighbors, set.mem_empty_eq, iff_false],
  rintro ⟨huw, hvw⟩,
  apply htf {u, v, w},
  simp only [*, is_3_clique_triple_iff, and_self],
end

lemma degree_add_degree_le_of_triangle_free [fintype V]
  (htf : G.clique_free 3)
  {u v : V} (huv : G.adj u v)
  [fintype (G.neighbor_set u)] [fintype (G.neighbor_set v)] :
  G.degree u + G.degree v ≤ fintype.card V :=
begin
  classical,
  convert_to (G.neighbor_set u ∪ G.neighbor_set v).to_finset.card ≤ _,
  { rw [set.to_finset_union, finset.card_union_eq],
    { simp },
    { rw [set.to_finset_disjoint_iff, set.disjoint_iff_inter_eq_empty,
        ← common_neighbors_eq, common_neighbors_of_triangle_free htf huv] } },
  exact finset.card_le_univ _,
end

lemma sum_degree_pow_two_le_of_triangle_free [fintype V]
  [decidable_eq V] [decidable_rel G.adj]
  (htf : G.clique_free 3) :
  ∑ v, G.degree v ^ 2 ≤ G.edge_finset.card * fintype.card V :=
begin
  calc ∑ v, G.degree v ^ 2
        = ∑ v, ∑ e in G.incidence_finset v, G.degree v : _
    ... = ∑ e in G.edge_finset, ∑ v in finset.univ.filter (∈ e), G.degree v : _
    ... ≤ ∑ e in G.edge_finset, fintype.card V : _
    ... = G.edge_finset.card * fintype.card V : _,
  { simp only [pow_two, finset.sum_const, card_incidence_finset_eq_degree,
      nsmul_eq_mul, nat.cast_id], },
  { simp only [finset.sum_filter],
    rw [finset.sum_comm],
    apply finset.sum_congr rfl,
    rintro u -,
    rw [← finset.sum_filter],
    apply finset.sum_congr _ (λ _ _, rfl),
    ext e,
    refine sym2.ind (λ v w, _) e,
    simp [mk_mem_incidence_set_iff], },
  { apply finset.sum_le_sum,
    intros e he,
    rw mem_edge_finset at he,
    refine sym2.ind (λ v w he, _) e he,
    simp only [mem_edge_set] at he,
    simp only [finset.filter_or, eq_comm, finset.filter_eq, sym2.mem_iff, finset.mem_univ, if_true],
    rw [finset.sum_union],
    { simp only [finset.sum_singleton],
      exact degree_add_degree_le_of_triangle_free htf he },
    { simp only [finset.disjoint_singleton, ne.def, he.ne, not_false_iff] } },
  { rw [finset.sum_const, nsmul_eq_mul, nat.cast_id] },
end

lemma cauchy {α : Type*} [fintype α] (f : α → ℕ) :
  (∑ x, f x) ^ 2 ≤ fintype.card α * ∑ x, f x ^ 2 :=
begin
  sorry
end

lemma card_edge_set_le_of_triangle_free [fintype V]
  [decidable_eq V] [decidable_rel G.adj]
  (htf : G.clique_free 3) :
  G.edge_finset.card ≤ fintype.card V ^ 2 / 4 :=
begin
  have := calc (2 * G.edge_finset.card) ^ 2
        = (∑ v, G.degree v) ^ 2 : by rw G.sum_degrees_eq_twice_card_edges
    ... ≤ fintype.card V * (∑ v, G.degree v ^ 2) : cauchy _
    ... ≤ fintype.card V * (G.edge_finset.card * fintype.card V) :
      mul_le_mul (le_refl _) (sum_degree_pow_two_le_of_triangle_free htf) (zero_le _) (zero_le _)
    ... = fintype.card V ^ 2 * G.edge_finset.card : by ring,
  obtain (h : G.edge_finset.card = 0) | h := eq_zero_or_pos,
  { simp [h] },
  { rw [pow_two, ← mul_assoc, mul_le_mul_right h, mul_comm 2, mul_assoc] at this,
    rw [nat.le_div_iff_mul_le _ _ (by norm_num : 0 < 4)],
    exact this },
end

/-- Theorem 2 in Bollobas "Modern Graph Theory" -/
theorem not_triangle_free_of_lt_card_edge_set [fintype V]
  [decidable_eq V] [decidable_rel G.adj]
  (h : fintype.card V ^ 2 / 4 < G.edge_finset.card) : ¬ G.clique_free 3 :=
begin
  classical,
  contrapose! h,
  convert card_edge_set_le_of_triangle_free h,
end

@[simp] lemma two_mul_add_one_div_two (n : ℕ) : (2*n + 1) / 2 = n :=
begin
  sorry
end

lemma four_mul_add_one_div_four (n : ℕ) : (4*n + 1) / 4 = n :=
begin
  sorry
end

lemma div_four_eq (n : ℕ) :
  n ^ 2 / 4 = (n / 2) * ((n + 1) / 2) :=
begin
  obtain ⟨k, rfl | rfl⟩ := nat.even_or_odd' n,
  { norm_num [mul_pow],
    rw pow_two, },
  { simp [pow_two, add_assoc],
    simp [mul_add, add_mul],
    convert_to (4 * (k * (k + 1)) + 1) / 4 = _,
    { congr' 1,
      ring, },
    rw [four_mul_add_one_div_four], },
end

instance (V W : Type*) [decidable_eq V] [decidable_eq W] :
  decidable_rel (complete_bipartite_graph V W).adj :=
begin
  intros a b,
  obtain (a|a) := a; obtain (b|b) := b; simp; apply_instance,
end

lemma bipartite_num_edges (n : ℕ) :
  (complete_bipartite_graph (fin (n / 2)) (fin ((n + 1) / 2))).edge_finset.card
  = n ^ 2 / 4 :=
begin
  rw div_four_eq,
  sorry,
end

/-- Therefore the bound in `simple_graph.not_triangle_free_of_lt_card_edge_set` is strict. -/
lemma bipartite_triangle_free (n : ℕ) :
  (complete_bipartite_graph (fin (n / 2)) (fin ((n + 1) / 2))).clique_free 3 :=
begin
  simp_rw [clique_free, is_3_clique_iff],
  push_neg,
  intros s a b c,
  simp,
  obtain (a|a) := a; obtain (b|b) := b; obtain (c|c) := c; simp,
end

end simple_graph
