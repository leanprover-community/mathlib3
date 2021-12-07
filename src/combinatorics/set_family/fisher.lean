import data.real.basic
import algebra.big_operators.ring
import linear_algebra.finite_dimensional
import data.matrix.rank

open finset finite_dimensional
open_locale big_operators

lemma product_sdiff_diag {α : Type*} [decidable_eq α] {s : finset α} :
  s.product s \ s.diag = s.off_diag :=
by rw [←diag_union_off_diag, union_comm, union_sdiff_self,
    sdiff_eq_self_of_disjoint (disjoint_diag_off_diag _).symm]

lemma product_sdiff_off_diag {α : Type*} [decidable_eq α] {s : finset α} :
  s.product s \ s.off_diag = s.diag :=
by rw [←diag_union_off_diag, union_sdiff_self, sdiff_eq_self_of_disjoint (disjoint_diag_off_diag _)]

lemma union_diag {α : Type*} [decidable_eq α] {s t : finset α} :
  (s ∪ t).diag = s.diag ∪ t.diag :=
by { ext ⟨i, j⟩, simp only [mem_diag, mem_union, or_and_distrib_right] }

lemma union_off_diag {α : Type*} [decidable_eq α] {s t : finset α} (h : disjoint s t) :
  (s ∪ t).off_diag = s.off_diag ∪ t.off_diag ∪ s.product t ∪ t.product s :=
begin
  ext ⟨i, j⟩,
  simp only [mem_union, mem_product, mem_off_diag, mem_union, or_assoc, or_and_distrib_right,
    and_or_distrib_left, ←and_assoc],
  rw [or_congr_right'],
  rw [←or_rotate, or_congr_right'],
  rw or_comm,
  refine or_congr (and_iff_left_of_imp _) (and_iff_left_of_imp _),
  { rintro ⟨hi, hj⟩,
    exact h.forall_ne_finset hi hj },
  { rintro ⟨hi, hj⟩,
    exact h.symm.forall_ne_finset hi hj },
end

@[simp] lemma singleton_off_diag {α : Type*} [decidable_eq α] (a : α) :
  ({a} : finset α).off_diag = ∅ :=
by simp [←finset.card_eq_zero]

lemma singleton_diag {α : Type*} [decidable_eq α] (a : α) : ({a} : finset α).diag = {(a, a)} :=
by rw [←product_sdiff_off_diag, singleton_off_diag, sdiff_empty, singleton_product_singleton]

lemma insert_diag {α : Type*} [decidable_eq α] {a : α} {s : finset α} :
  (insert a s).diag = insert (a, a) s.diag :=
by rw [insert_eq, insert_eq, union_diag, singleton_diag]

lemma insert_off_diag {α : Type*} [decidable_eq α] {a : α} {s : finset α} (has : a ∉ s) :
  (insert a s).off_diag = s.off_diag ∪ ({a} : finset α).product s ∪ s.product {a} :=
by rw [insert_eq, union_comm, union_off_diag (disjoint_singleton_right.2 has), singleton_off_diag,
  union_empty, union_right_comm]

@[to_additive] lemma prod_diag {α R : Type*} [decidable_eq α] [comm_monoid R]
  (s : finset α) (f : α → α → R) :
  ∏ i in s.diag, f i.1 i.2 = ∏ i in s, f i i :=
begin
  refine (finset.prod_bij (λ a _, (a, a)) (by simp) _ _ _).symm,
  { simp },
  { simp },
  simp only [mem_diag, exists_prop, and_imp, prod.forall, prod.mk.inj_iff],
  rintro i _ hi rfl,
  exact ⟨i, hi, rfl, rfl⟩,
end

lemma sum_sq {α R : Type*} [decidable_eq α] [comm_ring R] (s : finset α) (f : α → R) :
  (∑ i in s, f i) ^ 2 = ∑ i in s, f i ^ 2 + ∑ ij in s.off_diag, f ij.1 * f ij.2 :=
by simp_rw [sq, sum_mul, mul_sum, ←sum_product', ←diag_union_off_diag,
    sum_union (disjoint_diag_off_diag _), sum_diag s (λ i j, f i * f j)]

lemma exists_sol {ι α : Type*} [fintype ι] [decidable_eq α]
  (E : ι → finset α) (h : (univ.bUnion E).card < fintype.card ι) :
  ∃ x : ι → ℝ, (∃ i, x i ≠ 0) ∧ ∀ j ∈ univ.bUnion E, ∑ i, ite (j ∈ E i) (x i) 0 = 0 :=
begin
  haveI : decidable_eq ι := classical.dec_eq _,
  let M : matrix (univ.bUnion E) ι ℝ := λ j i, ite (↑j ∈ E i) 1 0,
  have : 0 < finrank ℝ M.to_lin'.ker,
  { rw [←add_lt_add_iff_left (finrank ℝ M.to_lin'.range), M.to_lin'.finrank_range_add_finrank_ker,
      finrank_fintype_fun_eq_card, add_zero],
    apply (M.rank_le_card_height.trans_eq _).trans_lt h,
    rw fintype.card_coe },
  rw finrank_pos_iff_exists_ne_zero at this,
  obtain ⟨⟨x, hMx⟩, hx₀⟩ := this,
  simp only [ne.def, submodule.mk_eq_zero, function.funext_iff, not_forall] at hx₀,
  refine ⟨x, hx₀, λ j hj, _⟩,
  simpa [M, matrix.mul_vec, matrix.dot_product] using congr_fun hMx ⟨j, hj⟩,
end

lemma fisher_fintype {ι α : Type*} [fintype ι] [decidable_eq α] (t : ℕ)
  (E : ι → finset α) (hE : ∀ i, t < (E i).card) (hE' : pairwise (λ i j, (E i ∩ E j).card = t)) :
  fintype.card ι ≤ (univ.bUnion E).card :=
begin
  haveI : decidable_eq ι := classical.dec_eq _,
  rcases eq_or_ne t 0 with rfl | ht,
  { simp only [card_eq_zero, ←disjoint_iff_inter_eq_empty] at hE',
    simp only [finset.card_pos] at hE,
    refine card_univ.symm.trans_le (card_le_card_bUnion _ (λ i _, hE i)),
    rwa [coe_univ, set.pairwise_disjoint, set.pairwise_univ] },
  have ht' : (t : ℝ) ≠ 0 := nat.cast_ne_zero.2 ht,
  by_contra' h,
  obtain ⟨x, ⟨i, hi⟩, hx₂⟩ := exists_sol E h,
  have h : (∑ i, x i) ^ 2 = ∑ i, x i ^ 2 +
    t⁻¹ * ∑ k in univ.bUnion E, ((∑ i, ite (k ∈ E i) (x i) 0) ^ 2 - ∑ i, ite (k ∈ E i) (x i) 0 ^ 2),
  { simp_rw [sum_sq, add_tsub_cancel_left, ite_mul, zero_mul, mul_ite, mul_zero, add_right_inj,
      ←ite_and, ←mem_inter, @sum_comm _ _ α, ←sum_filter, filter_mem_eq_inter, sum_const, mul_sum],
    refine sum_congr rfl (λ i hi, _),
    simp only [mem_off_diag, mem_univ, true_and] at hi,
    rw [(inter_eq_right_iff_subset _ _).2 _, hE' _ _ hi, nsmul_eq_mul, inv_mul_cancel_left₀],
    { simpa },
    exact (inter_subset_left _ _).trans (subset_bUnion_of_mem _ (mem_univ _)) },
  have h' : (∑ i, x i) ^ 2 = t⁻¹ * ∑ i, (t - (E i).card) * x i ^ 2,
  { simp_rw [h, sum_sub_distrib, mul_sum, ←mul_assoc, mul_sub, inv_mul_cancel ht', sub_mul, one_mul,
      sum_sub_distrib, sub_eq_add_neg, add_right_inj, @sum_comm _ ι, ite_pow, zero_pow zero_lt_two,
      ←sum_filter, sum_const, filter_mem_eq_inter, mul_assoc, ←mul_sum, sum_filter, nsmul_eq_mul,
      (inter_eq_right_iff_subset _ _).2 (subset_bUnion_of_mem _ (mem_univ _)), add_left_eq_self],
    rw [sum_congr rfl (λ j hj, _), sum_const_zero, mul_zero],
    rw [hx₂ _ hj, sq, mul_zero] },
  refine ((sq_nonneg (univ.sum x)).trans_eq h').not_lt (mul_neg_of_pos_of_neg _ _),
  { rwa [inv_pos, nat.cast_pos, pos_iff_ne_zero] },
  refine (finset.sum_lt_sum (λ i _, _) ⟨i, mem_univ _, _⟩).trans_eq sum_const_zero,
  { refine mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _),
    simpa using (hE _).le },
  exact mul_neg_of_neg_of_pos (by simpa using hE i) (by rwa sq_pos_iff),
end

lemma fisher {ι α : Type*} [decidable_eq α] (t : ℕ)
  (s : finset ι) (E : ι → finset α)
  (hE : ∀ i ∈ s, t < (E i).card) (hE' : (s : set ι).pairwise (λ i j, (E i ∩ E j).card = t)) :
  s.card ≤ (s.bUnion E).card :=
begin
  convert fisher_fintype t (λ i : {i // i ∈ s}, E i) (λ i, hE _ i.2) (λ i j t, _) using 1,
  { exact (fintype.card_coe _).symm },
  { rw [univ_eq_attach, ←sup_eq_bUnion s.attach, sup_attach, sup_eq_bUnion] },
  { exact hE' i.2 j.2 (mt subtype.eq t) },
end

lemma fisher_set_family {α : Type*} [decidable_eq α] (t : ℕ) (E : finset (finset α))
  (hE : ∀ i ∈ E, t < finset.card i)
  (hE' : (E : set (finset α)).pairwise (λ i j, (i ∩ j).card = t)) :
  E.card ≤ (E.bUnion id).card :=
fisher t E id hE hE'
