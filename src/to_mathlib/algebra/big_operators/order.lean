import algebra.big_operators.order

variables {ι R M : Type*} [ordered_comm_semiring R] [ordered_comm_monoid M]
  {f g : ι → R} {s t : finset ι}

open_locale big_operators

namespace finset

@[to_additive sum_le_sum_of_subset_of_nonpos]
lemma prod_le_prod_of_subset_of_le_one' {f : ι → M}
  (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → f i ≤ 1) :
  ∏ i in t, f i ≤ ∏ i in s, f i :=
by classical;
calc ∏ i in t, f i = ∏ i in t \ s ∪ s, f i    : by rw [sdiff_union_of_subset h]
  ... = (∏ i in t \ s, f i) * (∏ i in s, f i) : (prod_union sdiff_disjoint)
  ... ≤ ∏ i in s, f i                         : mul_le_of_le_one_left' $
    prod_le_one' $ by simpa only [mem_sdiff, and_imp]

lemma prod_anti_set_of_le_one {f : ι → M} (hf : ∀ b, f b ≤ 1) :
  antitone (λ s, ∏ b in s, f b) :=
λ _ _ hst, prod_le_prod_of_subset_of_le_one' hst (λ _ _ _, hf _)

lemma one_le_prod₀
  (h : ∀i ∈ s, 1 ≤ f i) : 1 ≤ (∏ i in s, f i) :=
prod_induction _ _ (λ _ _, one_le_mul_of_one_le_of_one_le) le_rfl h

lemma prod_le_prod_of_subset_of_one_le₀
  (h : s ⊆ t) (hs : 0 ≤ ∏ b in s, f b) (hf : ∀ b ∈ t, b ∉ s → 1 ≤ f b) :
  ∏ b in s, f b ≤ ∏ b in t, f b :=
by classical; calc (∏ i in s, f i) ≤ (∏ i in t \ s, f i) * (∏ i in s, f i) :
    le_mul_of_one_le_left hs $ one_le_prod₀ $ by simpa only [mem_sdiff, and_imp]
  ... = ∏ i in t \ s ∪ s, f i : (prod_union sdiff_disjoint).symm
  ... = ∏ i in t, f i         : by rw [sdiff_union_of_subset h]

lemma prod_le_prod_of_subset_of_le_one₀
  (h : s ⊆ t) (ht : ∀ i ∈ t, 0 ≤ f i) (hf : ∀ i ∈ t, i ∉ s → f i ≤ 1) :
  ∏ i in t, f i ≤ ∏ i in s, f i :=
by classical;
calc ∏ i in t, f i = ∏ i in t \ s ∪ s, f i    : by rw [sdiff_union_of_subset h]
  ... = (∏ i in t \ s, f i) * (∏ i in s, f i) : (prod_union sdiff_disjoint)
  ... ≤ ∏ i in s, f i                         : by
    { refine mul_le_of_le_one_left (prod_nonneg $ λ _ hb, ht _ (h hb)) (prod_le_one _ _),
      { simp [ht] { contextual := tt} },
      { simpa using hf } }

lemma prod_le_one₀
  (h : ∀i ∈ s, f i ≤ 1) (h' : ∀i ∈ s, 0 ≤ f i) : ∏ i in s, f i ≤ 1 :=
begin
  rw ←prod_empty,
  refine prod_le_prod_of_subset_of_le_one₀ (empty_subset _) h' (λ _ hb _, h _ hb)
end

lemma monotone_prod_of_one_le' (hf : ∀ b, 1 ≤ f b) :
  monotone (λ s, ∏ b in s, f b) :=
λ _ _ h, prod_le_prod_of_subset_of_one_le₀ h
  (prod_nonneg (λ b _, zero_le_one.trans (hf _))) (λ b _ _, hf b)

lemma antitone_prod_of_le_one' (hf : ∀ b, f b ≤ 1) (hf' : ∀ b, 0 ≤ f b) :
  antitone (λ s, ∏ b in s, f b) :=
λ _ _ h, prod_le_prod_of_subset_of_le_one₀ h (λ _ _, hf' _) (λ _ _ _, hf _)

lemma sum_le_prod_one_add_of_nonneg {R : Type*} [strict_ordered_comm_semiring R] {f : ι → R}
  (s : finset ι) (hf : ∀ b ∈ s, 0 ≤ f b) :
  ∑ i in s, f i ≤ ∏ a in s, (1 + f a) :=
begin
  classical,
  induction s using finset.cons_induction_on with a s ha IH,
  { simp },
  simp only [ha, add_mul, cons_eq_insert, sum_insert, not_false_iff, prod_insert, one_mul],
  rw [add_comm],
  refine add_le_add (IH (λ b hb, hf _ (mem_cons.mpr (or.inr hb)))) _,
  refine le_mul_of_one_le_right (hf _ (mem_cons_self _ _)) (one_le_prod₀ (λ b hb, _)),
  simp [hf _ (mem_cons.mpr (or.inr hb))]
end

lemma prod_le_prod_of_nonneg (s : finset ι)
  (h : ∀ b ∈ s, f b ≤ g b) (h' : ∀ b ∈ s, 0 ≤ f b) :
  ∏ i in s, f i ≤ ∏ i in s, g i :=
begin
  classical,
  induction s using finset.cons_induction_on with a s ha IH,
  { simp },
  simp only [ha, cons_eq_insert, prod_insert, not_false_iff],
  refine mul_le_mul (h _ (mem_cons_self _ _)) (IH _ _) (prod_nonneg _) ((h' _ _).trans (h _ _)),
  { intros b hb,
    exact h _ (mem_cons.mpr (or.inr hb)) },
  { intros b hb,
    exact h' _ (mem_cons.mpr (or.inr hb)) },
  { intros b hb,
    exact h' _ (mem_cons.mpr (or.inr hb)) },
  { simp },
  { simp }
end

end finset
