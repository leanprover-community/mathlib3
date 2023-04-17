import combinatorics.simple_graph.ramsey
import combinatorics.pigeonhole

namespace simple_graph

namespace product

open finset


def my_labelling (k l : ℕ) : top_edge_labelling (fin k × fin l) (fin 2) :=
top_edge_labelling.mk (λ x y h, if x.2 = y.2 then 0 else 1)
  (λ x y h, by simp only [@eq_comm (fin l)])

lemma is_ramsey_valid_my_labelling {k l : ℕ} : ¬ is_ramsey_valid (fin k × fin l) ![k + 1, l + 1] :=
begin
  rw [is_ramsey_valid_iff_eq],
  intros h,
  obtain ⟨m, hm⟩ := h (my_labelling _ _),
  simp only [fin.exists_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons] at hm,
  rcases hm with (⟨hm, hm'⟩ | ⟨hm, hm'⟩),
  { have h₁ : ∀ i ∈ m, prod.fst i ∈ (univ : finset (fin k)), { simp },
    have h₂ : (univ : finset (fin k)).card * 1 < m.card,
    { rw [mul_one, ←hm', card_fin],
      simp },
    obtain ⟨i, -, hi⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to h₁ h₂,
    simp only [one_lt_card_iff, mem_filter, prod.exists, and_assoc] at hi,
    obtain ⟨a, b, c, d, habm, rfl, hcdm, rfl, hi⟩ := hi,
    have := hm habm hcdm hi,
    simp only [my_labelling, top_edge_labelling.mk_get] at this,
    simp only [ne.def, prod.mk.inj_iff, eq_self_iff_true, true_and] at hi,
    simpa [if_neg hi] using this },
  { have h₁ : ∀ i ∈ m, prod.snd i ∈ (univ : finset (fin l)), { simp },
    have h₂ : (univ : finset (fin l)).card * 1 < m.card,
    { rw [mul_one, ←hm', card_fin],
      simp },
    obtain ⟨i, -, hi⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to h₁ h₂,
    simp only [one_lt_card_iff, mem_filter, prod.exists, and_assoc] at hi,
    obtain ⟨a, b, c, d, habm, rfl, hcdm, rfl, hi⟩ := hi,
    have := hm habm hcdm hi,
    simp only [my_labelling, top_edge_labelling.mk_get] at this,
    simp only [ne.def, prod.mk.inj_iff, eq_self_iff_true, true_and] at hi,
    simpa [if_neg hi] using this }
end

lemma ramsey_product_bound (k l : ℕ) : k * l < ramsey_number ![k + 1, l + 1] :=
begin
  have := @is_ramsey_valid_my_labelling k l,
  rwa [←ramsey_number_le_iff, fintype.card_prod, fintype.card_fin, fintype.card_fin, not_le] at this
end

def my_other_labelling (k l : ℕ) : top_edge_labelling (fin (k + 2) × fin l) (fin 2) :=
top_edge_labelling.mk
  (λ x y h,
    if x.1 = y.1 ∨
      ((⟦(x.1, y.1)⟧ : sym2 (fin (k + 2))) = ⟦(0, 1)⟧ ∧ x.2 = y.2) ∨
      ((⟦(x.1, y.1)⟧ : sym2 (fin (k + 2))) ≠ ⟦(0, 1)⟧ ∧ x.2 ≠ y.2)
    then 1
    else 0)
  begin
    intros x y h,
    refine if_congr _ rfl rfl,
    rw [sym2.eq_swap, ne.def y.2, @eq_comm _ y.1, @eq_comm _ y.2],
  end

def my_other_labelling' (α : Type*) [decidable_eq α] (l : ℕ) (a b : α) :
  top_edge_labelling (α × fin l) (fin 2) :=
top_edge_labelling.mk
  (λ x y h,
    if x.1 = y.1 ∨
      ((⟦(x.1, y.1)⟧ : sym2 α) = ⟦(a, b)⟧ ∧ x.2 = y.2) ∨
      ((⟦(x.1, y.1)⟧ : sym2 α) ≠ ⟦(a, b)⟧ ∧ x.2 ≠ y.2)
    then 1
    else 0)
  begin
    intros x y h,
    refine if_congr _ rfl rfl,
    rw [sym2.eq_swap, ne.def y.2, @eq_comm _ y.1, @eq_comm _ y.2],
  end

lemma my_other_labelling_swap' (α : Type*) [decidable_eq α] (l : ℕ) (a b : α) :
  my_other_labelling' α l a b = my_other_labelling' α l b a :=
begin
  refine top_edge_labelling.ext_get _,
  intros x y h,
  simp only [my_other_labelling', top_edge_labelling.mk_get],
  refine if_congr _ rfl rfl,
  rw @sym2.eq_swap _ a,
end

open_locale big_operators

lemma is_ramsey_valid_my_other_labelling'_zero {α : Type*} [fintype α] [decidable_eq α]
  {x y : α} {l : ℕ} {m : finset (α × fin l)} (z : α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
  ¬ ((my_other_labelling' α l x y).monochromatic_of m 0 ∧ fintype.card α = m.card) :=
begin
  rintro ⟨hm, hm'⟩,
  have : ∀ i ∈ (univ : finset α), (m.filter (λ x : _ × _, x.fst = i)).card ≤ 1,
  { rintro i -,
    rw card_le_one,
    simp only [mem_filter, and_imp, prod.forall],
    rintro a b hab rfl a' b' hab' rfl,
    by_contra',
    have := hm hab hab' this,
    rw [my_other_labelling', top_edge_labelling.mk_get] at this,
    simpa only [eq_self_iff_true, true_or, if_true, fin.one_eq_zero_iff,
      nat.succ_succ_ne_one] using this },
  have : ∀ i ∈ (univ : finset α), (filter (λ (x : _ × fin l), x.fst = i) m).card = 1,
  { rw [←sum_eq_sum_iff_of_le this, ←card_eq_sum_ones, card_univ, ←card_eq_sum_card_fiberwise,
      ←hm'],
    simp only [mem_univ, implies_true_iff] },
  have : ∀ i : α, ∃ (a : α × fin l), a ∈ m ∧ a.fst = i,
  { intros i,
    simp only [←exists_prop],
    rw [←filter_nonempty_iff, ←card_pos, this i (mem_univ _)],
    simp only [nat.lt_one_iff] },
  have h' : ∀ i : α, ∃ j : fin l, (i, j) ∈ m,
  { intros i,
    obtain ⟨⟨a, b⟩, c, rfl⟩ := this i,
    exact ⟨b, c⟩ },
  choose f hf using h',
  have h₁ : ∀ {x y : α}, x ≠ y →
    (my_other_labelling' α l x y).monochromatic_of m 0 → ∀ i, i ≠ x → f i = f y,
  { intros x y hxy hm i hi₁,
    by_contra',
    have : (i, f i) ≠ (y, f y),
    { rw [ne.def, prod.mk.inj_iff, not_and_distrib],
      exact or.inr this },
    have := hm (hf _) (hf _) this,
    rw [my_other_labelling', top_edge_labelling.mk_get, if_pos] at this,
    { simpa only [fin.one_eq_zero_iff, nat.succ_succ_ne_one] using this },
    refine or.inr (or.inr ⟨_, ‹_›⟩),
    dsimp,
    rw sym2.congr_left,
    exact hi₁ },
  have h₂ : ∀ i, i ≠ x → f i = f y,
  { exact h₁ hxy hm },
  have h₃ : ∀ i, i ≠ y → f i = f x,
  { refine h₁ hxy.symm _,
    rwa my_other_labelling_swap' },
  have h₄ : f x ≠ f y,
  { intro h',
    have : (x, f x) ≠ (y, f y),
    { simp only [hxy, ne.def, prod.mk.inj_iff, false_and, not_false_iff] },
    have := hm (hf _) (hf _) this,
    rw [my_other_labelling', top_edge_labelling.mk_get, if_pos] at this,
    { simpa only [fin.one_eq_zero_iff, nat.succ_succ_ne_one] using this },
    exact or.inr (or.inl ⟨rfl, h'⟩) },
  refine h₄ _,
  rw [←h₂ z hxz.symm, h₃ z hyz.symm],
end

lemma is_ramsey_valid_my_other_labelling_one {α : Type*} [decidable_eq α] [fintype α] {l : ℕ}
  {m : finset (α × fin l)} (x y : α) (h : x ≠ y) :
  ¬ ((my_other_labelling' α l x y).monochromatic_of m 1 ∧ l + 2 = m.card) :=
begin
  rintro ⟨hm, hm'⟩,
  let f' : α → finset (α × fin l) := λ i, m.filter (λ x, x.1 = i),
  -- let s₁₂ : finset α := {x}ᶜ,
  -- let s₀₂ : finset α := {y}ᶜ,
  have h₀ : ∀ x : α, ((({x}ᶜ : finset α).bUnion f').image prod.snd).card ≤ l,
  { intro x,
    refine (card_le_univ _).trans _,
    rw fintype.card_fin },
  have h₀' : ∀ x y, x ≠ y → (my_other_labelling' α l x y).monochromatic_of m 1 →
    set.inj_on prod.snd (({x}ᶜ : finset α).bUnion f' : set (α × fin l)),
  { intros x y hxy hm,
    simp only [set.inj_on, mem_coe, mem_bUnion, forall_exists_index, mem_compl, mem_singleton,
      prod.forall, mem_filter, and_imp],
    rintro a b _ ha hab rfl a' _ _ ha' hab' rfl rfl,
    by_contra',
    have h := hm hab hab' this,
    rw [my_other_labelling', top_edge_labelling.mk_get] at h,
    simp only [prod.mk.inj_iff, eq_self_iff_true, and_true] at this,
    simpa [this, ha, ha'] using h },
  have hx : ((({x}ᶜ : finset α).bUnion f').image prod.snd).card ≤ l := h₀ _,
  have hy : ((({y}ᶜ : finset α).bUnion f').image prod.snd).card ≤ l := h₀ _,
  rw card_image_of_inj_on (h₀' _ _ h hm) at hx,
  have hm_alt : (my_other_labelling' α l y x).monochromatic_of m 1,
  { rwa [my_other_labelling_swap'] },
  rw card_image_of_inj_on (h₀' _ _ h.symm hm_alt) at hy,
  have : ∀ i, f' i ∪ ({i}ᶜ : finset α).bUnion f' = m,
  { intros i,
    rw [←bUnion_insert, insert_compl_self, bUnion_filter_eq_of_maps_to],
    simp },
  suffices : m.card ≤ l + 1,
  { rw ←hm' at this,
    norm_num at this },
  cases le_or_lt (f' x).card 1 with hx' hx',
  { rw [←this x, union_comm],
    exact (card_union_le _ _).trans (add_le_add hx hx') },
  clear hm_alt,
  have f'y : f' y = ∅,
  { rw [one_lt_card] at hx',
    simp only [mem_filter, exists_prop, prod.exists, ne.def, not_and, and_assoc] at hx',
    obtain ⟨_, b, hxb, rfl, x, b', hxb', rfl, h'⟩ := hx',
    rw eq_empty_iff_forall_not_mem,
    simp only [prod.forall, mem_filter, not_and],
    rintro y b'' hab'' rfl,
    apply h',
    have : (x, b) ≠ (y, b''),
    { simp only [ne.def, prod.mk.inj_iff, h, false_and, not_false_iff] },
    have := hm hxb hab'' this,
    rw [my_other_labelling', top_edge_labelling.mk_get] at this,
    simp only [eq_self_iff_true, true_and, ne.def, not_true, false_and, or_false, ite_eq_left_iff,
      fin.zero_eq_one_iff, nat.succ_succ_ne_one, h, false_or, imp_false, not_not] at this,
    cases this,
    have : (x, b') ≠ (y, b),
    { simp only [ne.def, prod.mk.inj_iff, h, false_and, not_false_iff] },
    have := hm hxb' hab'' this,
    rw [my_other_labelling', top_edge_labelling.mk_get] at this,
    simp only [eq_self_iff_true, true_and, ne.def, not_true, false_and, or_false, ite_eq_left_iff,
      fin.zero_eq_one_iff, nat.succ_succ_ne_one, h, false_or, imp_false, not_not] at this,
    rw this },
  rw [←this y, f'y, empty_union],
  exact hy.trans (by simp),
end

lemma is_ramsey_valid_my_other_labelling {k l : ℕ} :
  ¬ is_ramsey_valid (fin (k + 3) × fin l) ![k + 3, l + 2] :=
begin
  rw [is_ramsey_valid_iff_eq],
  intros h,
  obtain ⟨m, hm⟩ := h (my_other_labelling' _ _ 0 1),
  simp only [fin.exists_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons] at hm,
  rcases hm with hm | hm,
  { have : (my_other_labelling' (fin (k + 3)) l 0 1).monochromatic_of m 0 ∧
      fintype.card (fin (k + 3)) = m.card,
    { simpa using hm },
    refine is_ramsey_valid_my_other_labelling'_zero (2 : fin (k + 3))
      _ _ _ this,
    dec_trivial,
    dec_trivial,
    dec_trivial },
  { refine is_ramsey_valid_my_other_labelling_one _ _ _ hm,
    dec_trivial },
end

lemma ramsey_product_bound' (k l : ℕ) : (k + 3) * l < ramsey_number ![k + 3, l + 2] :=
begin
  have := @is_ramsey_valid_my_other_labelling k l,
  rwa [←ramsey_number_le_iff, fintype.card_prod, fintype.card_fin, fintype.card_fin, not_le] at this
end

end product

lemma sub_one_mul_sub_one_lt_ramsey_number {k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) :
  (k - 1) * (l - 1) < ramsey_number ![k, l] :=
begin
  cases k,
  { simpa using hk },
  cases l,
  { simpa using hl },
  exact product.ramsey_product_bound k l,
end

lemma mul_sub_two_lt_ramsey_number {k l : ℕ} (hk : 3 ≤ k) (hl : l ≠ 0) :
  k * (l - 2) < ramsey_number ![k, l] :=
begin
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le' hk,
  cases l,
  { simpa using hl },
  cases l,
  { rw [nat.nat_zero_eq_zero, mul_zero, ramsey_number_pair_swap, ramsey_number_one_succ],
    simp },
  exact product.ramsey_product_bound' k l,
end

end simple_graph
