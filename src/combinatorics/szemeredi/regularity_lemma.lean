/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.special_functions.exp_log
import analysis.special_functions.pow
import combinatorics.choose.bounds
import combinatorics.simple_graph.basic
import order.iterate

/-!
# Szemerédi's Regularity Lemma

In this file, we define edge density, equipartitions, and prove Szemerédi's Regularity Lemma.
-/

universe u

open_locale big_operators
open finset fintype function

/-! ### Things that belong to mathlib -/

lemma prod_quotient_sym2_not_diag {α : Type u} [decidable_eq α] (s : finset α) :
  (finset.filter (λ (a : sym2 α), ¬a.is_diag) (finset.image quotient.mk (s.product s))).card =
    s.card.choose 2 :=
begin
  let ordered_pairs : finset (α × α) := (s.product s).filter (λ (x : α × α), ¬(x.1 = x.2)),
  have : ordered_pairs.card = s.card * (s.card - 1),
  { rw [nat.mul_sub_left_distrib, mul_one],
    change finset.card (finset.filter _ _) = _,
    rw [finset.filter_not, card_sdiff (filter_subset _ _), finset.card_product],
    congr' 1,
    refine finset.card_congr (λ (x : _ × _) _, x.1) _ _ _,
    { rintro ⟨x, y⟩ h,
      simp only [mem_filter, mem_product] at h,
      apply h.1.1 },
    { simp only [true_and, prod.forall, mem_filter, mem_product],
      rintro a b ⟨x, y⟩ ⟨⟨_, _⟩, rfl⟩ ⟨_, rfl : x = y⟩ (rfl : a = x),
      refl },
    { simp only [exists_prop, mem_filter, imp_self, exists_and_distrib_right, implies_true_iff,
        exists_eq_right, exists_eq_right', and_self, prod.exists, mem_product] } },
  rw [nat.choose_two_right, ←this],
  symmetry,
  apply nat.div_eq_of_eq_mul_right (show 0 < 2, by norm_num),
  have : ∀ x ∈ ordered_pairs,
    quotient.mk x ∈ ((s.product s).image quotient.mk).filter (λ (a : sym2 α), ¬a.is_diag),
  { rintro ⟨x, y⟩ hx,
    simp only [mem_image, exists_prop, mem_filter, sym2.is_diag_iff_proj_eq, sym2.eq_iff,
      prod.exists, mem_product],
    simp only [mem_filter, mem_product] at hx,
    refine ⟨⟨_, _, hx.1, or.inl ⟨rfl, rfl⟩⟩, hx.2⟩ },
  rw [card_eq_sum_card_fiberwise this, finset.sum_const_nat, mul_comm],
  refine quotient.ind _,
  rintro ⟨x, y⟩ hxy,
  simp only [mem_image, exists_prop, mem_filter, sym2.is_diag_iff_proj_eq, sym2.eq_iff,
    prod.exists, mem_product] at hxy,
  have : x ∈ s ∧ y ∈ s,
  { rcases hxy with ⟨⟨x, y, ⟨_, _⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, _⟩;
    refine ⟨‹_›, ‹_›⟩ },
  have : filter (λ (z : α × α), ⟦z⟧ = ⟦(x, y)⟧) ordered_pairs = ({(x,y), (y,x)} : finset _),
  { ext ⟨x₁, y₁⟩,
    simp only [true_and, mem_filter, mem_insert, mem_product, mem_singleton, sym2.eq_iff,
      and_iff_right_iff_imp, prod.mk.inj_iff],
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩),
    { refine ⟨‹_›, hxy.2⟩, },
    refine ⟨⟨this.2, this.1⟩, ne.symm hxy.2⟩ },
  rw [this, card_insert_of_not_mem, card_singleton],
  simp only [not_and, prod.mk.inj_iff, mem_singleton],
  rintro rfl,
  exact hxy.2
end

lemma card_sym2_not_diag {α : Type u} [decidable_eq α] [fintype α] :
  (univ.filter (λ (a : sym2 α), ¬a.is_diag)).card = (card α).choose 2 :=
prod_quotient_sym2_not_diag (univ : finset α)

lemma sym2.injective {α : Type u} : function.injective (sym2.diag : α → sym2 α) :=
begin
  rintro x y (h : ⟦_⟧ = ⟦_⟧),
  rw sym2.eq_iff at h,
  simpa using h
end

lemma card_sym2 {α : Type u} [decidable_eq α] [fintype α] :
  card (sym2 α) = card α * (card α + 1) / 2 :=
begin
  have : univ.filter (λ (x : sym2 α), x.is_diag) = univ.image sym2.diag,
  { ext,
    simp [sym2.is_diag] },
  rw [←finset.card_univ, ←filter_union_filter_neg_eq sym2.is_diag (univ : finset (sym2 α)),
    card_disjoint_union, this, card_image_of_injective _ sym2.injective, card_sym2_not_diag,
    nat.choose_two_right, finset.card_univ, add_comm, ←nat.triangle_succ, nat.succ_sub_one,
    mul_comm],
  rw disjoint_iff_inter_eq_empty,
  apply filter_inter_filter_neg_eq,
end

lemma between_nat_iff {a t : ℕ} :
  (a = t ∨ a = t+1) ↔ (t ≤ a ∧ a ≤ t+1) :=
begin
  split,
  { rintro (rfl | rfl);
    simp },
  rintro ⟨h₁, h₂⟩,
  obtain h | h := h₁.eq_or_lt,
  { exact or.inl h.symm },
  exact or.inr (le_antisymm h₂ (nat.succ_le_of_lt h)),
end

namespace real

lemma le_exp_iff_log_le {a b : ℝ} (ha : 0 < a) :
  log a ≤ b ↔ a ≤ exp b :=
by rw [←exp_le_exp, exp_log ha]

end real

lemma sum_mul_sq_le_sq_mul_sq {α : Type*} (s : finset α) (f g : α → ℝ) :
  (∑ i in s, f i * g i)^2 ≤ (∑ i in s, (f i)^2) * (∑ i in s, (g i)^2) :=
begin
  have : 0 ≤ ∑ i in s, (g i)^2 := sum_nonneg (λ i hi, sq_nonneg _),
  cases eq_or_lt_of_le this with h h,
  { rw [eq_comm, sum_eq_zero_iff_of_nonneg] at h,
    { simp only [nat.succ_pos', pow_eq_zero_iff] at h,
      rw [finset.sum_congr rfl (show ∀ i ∈ s, f i * g i = 0, from λ i hi, by simp [h i hi]),
          finset.sum_congr rfl (show ∀ i ∈ s, g i ^ 2 = 0, from λ i hi, by simp [h i hi])],
      simp },
    { intros i hi,
      apply sq_nonneg } },
  let lambda := (∑ i in s, f i * g i) / (∑ i in s, (g i)^2),
  have : 0 ≤ ∑ i in s, (f i - lambda * g i)^2,
  { apply sum_nonneg,
    intros i hi,
    apply sq_nonneg },
  simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib, mul_pow, mul_assoc, ←mul_sum,
    mul_left_comm _ lambda, ←mul_sum, div_pow, div_mul_eq_mul_div, ←sq, ←div_mul_eq_mul_div,
    div_mul_eq_mul_div_comm, sq (∑ i in s, g i ^ 2), div_self_mul_self', ←div_eq_mul_inv, two_mul,
    ←sub_sub, sub_add_cancel, sub_nonneg] at this,
  rw div_le_iff h at this,
  assumption
end

lemma bUnion_subset_of_forall_subset {α β : Type*} [decidable_eq β]
  {s : finset α} (t : finset β) (f : α → finset β) (h : ∀ x ∈ s, f x ⊆ t) : s.bUnion f ⊆ t :=
begin
  intros i hi,
  simp only [mem_bUnion, exists_prop] at hi,
  obtain ⟨a, ha₁, ha₂⟩ := hi,
  exact h _ ha₁ ha₂,
end

lemma sdiff_ssubset {α : Type*} [decidable_eq α] {x y : finset α} (hx : y ⊆ x) (hy : y.nonempty) :
  x \ y ⊂ x :=
begin
  obtain ⟨i, hi⟩ := hy,
  rw ssubset_iff_of_subset (sdiff_subset _ _),
  exact ⟨i, hx hi, λ t, (mem_sdiff.1 t).2 hi⟩,
end

lemma lt_div_mul_add {a b : ℕ} (hb : 0 < b) : a < a/b*b + b :=
begin
  rw [←nat.succ_mul, ←nat.div_lt_iff_lt_mul _ _ hb],
  exact nat.lt_succ_self _,
end

namespace finset
variables {α : Type*}
  [decidable_pred (λ (ab : α × α), well_ordering_rel ab.fst ab.snd)]

/-- Pairs of parts. We exclude the diagonal, as these do not make sense nor
behave well in the context of Szemerédi's Regularity Lemma. -/
def distinct_pairs (s : finset α) :
  finset (α × α) :=
(s.product s).filter (λ ab, well_ordering_rel ab.1 ab.2)

variable {s : finset α}

lemma mem_distinct_pairs (a b : α) :
  (a, b) ∈ s.distinct_pairs ↔ a ∈ s ∧ b ∈ s ∧ well_ordering_rel a b :=
by rw [distinct_pairs, mem_filter, mem_product, and_assoc]

lemma distinct_pairs_card [decidable_eq α] :
  s.distinct_pairs.card = s.card.choose 2 :=
begin
  let ordered_pairs : finset (α × α) := (s.product s).filter (λ (x : α × α), ¬(x.1 = x.2)),
  have : ordered_pairs.card = s.card * (s.card - 1),
  { rw [nat.mul_sub_left_distrib, mul_one],
    change finset.card (finset.filter _ _) = _,
    rw [finset.filter_not, card_sdiff (filter_subset _ _), finset.card_product],
    congr' 1,
    refine finset.card_congr (λ (x : _ × _) _, x.1) _ _ _,
    { rintro ⟨x, y⟩ h,
      simp only [mem_filter, mem_product] at h,
      apply h.1.1 },
    { simp only [true_and, prod.forall, mem_filter, mem_product],
      rintro a b ⟨x, y⟩ ⟨⟨_, _⟩, rfl⟩ ⟨_, rfl : x = y⟩ (rfl : a = x),
      refl },
    { simp only [exists_prop, mem_filter, imp_self, exists_and_distrib_right, implies_true_iff,
        exists_eq_right, exists_eq_right', and_self, prod.exists, mem_product] } },
  rw [nat.choose_two_right, ←this],
  symmetry,
  apply nat.div_eq_of_eq_mul_right (show 0 < 2, by norm_num),
  have : ∀ x ∈ ordered_pairs,
    quotient.mk x ∈ ((s.product s).image quotient.mk).filter (λ (a : sym2 α), ¬a.is_diag),
  { rintro ⟨x, y⟩ hx,
    simp only [mem_image, exists_prop, mem_filter, sym2.is_diag_iff_proj_eq, sym2.eq_iff,
      prod.exists, mem_product],
    simp only [mem_filter, mem_product] at hx,
    refine ⟨⟨_, _, hx.1, or.inl ⟨rfl, rfl⟩⟩, hx.2⟩ },
  sorry
  /-
  rw [card_eq_sum_card_fiberwise, finset.sum_const_nat, mul_comm],
  rintro ⟨x, y⟩ hxy,
  simp only [mem_image, exists_prop, mem_filter, sym2.is_diag_iff_proj_eq, sym2.eq_iff,
    prod.exists, mem_product] at hxy,
  have : x ∈ s ∧ y ∈ s,
  { rcases hxy with ⟨⟨x, y, ⟨_, _⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, _⟩;
    refine ⟨‹_›, ‹_›⟩ },
  have : filter (λ (z : α × α), ⟦z⟧ = ⟦(x, y)⟧) ordered_pairs = ({(x,y), (y,x)} : finset _),
  { ext ⟨x₁, y₁⟩,
    simp only [true_and, mem_filter, mem_insert, mem_product, mem_singleton, sym2.eq_iff,
      and_iff_right_iff_imp, prod.mk.inj_iff],
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩),
    { refine ⟨‹_›, hxy.2⟩, },
    refine ⟨⟨this.2, this.1⟩, ne.symm hxy.2⟩ },
  rw [this, card_insert_of_not_mem, card_singleton],
  simp only [not_and, prod.mk.inj_iff, mem_singleton],
  rintro rfl,
  exact hxy.2-/
end

end finset

open finset

/-! ### Prerequisites for SRL -/.

lemma lemmaB {α : Type*} {s t : finset α} (hst : s ⊆ t) (f : α → ℝ) {a b : ℝ}
  (hs : (∑ x in s, f x)/s.card = a + b) (ht : (∑ x in t, f x) / t.card = a) :
  a^2 + s.card/t.card * b^2 ≤ (∑ x in t, f x^2)/t.card :=
begin
  obtain htcard | htcard := (t.card.cast_nonneg : (0 : ℝ) ≤ t.card).eq_or_lt,
  { rw [←ht, ←htcard, div_zero, div_zero, div_zero, zero_mul, add_zero, pow_succ, zero_mul] },
  obtain hscard | hscard := (s.card.cast_nonneg : (0 : ℝ) ≤ s.card).eq_or_lt,
  { rw [←hscard, zero_div, zero_mul, add_zero, ←ht, le_div_iff htcard, div_pow, sq (t.card : ℝ),
      div_mul_eq_mul_div_comm, div_self_mul_self', mul_inv_le_iff htcard],
    simpa using sum_mul_sq_le_sq_mul_sq t (λ _, 1) f },
  have htzero : (t.card : ℝ) ≠ 0 := htcard.ne.symm,
  have hszero : (s.card : ℝ) ≠ 0 := hscard.ne.symm,
  rw div_eq_iff htzero at ht,
  rw div_eq_iff hszero at hs,
  suffices h : (∑ x in s, (f x - a))^2 ≤ s.card * (∑ x in t, (f x - a)^2),
  { apply le_of_mul_le_mul_left _ htcard,
    rw [mul_add, ←mul_assoc, mul_div_cancel' _ htzero, mul_div_cancel' _ htzero,
      ←le_sub_iff_add_le'],
    apply le_of_mul_le_mul_left _ hscard,
    rw [←mul_assoc, ←sq],
    simp_rw sub_sq at h,
    rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ←sum_mul, ←mul_sum, sum_const,
      sum_const, ht, hs, nsmul_eq_mul, nsmul_eq_mul, mul_comm (a + b), ←mul_sub, add_sub_cancel',
    mul_pow] at h,
    convert h,
    ring },
  have cs := sum_mul_sq_le_sq_mul_sq s (λ _, 1) (λ x, f x - a),
  simp only [one_pow, one_mul, nsmul_eq_mul, sum_const, nat.smul_one_eq_coe] at cs,
  apply cs.trans _,
  rw mul_le_mul_left hscard,
  exact sum_le_sum_of_subset_of_nonneg hst (λ i _ _, sq_nonneg _),
end

/-- A set is equitable if no element value is more than one bigger than another. -/
def equitable_on {α : Type*} (s : set α) (f : α → ℕ) : Prop :=
  ∀ ⦃a₁ a₂⦄, a₁ ∈ s → a₂ ∈ s → f a₁ ≤ f a₂ → f a₂ - f a₁ ≤ 1

@[simp]
lemma equitable_on_empty {α : Type*} (f : α → ℕ) :
  equitable_on ∅ f :=
by simp [equitable_on]

lemma equitable_on_iff {α : Type*} (s : set α) (f : α → ℕ) :
  equitable_on s f ↔ ∀ ⦃a₁ a₂⦄, a₁ ∈ s → a₂ ∈ s → f a₂ - f a₁ ≤ 1 :=
begin
  split,
  { intros hf a₁ a₂ ha₁ ha₂,
    cases le_total (f a₁) (f a₂),
    { apply hf ha₁ ha₂ h },
    rw nat.sub_eq_zero_of_le h,
    apply zero_le_one },
  intros hf a₁ a₂ ha₁ ha₂ _,
  apply hf ha₁ ha₂
end

lemma equitable_on_iff_almost_eq_constant {α : Type*} (s : set α) (f : α → ℕ) :
  equitable_on s f ↔ ∃ b, ∀ a ∈ s, f a = b ∨ f a = b + 1 :=
begin
  classical,
  split,
  { rw equitable_on_iff,
    rcases s.eq_empty_or_nonempty with rfl | hs,
    { simp },
    { intros h,
      refine ⟨nat.find (set.nonempty.image f hs), _⟩,
      obtain ⟨w, hw₁, hw₂⟩ := nat.find_spec (set.nonempty.image f hs),
      intros a ha,
      have : nat.find (set.nonempty.image f hs) ≤ f a := nat.find_min' _ ⟨_, ha, rfl⟩,
      cases eq_or_lt_of_le this with q q,
      { exact or.inl q.symm },
      { refine or.inr (le_antisymm _ (nat.succ_le_of_lt q)),
        rw [←hw₂, ←nat.sub_le_left_iff_le_add],
        apply h hw₁ ha } } },
  { rintro ⟨b, hb⟩ x₁ x₂ hx₁ hx₂ h,
    rcases hb x₁ hx₁ with rfl | hx₁';
    cases hb x₂ hx₂ with hx₂' hx₂',
    { simp [hx₂'] },
    { simp [hx₂'] },
    { simpa [hx₁', hx₂'] using h },
    { simp [hx₁', hx₂'] } }
end

lemma equitable_on_finset_iff_eq_average {α : Type*} (s : finset α) (f : α → ℕ) :
  equitable_on (s : set α) f ↔
    ∀ a ∈ s, f a = (∑ i in s, f i) / s.card ∨ f a = (∑ i in s, f i) / s.card + 1 :=
begin
  rw equitable_on_iff_almost_eq_constant,
  refine ⟨_, λ h, ⟨_, h⟩ ⟩,
  rintro ⟨b, hb⟩,
  by_cases h : ∀ a ∈ s, f a = b+1,
  { clear hb,
    intros a ha,
    left,
    symmetry,
    apply nat.div_eq_of_eq_mul_left (finset.card_pos.2 ⟨_, ha⟩),
    rw [mul_comm, sum_const_nat],
    intros c hc,
    rw [h _ ha, h _ hc] },
  suffices : b = (∑ i in s, f i) / s.card,
  { simp_rw [←this],
    apply hb },
  simp_rw between_nat_iff at hb,
  symmetry,
  apply nat.div_eq_of_lt_le,
  { apply le_trans _ (sum_le_sum (λ a ha, (hb a ha).1)),
    simp [mul_comm] },
  push_neg at h,
  rcases h with ⟨x, hx₁, hx₂⟩,
  apply (sum_lt_sum (λ a ha, (hb a ha).2) ⟨_, hx₁, lt_of_le_of_ne (hb _ hx₁).2 hx₂⟩).trans_le,
  rw [mul_comm, sum_const_nat],
  simp,
end

lemma equitable_on_finset_iff {α : Type*} (s : finset α) (f : α → ℕ) :
  equitable_on (s : set α) f ↔
    ∀ a ∈ s, (∑ i in s, f i) / s.card ≤ f a ∧ f a ≤ (∑ i in s, f i) / s.card + 1 :=
begin
  rw equitable_on_finset_iff_eq_average,
  simp_rw [between_nat_iff],
end

namespace relation
variables {V : Type u} [decidable_eq V] (r : V → V → Prop) [decidable_rel r]

/-- Finset of edges between two finsets of vertices -/
def pairs_finset (U W : finset V) : finset (V × V) :=
(U.product W).filter (λ e, r e.1 e.2)

lemma mem_pairs_finset (U W : finset V) (x : V × V) :
  x ∈ pairs_finset r U W ↔ x.1 ∈ U ∧ x.2 ∈ W ∧ r x.1 x.2 :=
by simp only [pairs_finset, and_assoc, mem_filter, finset.mem_product]

lemma mem_pairs_finset' (U W : finset V) (x y : V) :
  (x, y) ∈ pairs_finset r U W ↔ x ∈ U ∧ y ∈ W ∧ r x y :=
mem_pairs_finset _ _ _ _

lemma pairs_finset_empty_left (W : finset V) :
  pairs_finset r ∅ W = ∅ :=
by rw [pairs_finset, finset.empty_product, filter_empty]

lemma pairs_finset_mono {A B A' B' : finset V} (hA : A' ⊆ A) (hB : B' ⊆ B) :
  pairs_finset r A' B' ⊆ pairs_finset r A B :=
begin
  intro x,
  rw [mem_pairs_finset, mem_pairs_finset],
  exact λ h, ⟨hA h.1, hB h.2.1, h.2.2⟩,
end

lemma card_pairs_finset_compl (U W : finset V) :
  (pairs_finset r U W).card + (pairs_finset (λ x y, ¬r x y) U W).card = U.card * W.card :=
begin
  rw [←finset.card_product, pairs_finset, pairs_finset, ←finset.card_union_eq,
    finset.filter_union_filter_neg_eq],
  rw finset.disjoint_filter,
  exact λ x _, not_not.2,
end

/-- Edge density between two finsets of vertices -/
noncomputable def pairs_density (U W : finset V) : ℝ :=
(pairs_finset r U W).card / (U.card * W.card)

lemma pairs_density_nonneg (U W : finset V) :
  0 ≤ pairs_density r U W :=
begin
  apply div_nonneg;
  exact_mod_cast nat.zero_le _,
end

lemma pairs_density_le_one (U W : finset V) :
  pairs_density r U W ≤ 1 :=
begin
  refine div_le_one_of_le _ (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)),
  norm_cast,
  rw [pairs_finset, ←finset.card_product],
  exact finset.card_filter_le _ _,
end

lemma pairs_density_compl {U W : finset V} (hU : U.nonempty) (hW : W.nonempty) :
  pairs_density r U W + pairs_density (λ x y, ¬r x y) U W = 1 :=
begin
  have h : ((U.card * W.card : ℕ) : ℝ) ≠ 0 := nat.cast_ne_zero.2 (mul_pos (finset.card_pos.2 hU)
    (finset.card_pos.2 hW)).ne.symm,
  rw [pairs_density, pairs_density, div_add_div_same, ←nat.cast_mul, div_eq_iff h, one_mul],
  exact_mod_cast card_pairs_finset_compl r U W,
end

lemma pairs_density_empty_left (W : finset V) :
  pairs_density r ∅ W = 0 :=
by rw [pairs_density, finset.card_empty, nat.cast_zero, zero_mul, div_zero]

lemma pairs_density_empty_right (U : finset V) :
  pairs_density r U ∅ = 0 :=
by rw [pairs_density, finset.card_empty, nat.cast_zero, mul_zero, div_zero]

section symmetric
variables {r} (hr : symmetric r)
include hr

lemma mem_pairs_finset_comm (U W : finset V) (x y : V) :
  (x, y) ∈ pairs_finset r U W ↔ (y, x) ∈ pairs_finset r W U :=
begin
  rw [mem_pairs_finset', mem_pairs_finset'],
  split; exact λ h, ⟨h.2.1, h.1, hr h.2.2⟩,
end

lemma pairs_count_comm (U W : finset V) :
  (pairs_finset r U W).card = (pairs_finset r W U).card :=
begin
  apply finset.card_congr (λ (i : V × V) hi, (i.2, i.1)) _ _ _,
  { rintro ⟨i, j⟩ h,
    rw mem_pairs_finset_comm hr,
    exact h },
  { rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h₁ h₂ h,
    rcases h,
    refl },
  rintro ⟨i, j⟩ h,
  refine ⟨⟨j, i⟩, _, rfl⟩,
  rw mem_pairs_finset_comm hr,
  exact h,
end

lemma pairs_density_comm (U W : finset V) : pairs_density r U W = pairs_density r W U :=
by rw [pairs_density, mul_comm, pairs_count_comm hr, pairs_density]

end symmetric

lemma aux₀ {A B A' B' : finset V} (hA : A' ⊆ A) (hB : B' ⊆ B) :
 (A'.card : ℝ)/A.card * (B'.card/B.card) * pairs_density r A' B' ≤ pairs_density r A B :=
begin
  obtain hA' | hA' := nat.eq_zero_or_pos A'.card,
  { rw [hA', nat.cast_zero, zero_div, zero_mul, zero_mul],
    exact pairs_density_nonneg r A B },
  obtain hB' | hB' := nat.eq_zero_or_pos B'.card,
  { rw [hB', nat.cast_zero, zero_div, mul_zero, zero_mul],
    exact pairs_density_nonneg r A B },
  have hAB' : (0 : ℝ) < A'.card * B'.card := by exact_mod_cast mul_pos hA' hB',
  have hAB : (0 : ℝ) < A.card * B.card := by exact_mod_cast mul_pos (hA'.trans_le
    (finset.card_le_of_subset hA)) (hB'.trans_le (finset.card_le_of_subset hB)),
  rw [pairs_density, pairs_density, div_mul_div, mul_comm, div_mul_div_cancel _ hAB'.ne.symm,
    div_le_div_right hAB, nat.cast_le],
  exact finset.card_le_of_subset (pairs_finset_mono r hA hB),
end

lemma aux₁ {A B A' B' : finset V} (hA : A' ⊆ A) (hB : B' ⊆ B) :
  pairs_density r A' B' - pairs_density r A B ≤ 1 - (A'.card : ℝ)/A.card * (B'.card/B.card) :=
calc
  pairs_density r A' B' - pairs_density r A B
      ≤ pairs_density r A' B' - A'.card/A.card * (B'.card/B.card) * pairs_density r A' B'
      : sub_le_sub_left (aux₀ r hA hB) _
  ... = (1 - A'.card/A.card * (B'.card/B.card)) * pairs_density r A' B'
      : by rw [sub_mul, one_mul]
  ... ≤ 1 - A'.card/A.card * (B'.card/B.card)
      : begin
          convert mul_le_mul_of_nonneg_left (pairs_density_le_one r _ _) _,
          { rw mul_one },
          apply sub_nonneg_of_le,
          apply mul_le_one, swap,
          apply div_nonneg,
          exact nat.cast_nonneg _,
          exact nat.cast_nonneg _,
          apply div_le_one_of_le,
          rw nat.cast_le,
          exact finset.card_le_of_subset hA,
          exact nat.cast_nonneg _,
          apply div_le_one_of_le,
          rw nat.cast_le,
          exact finset.card_le_of_subset hB,
          exact nat.cast_nonneg _,
        end

lemma aux₂ {A B A' B' : finset V} (hA : A' ⊆ A) (hB : B' ⊆ B) :
  abs (pairs_density r A' B' - pairs_density r A B) ≤ 1 - (A'.card : ℝ)/A.card * (B'.card/B.card) :=
begin
  have habs : abs (pairs_density r A' B' - pairs_density r A B) ≤ 1,
  { rw [abs_sub_le_iff, ←sub_zero (1 : ℝ)],
    split; exact sub_le_sub (pairs_density_le_one r _ _) (pairs_density_nonneg r _ _) },
  obtain hA' | hA' := nat.eq_zero_or_pos A'.card,
  { rw [hA', nat.cast_zero, zero_div, zero_mul, sub_zero],
    exact habs },
  obtain hB' | hB' := nat.eq_zero_or_pos B'.card,
  { rw [hB', nat.cast_zero, zero_div, mul_zero, sub_zero],
    exact habs },
  rw finset.card_pos at hA' hB',
  refine abs_sub_le_iff.2 ⟨aux₁ r hA hB, _⟩,
  rw [←add_sub_cancel (pairs_density r A B) (pairs_density (λ x y, ¬r x y) A B),
    ←add_sub_cancel (pairs_density r A' B') (pairs_density (λ x y, ¬r x y) A' B'),
    pairs_density_compl _ (hA'.mono hA) (hB'.mono hB), pairs_density_compl _ hA' hB',
    sub_sub_sub_cancel_left],
  exact aux₁ _ hA hB,
end

lemma aux₃ {A B A' B' : finset V} (hA : A' ⊆ A) (hB : B' ⊆ B) {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
  (hAcard : (1 - δ) * A.card ≤ A'.card) (hBcard : (1 - δ) * B.card ≤ B'.card) :
  abs (pairs_density r A' B' - pairs_density r A B) ≤ 2*δ - δ^2 :=
begin
  have hδ' : 0 ≤ 2 * δ - δ ^ 2,
  { rw [sub_nonneg, sq],
    refine mul_le_mul_of_nonneg_right (hδ₁.le.trans _) hδ₀,
    norm_num },
  rw ←sub_pos at hδ₁,
  obtain hA' | hA'pos := (nat.cast_nonneg A'.card).eq_or_lt,
  { rw ←hA' at hAcard,
    rwa [pairs_density, pairs_density, ←hA', (nonpos_of_mul_nonpos_left hAcard hδ₁).antisymm
      (nat.cast_nonneg _), zero_mul, zero_mul, div_zero, div_zero, sub_zero, abs_zero] },
  obtain hB' | hB'pos := (nat.cast_nonneg B'.card).eq_or_lt,
  { rw ←hB' at hBcard,
    rwa [pairs_density, pairs_density, ←hB', (nonpos_of_mul_nonpos_left hBcard hδ₁).antisymm
      (nat.cast_nonneg _), mul_zero, mul_zero, div_zero, div_zero, sub_zero, abs_zero] },
  have hApos : (0 : ℝ) < A.card := hA'pos.trans_le (nat.cast_le.2 (finset.card_le_of_subset hA)),
  have hBpos : (0 : ℝ) < B.card := hB'pos.trans_le (nat.cast_le.2 (finset.card_le_of_subset hB)),
  calc
    abs (pairs_density r A' B' - pairs_density r A B)
        ≤ 1 - A'.card/A.card * (B'.card/B.card)
        : aux₂ r hA hB
    ... ≤ 1 - (1 - δ) * (1 - δ)
        : sub_le_sub_left (mul_le_mul ((le_div_iff hApos).2 hAcard) ((le_div_iff hBpos).2
            hBcard) hδ₁.le (div_nonneg hA'pos.le hApos.le)) 1
    ... = 2*δ - δ^2
        : by ring,
end

lemma LemmaA {A B A' B' : finset V} (hA : A' ⊆ A) (hB : B' ⊆ B) {δ : ℝ} (hδ : 0 ≤ δ)
  (hAcard : (1 - δ) * A.card ≤ A'.card) (hBcard : (1 - δ) * B.card ≤ B'.card) :
  abs (pairs_density r A' B' - pairs_density r A B) ≤ 2 * δ :=
begin
  cases le_or_lt 1 δ,
  { apply (abs_sub _ _).trans,
    rw [abs_of_nonneg (pairs_density_nonneg r _ _), abs_of_nonneg (pairs_density_nonneg r A B),
      two_mul],
    exact add_le_add ((pairs_density_le_one r _ _).trans h)
      ((pairs_density_le_one r A B).trans h) },
  exact (aux₃ r hA hB hδ h hAcard hBcard).trans ((sub_le_self_iff _).2 (sq_nonneg δ)),
end

end relation

open relation

namespace simple_graph
variables {V : Type u} [decidable_eq V] (G : simple_graph V) [decidable_rel G.adj]

/- Remnants of what's now under `relation`. The only point for keeping it is to sometimes avoid
writing `G.adj` and `G.sym` sometimes. -/
/-- Edge density between two finsets of vertices -/
noncomputable def edge_density : finset V → finset V → ℝ :=
pairs_density G.adj

lemma edge_density_comm (U W : finset V) : G.edge_density U W = G.edge_density W U :=
pairs_density_comm G.sym U W

lemma edge_density_nonneg (U W : finset V) :
  0 ≤ G.edge_density U W :=
pairs_density_nonneg _ U W

lemma edge_density_le_one (U W : finset V) :
  G.edge_density U W ≤ 1 :=
pairs_density_le_one _ U W

/-- A pair of finsets of vertices is ε-uniform iff their edge density is close to the density of any
big enough pair of subsets. Intuitively, the edges between them are random-like. -/
def is_uniform (ε : ℝ) (U W : finset V) : Prop :=
∀ U', U' ⊆ U → ∀ W', W' ⊆ W → ε * U.card ≤ U'.card → ε * W.card ≤ W'.card →
abs (edge_density G U' W' - edge_density G U W) < ε

/-- If the pair `(U, W)` is `ε`-uniform and `ε ≤ ε'`, then it is `ε'`-uniform. -/
lemma is_uniform_mono {ε ε' : ℝ} {U W : finset V} (h : ε ≤ ε') (hε : is_uniform G ε U W) :
  is_uniform G ε' U W :=
begin
  intros U' hU' W' hW' hU hW,
  apply (hε _ hU' _ hW' (le_trans _ hU) (le_trans _ hW)).trans_le h;
  apply mul_le_mul_of_nonneg_right h (nat.cast_nonneg _),
end

lemma is_uniform_symmetric (ε : ℝ) : symmetric (is_uniform G ε) :=
begin
  intros U W h W' hW' U' hU' hW hU,
  rw edge_density_comm _ W',
  rw edge_density_comm _ W,
  apply h _ hU' _ hW' hU hW,
end

open_locale classical

/- Extracts a witness of the non-uniformity of `(U, W)`. It uses an arbitrary ordering of
`finset V` -/
noncomputable def witness_aux (ε : ℝ) (U W : finset V) : finset V × finset V :=
dite (U = W ∨ G.is_uniform ε U W) (λ _, (U, W)) (λ h, begin
    unfold is_uniform at h,
    push_neg at h,
    exact (classical.some h.2, classical.some (classical.some_spec h.2).2),
  end)

/- Extracts a witness of the non-uniformity of `(U, W)`. It uses an arbitrary ordering of
`finset V` (`well_ordering_rel`) to ensure that the witnesses of `(U, W)` and `(W, U)` are related
(the existentials don't ensure we would take the same from `¬G.is_uniform ε U W` and
`¬G.is_uniform ε W U`). -/
noncomputable def witness (ε : ℝ) (U W : finset V) : finset V × finset V :=
ite (well_ordering_rel U W) (G.witness_aux ε U W) (G.witness_aux ε W U).swap

lemma witness_comm (ε : ℝ) (U W : finset V) :
  G.witness ε U W = (G.witness ε W U).swap :=
begin
  unfold witness,
  obtain h | rfl | h := trichotomous_of well_ordering_rel U W,
  { rw [if_pos h, if_neg (asymm h), prod.swap_swap] },
  { rw [witness_aux, if_neg, dif_pos (or.intro_left _ rfl), prod.swap],
    exact _root_.irrefl _ },
  rw [if_pos h, if_neg (asymm h)],
end

end simple_graph

open simple_graph

/-- An partition of a finite set `S` is a collection of disjoint subsets of `S` which cover it. -/
@[ext]
structure finpartition_on {V : Type u} (s : finset V) :=
(parts : finset (finset V))
(disjoint : ∀ (a₁ a₂ ∈ parts) x, x ∈ a₁ → x ∈ a₂ → a₁ = a₂)
(cover : ∀ ⦃x⦄, x ∈ s → ∃ (a ∈ parts), x ∈ a)
(subset : ∀ ⦃a⦄, a ∈ parts → a ⊆ s)
(not_empty_mem : ∅ ∉ parts)

/-- A `finpartition V` is a partition of the entire finite type `V` -/
abbreviation finpartition (V : Type u) [fintype V] := finpartition_on (univ : finset V)

namespace finpartition_on
variables {V : Type u} {s : finset V} [decidable_eq V] (P : finpartition_on s)

/-- The size of a finpartition_on is its number of parts. -/
protected def size : ℕ := P.parts.card

lemma disjoint' (a₁ : finset V) (ha₁ : a₁ ∈ P.parts) (a₂ : finset V) (ha₂ : a₂ ∈ P.parts)
  (h : a₁ ≠ a₂) :
  _root_.disjoint a₁ a₂ :=
begin
  rintro x hx,
  rw [inf_eq_inter, mem_inter] at hx,
  exact h (P.disjoint a₁ a₂ ha₁ ha₂ x hx.1 hx.2),
end

lemma nonempty_of_mem_parts {a : finset V} (ha : a ∈ P.parts) : a.nonempty :=
begin
  rw nonempty_iff_ne_empty,
  rintro rfl,
  exact P.not_empty_mem ha,
end

lemma nonempty_parts_iff : P.parts.nonempty ↔ s.nonempty :=
begin
  refine ⟨λ ⟨a, ha⟩, (P.nonempty_of_mem_parts ha).mono (P.subset ha), _⟩,
  rintro ⟨x, hx⟩,
  obtain ⟨a, ha, -⟩ := P.cover hx,
  exact ⟨a, ha⟩,
end

lemma empty_parts_iff : P.parts = ∅ ↔ s = ∅ :=
by rw [←not_iff_not, ←ne.def, ←nonempty_iff_ne_empty, nonempty_parts_iff, nonempty_iff_ne_empty]

lemma bUnion_eq : P.parts.bUnion id = s :=
(bUnion_subset_of_forall_subset _ _ (λ a ha, P.subset ha)).antisymm (λ x hx, mem_bUnion.2
  (P.cover hx))

lemma sum_card_parts : ∑ i in P.parts, i.card = s.card :=
begin
  rw ←card_bUnion P.disjoint',
  exact congr_arg finset.card P.bUnion_eq,
end

/-- Given a finpartition `P` of `s` and finpartitions of each part of `P`, this yields the fin,-/
def bind (Q : Π i ∈ P.parts, finpartition_on i) : finpartition_on s :=
{ parts := P.parts.attach.bUnion (λ i, (Q i.1 i.2).parts),
  disjoint := λ a b ha hb x hxa hxb, begin
    rw finset.mem_bUnion at ha hb,
    obtain ⟨⟨A, hA⟩, -, ha⟩ := ha,
    obtain ⟨⟨B, hB⟩, -, hb⟩ := hb,
    refine (Q A hA).disjoint a b ha _ x hxa hxb,
    have := P.disjoint A B hA hB x ((Q A hA).subset ha hxa) ((Q B hB).subset hb hxb),
    subst this,
    exact hb,
  end,
  cover := begin
    rintro x hx,
    obtain ⟨A, hA, hxA⟩ := P.cover hx,
    obtain ⟨a, ha, hxa⟩ := (Q A hA).cover hxA,
    refine ⟨a, _, hxa⟩,
    rw finset.mem_bUnion,
    exact ⟨⟨A, hA⟩, P.parts.mem_attach _, ha⟩,
  end,
  subset := begin
    rintro a ha,
    rw finset.mem_bUnion at ha,
    obtain ⟨⟨A, hA⟩, -, ha⟩ := ha,
    exact ((Q A hA).subset ha).trans (P.subset hA),
  end,
  not_empty_mem := λ h, begin
    rw finset.mem_bUnion at h,
    obtain ⟨⟨A, hA⟩, -, h⟩ := h,
    exact (Q A hA).not_empty_mem h,
  end }

lemma mem_bind_parts {Q : Π i ∈ P.parts, finpartition_on i} {a : finset V} :
  a ∈ (P.bind Q).parts ↔ ∃ A hA, a ∈ (Q A hA).parts :=
begin
  rw [bind, mem_bUnion],
  split,
  { rintro ⟨⟨A, hA⟩, -, h⟩,
    exact ⟨A, hA, h⟩ },
  rintro ⟨A, hA, h⟩,
  exact ⟨⟨A, hA⟩, mem_attach _ ⟨A, hA⟩, h⟩,
end

lemma bind_size (Q : Π i ∈ P.parts, finpartition_on i) :
  (P.bind Q).size = ∑ A in P.parts.attach, (Q _ A.2).size :=
begin
  apply card_bUnion,
  rintro ⟨A, hA⟩ - ⟨B, hB⟩ - hAB c,
  rw [inf_eq_inter, mem_inter],
  rintro ⟨hcA, hcB⟩,
  apply hAB,
  rw subtype.mk_eq_mk,
  obtain ⟨x, hx⟩ := nonempty_of_mem_parts _ hcA,
  exact P.disjoint _ _ hA hB x (finpartition_on.subset _ hcA hx)
    (finpartition_on.subset _ hcB hx),
end

/-- An equipartition is a partition whose parts are all the same size, up to a difference of `1`. -/
def is_equipartition : Prop :=
equitable_on (P.parts : set (finset V)) card

lemma is_equipartition_iff_card_parts_eq_average :
  P.is_equipartition ↔
  ∀ a : finset V, a ∈ P.parts → a.card = s.card/P.size ∨ a.card = s.card/P.size + 1 :=
begin
  simp_rw [is_equipartition, equitable_on_finset_iff_eq_average _ _, ←card_bUnion P.disjoint',
    ←P.bUnion_eq],
  refl,
end

variables (G : simple_graph V)
open_locale classical

noncomputable def non_uniform_pairs (ε : ℝ) :
  finset (finset V × finset V) :=
(P.parts.product P.parts).filter (λ UW, well_ordering_rel UW.1 UW.2 ∧ ¬G.is_uniform ε UW.1 UW.2)

lemma mem_non_uniform_pairs (U W : finset V) (ε : ℝ) :
  (U, W) ∈ P.non_uniform_pairs G ε ↔ U ∈ P.parts ∧ W ∈ P.parts ∧ well_ordering_rel U W ∧
  ¬G.is_uniform ε U W :=
by rw [non_uniform_pairs, mem_filter, mem_product, and_assoc]

/-- An finpartition is `ε-uniform` iff at most a proportion of `ε` of its pairs of parts are not
`ε-uniform`. -/
def is_uniform (ε : ℝ) : Prop :=
((P.non_uniform_pairs G ε).card : ℝ) ≤ ε * P.size.choose 2

lemma empty_is_uniform {P : finpartition_on s} (hP : P.parts = ∅) (G : simple_graph V) (ε : ℝ) :
  P.is_uniform G ε :=
by rw [finpartition_on.is_uniform, finpartition_on.non_uniform_pairs, finpartition_on.size, hP,
  empty_product, filter_empty, finset.card_empty, finset.card_empty, nat.choose_zero_succ,
  nat.cast_zero, mul_zero]

/-- The index is the auxiliary quantity that drives the induction process in the proof of
Szemerédi's Regularity Lemma (see `increment`). As long as we do not have a suitable equipartition,
we will find a new one that has an index greater than the previous one plus some fixed constant.
Then `index_le_half` ensures this process only happens finitely many times. -/
noncomputable def index (P : finpartition_on s) : ℝ :=
(∑ UW in P.parts.distinct_pairs, G.edge_density UW.1 UW.2^2)/P.size^2

lemma index_nonneg (P : finpartition_on s) :
  0 ≤ P.index G :=
div_nonneg (finset.sum_nonneg (λ _ _, sq_nonneg _)) (sq_nonneg _)

lemma index_le_half (P : finpartition_on s) :
  P.index G ≤ 1/2 :=
begin
  rw finpartition_on.index,
  apply div_le_of_nonneg_of_le_mul (sq_nonneg _),
  { norm_num },
  suffices h : (∑ UW in P.parts.distinct_pairs, G.edge_density UW.1 UW.2^2) ≤
    P.parts.distinct_pairs.card,
  { apply h.trans,
    rw [distinct_pairs_card, div_mul_eq_mul_div, one_mul],
    convert choose_le_pow 2 _,
    norm_num },
  rw [finset.card_eq_sum_ones, sum_nat_cast, nat.cast_one],
  refine finset.sum_le_sum (λ s _, _),
  rw [sq, ←abs_le_one_iff_mul_self_le_one, abs_eq_self.2 (G.edge_density_nonneg _ _)],
  exact G.edge_density_le_one _ _,
end

end finpartition_on

--just here for the pretty printer
/-abbreviation finpartition.size {V : Type*} [decidable_eq V] [fintype V] (P : finpartition V) :
  ℕ := P.size-/

lemma finpartition.is_equipartition_iff_card_parts_eq_average {V : Type*} [decidable_eq V]
  [fintype V] (P : finpartition V) :
  P.is_equipartition ↔
  ∀ a : finset V, a ∈ P.parts → a.card = card V/P.size ∨ a.card = card V/P.size + 1 :=
by rw [P.is_equipartition_iff_card_parts_eq_average, card_univ]

open finpartition_on

/-! ### Simple equipartitions -/

/-- The discrete equipartition of a fintype is the partition in singletons. -/
@[simps]
def discrete_finpartition_on {V : Type*} [decidable_eq V] (s : finset V) : finpartition_on s :=
{ parts := s.image singleton,
  disjoint :=
  begin
    simp only [mem_image, exists_true_left, exists_imp_distrib],
    rintro a₁ a₂ i hi rfl j hj rfl k,
    simp only [mem_singleton],
    rintro rfl rfl,
    refl
  end,
  cover := λ v hv, ⟨{v}, mem_image.2 ⟨v, hv, rfl⟩, finset.mem_singleton_self v⟩,
  subset := by simp,
  not_empty_mem := λ h, begin
    obtain ⟨x, _, hx⟩ := mem_image.1 h,
    exact singleton_ne_empty _ hx,
  end }

@[simps]
def indiscrete_finpartition_on {V : Type*} [decidable_eq V] {s : finset V} (hs : s.nonempty) :
  finpartition_on s :=
{ parts := {s},
  disjoint :=
  begin
    simp only [mem_singleton],
    rintro _ _ rfl rfl _ _ _,
    refl
  end,
  cover := λ u hu, ⟨s, mem_singleton_self _, hu⟩,
  subset := by simp,
  not_empty_mem := λ h, hs.ne_empty (mem_singleton.1 h).symm }

namespace discrete_finpartition_on
variables {V : Type u} [decidable_eq V] (s : finset V) (G : simple_graph V)

lemma is_equipartition : (discrete_finpartition_on s).is_equipartition :=
(equitable_on_iff_almost_eq_constant _ _).2 ⟨1, by simp⟩

protected lemma size : (discrete_finpartition_on s).size = s.card :=
begin
  change finset.card (s.image _) = _,
  rw [finset.card_image_of_injective],
  intros i j k,
  rwa singleton_inj at k,
end

lemma non_uniform_pairs {ε : ℝ} (hε : 0 < ε) :
  (discrete_finpartition_on s).non_uniform_pairs G ε = ∅ :=
begin
  rw eq_empty_iff_forall_not_mem,
  rintro ⟨U, W⟩,
  simp only [finpartition_on.mem_non_uniform_pairs, discrete_finpartition_on_parts, mem_image,
    and_imp, exists_prop, not_and, not_not, ne.def, exists_imp_distrib],
  rintro x hx rfl y hy rfl h U' hU' W' hW' hU hW,
  rw [card_singleton, nat.cast_one, mul_one] at hU hW,
  obtain rfl | rfl := finset.subset_singleton_iff.1 hU',
  { rw [finset.card_empty] at hU,
    exact (hε.not_le hU).elim },
  obtain rfl | rfl := finset.subset_singleton_iff.1 hW',
  { rw [finset.card_empty] at hW,
    exact (hε.not_le hW).elim },
  rwa [sub_self, abs_zero],
end

lemma is_uniform {ε : ℝ} (hε : 0 < ε) :
  (discrete_finpartition_on s).is_uniform G ε :=
begin
  rw [finpartition_on.is_uniform, discrete_finpartition_on.size, non_uniform_pairs _ _ hε,
    finset.card_empty, nat.cast_zero],
  exact mul_nonneg hε.le (nat.cast_nonneg _),
end

end discrete_finpartition_on

section
variables {α : Type*} [decidable_eq α] {s : finset α}

lemma mk_equitable_aux1 {m a b : ℕ} (hs : a*m + b*(m+1) = s.card) (A : finset (finset α))
  (subs : ∀ i ∈ A, i ⊆ s) (h : s = ∅) :
  ∃ (P : finset (finset α)),
    (∀ (x : finset α), x ∈ P → x.card = m ∨ x.card = m+1) ∧
    (∀ x, x ∈ A → (x \ finset.bUnion (P.filter (λ y, y ⊆ x)) id).card ≤ m) ∧
    (∀ x ∈ s, ∃ y ∈ P, x ∈ y) ∧
    (∀ (x₁ x₂ ∈ P) i, i ∈ x₁ → i ∈ x₂ → x₁ = x₂) ∧
    (∀ x ∈ P, x ⊆ s) ∧
    ((P.filter (λ i, finset.card i = m+1)).card = b) :=
begin
  subst h,
  simp only [finset.subset_empty] at subs,
  simp only [finset.card_empty, nat.mul_eq_zero, nat.succ_ne_zero, or_false,
    add_eq_zero_iff, and_false] at hs,
  refine ⟨∅, by simp, λ i hi, by simp [subs i hi], by simp [hs.2]⟩,
end

lemma mk_equitable_aux2 {m a b : ℕ} (hs : a*m + b*(m+1) = s.card) (A : finset (finset α))
  (subs : ∀ i ∈ A, i ⊆ s) (h : m = 0) :
  ∃ (P : finset (finset α)),
    (∀ (x : finset α), x ∈ P → x.card = m ∨ x.card = m+1) ∧
    (∀ x, x ∈ A → (x \ finset.bUnion (P.filter (λ y, y ⊆ x)) id).card ≤ m) ∧
    (∀ x ∈ s, ∃ y ∈ P, x ∈ y) ∧
    (∀ (x₁ x₂ ∈ P) i, i ∈ x₁ → i ∈ x₂ → x₁ = x₂) ∧
    (∀ x ∈ P, x ⊆ s) ∧
    ((P.filter (λ i, finset.card i = m+1)).card = b) :=
begin
  subst h,
  simp only [mul_one, zero_add, mul_zero] at hs,
  simp only [exists_prop, card_eq_zero, zero_add, le_zero_iff, sdiff_eq_empty_iff_subset],
  refine ⟨s.image singleton, by simp, _, by simp, _, by simp, _⟩,
  { intros x hx i hi,
    simp only [mem_bUnion, mem_image, exists_prop, mem_filter, id.def],
    refine ⟨{i}, ⟨⟨i, subs x hx hi, rfl⟩, by simpa⟩, by simp⟩ },
  { simp only [mem_image, and_imp, exists_prop, exists_imp_distrib],
    rintro _ _ x _ rfl y _ rfl,
    simp [singleton_inj] },
  { simp only [mem_image, and_imp, filter_true_of_mem, implies_true_iff, eq_self_iff_true,
      forall_apply_eq_imp_iff₂, exists_imp_distrib, card_singleton],
    rw [card_image_of_injective, hs],
    intros _ _ t,
    rwa singleton_inj at t }
end

lemma mk_equitable_aux {m a b : ℕ} (hs : a*m + b*(m+1) = s.card) (A : finset (finset α))
  (all : ∀ x ∈ s, ∃ y ∈ A, x ∈ y)
  (disj : ∀ (x₁ x₂ ∈ A) i, i ∈ x₁ → i ∈ x₂ → x₁ = x₂)
  (subs : ∀ i ∈ A, i ⊆ s) :
  ∃ (P : finset (finset α)),
    (∀ (x : finset α), x ∈ P → x.card = m ∨ x.card = m+1) ∧
    (∀ x, x ∈ A → (x \ finset.bUnion (P.filter (λ y, y ⊆ x)) id).card ≤ m) ∧
    (∀ x ∈ s, ∃ y ∈ P, x ∈ y) ∧
    (∀ (x₁ x₂ ∈ P) i, i ∈ x₁ → i ∈ x₂ → x₁ = x₂) ∧
    (∀ x ∈ P, x ⊆ s) ∧
    ((P.filter (λ i, finset.card i = m+1)).card = b) :=
begin
  induction s using finset.strong_induction with s ih generalizing A a b,
  cases s.eq_empty_or_nonempty with h hs_ne,
  { exact mk_equitable_aux1 hs A subs h },
  cases (nat.eq_zero_or_pos m) with h m_pos,
  { exact mk_equitable_aux2 hs A subs h },
  have : 0 < a ∨ 0 < b,
  { by_contra,
    push_neg at h,
    simp only [le_zero_iff] at h,
    rw [h.1, h.2] at hs,
    simp only [add_zero, zero_mul, eq_comm, card_eq_zero] at hs,
    exact hs_ne.ne_empty hs },
  set p'_size := if 0 < a then m else m+1 with h',
  have : 0 < p'_size,
  { rw h',
    split_ifs,
    { apply m_pos },
    exact nat.succ_pos' },
  by_cases ∃ p ∈ A, m+1 ≤ finset.card p,
  { rcases h with ⟨p, hp₁, hp₂⟩,
    have : p'_size ≤ p.card,
    { apply le_trans _ hp₂,
      rw h',
      split_ifs,
      { apply nat.le_succ },
      refl },
    obtain ⟨p', hp'₁, hp'₂⟩ := exists_smaller_set _ _ this,
    have : p'.nonempty,
    { rwa [←card_pos, hp'₂] },
    obtain ⟨P', hP'₁, hP'₂, hP'₃, hP'₄, hP'₅, hP'₆⟩ :=
      @ih (s \ p')
      (sdiff_ssubset (finset.subset.trans hp'₁ (subs _ hp₁)) ‹p'.nonempty›)
      (insert (p \ p') (A.erase p))
      (if 0 < a then a-1 else a)
      (if 0 < a then b else b-1)
      _ _ _ _,
    rotate,
    { rw [card_sdiff (finset.subset.trans hp'₁ (subs _ hp₁)), ←hs, hp'₂, h'],
      split_ifs,
      { rw [nat.mul_sub_right_distrib, one_mul,
          nat.sub_add_eq_add_sub (nat.le_mul_of_pos_left h)] },
      { rw [nat.mul_sub_right_distrib, one_mul, ←nat.add_sub_assoc],
        apply nat.le_mul_of_pos_left (‹0 < a ∨ 0 < b›.resolve_left h) } },
    { simp only [and_imp, exists_prop, mem_insert, mem_sdiff, mem_erase, ne.def],
      intros x hx₁ hx₂,
      by_cases x ∈ p,
      { refine ⟨p \ p', or.inl rfl, by simp only [hx₂, h, mem_sdiff, not_false_iff, and_self]⟩ },
    obtain ⟨y, hy₁, hy₂⟩ := all x hx₁,
      refine ⟨y, or.inr ⟨λ t, _, hy₁⟩, hy₂⟩,
      apply h,
      rw ←t,
      exact hy₂ },
    { simp only [mem_insert, mem_erase, ne.def],
      rintro x₁ x₂ (rfl | hx₁) (rfl | hx₂) i hi₁ hi₂,
      { refl },
      { apply (hx₂.1 (disj _ _ hx₂.2 hp₁ i hi₂ (sdiff_subset _ _ hi₁))).elim },
      { apply (hx₁.1 (disj _ _ hx₁.2 hp₁ i hi₁ (sdiff_subset _ _ hi₂))).elim },
      exact disj _ _ hx₁.2 hx₂.2 _ hi₁ hi₂ },
    { simp only [and_imp, mem_insert, forall_eq_or_imp, mem_erase, ne.def],
      split,
      { apply sdiff_subset_sdiff (subs _ hp₁) (refl _) },
      intros i hi₁ hi₂ x hx,
      simp only [mem_sdiff, subs i hi₂ hx, true_and],
      exact λ q, hi₁ (disj _ _ hi₂ hp₁ _ hx (hp'₁ q)) },
    refine ⟨insert p' P', _, _, _, _, _, _⟩,
    { simp only [mem_insert, forall_eq_or_imp, and_iff_left hP'₁, hp'₂, h'],
      split_ifs,
      { left, refl },
      { right, refl } },
    { conv in (_ ∈ _) {rw ←finset.insert_erase hp₁},
      simp only [and_imp, mem_insert, forall_eq_or_imp, ne.def],
      split,
      { simp only [filter_insert, if_pos hp'₁, bUnion_insert, mem_erase],
        apply le_trans (card_le_of_subset _) (hP'₂ (p \ p') (mem_insert_self _ _)),
        intros i,
        simp only [not_exists, mem_bUnion, and_imp, mem_union, mem_filter, mem_sdiff, id.def,
          not_or_distrib],
        intros hi₁ hi₂ hi₃,
        refine ⟨⟨hi₁, hi₂⟩, λ x hx hx', hi₃ _ hx (finset.subset.trans hx' (sdiff_subset _ _))⟩ },
      intros x hx,
      apply (card_le_of_subset _).trans (hP'₂ x (mem_insert_of_mem hx)),
      apply sdiff_subset_sdiff (finset.subset.refl _) (bUnion_subset_bUnion_of_subset_left _ _),
      refine filter_subset_filter _ (subset_insert _ _) },
    { simp only [and_imp, exists_prop, mem_sdiff] at hP'₃,
      simp only [exists_prop, mem_insert, or_and_distrib_right, exists_or_distrib],
      intros x hx,
      refine if h : x ∈ p' then or.inl ⟨_, rfl, h⟩ else or.inr (hP'₃ _ hx h) },
    { simp only [mem_insert, forall_eq_or_imp],
      rintro x₁ x₂ (rfl | hx₁) (rfl | hx₂),
      { simp },
      { intros i hi₁ hi₂,
        apply ((mem_sdiff.1 (hP'₅ _ hx₂ hi₂)).2 hi₁).elim },
      { intros i hi₁ hi₂,
        apply ((mem_sdiff.1 (hP'₅ _ hx₁ hi₁)).2 hi₂).elim },
      exact hP'₄ _ _ hx₁ hx₂ },
    { simp only [mem_insert, forall_eq_or_imp],
      refine ⟨finset.subset.trans hp'₁ (subs _ hp₁),
        λ x hx i hi, (mem_sdiff.1 (hP'₅ x hx hi)).1⟩ },
    rw [filter_insert, hp'₂, h'],
    by_cases 0 < a,
    { rw [if_pos h, if_neg, hP'₆, if_pos h],
      simp only [nat.one_ne_zero, self_eq_add_right, not_false_iff] },
    rw [if_neg h, if_pos rfl, card_insert_of_not_mem, hP'₆, if_neg h, nat.sub_add_cancel],
    apply ‹0 < a ∨ 0 < b›.resolve_left h,
    simp only [mem_filter, hp'₂, h', if_neg h, eq_self_iff_true, and_true],
    intro t,
    obtain ⟨i, hi⟩ := ‹p'.nonempty›,
    apply (mem_sdiff.1 (hP'₅ _ t hi)).2 hi },
  push_neg at h,
  have : p'_size ≤ s.card,
  { rw [←hs, h'],
    split_ifs,
    { apply le_add_right (nat.le_mul_of_pos_left ‹0 < a›) },
    exact le_add_left (nat.le_mul_of_pos_left (‹0 < a ∨ 0 < b›.resolve_left ‹¬0 < a›)) },
  obtain ⟨s', hs'₁, hs'₂⟩ := exists_smaller_set _ _ this,
  have : s'.nonempty,
  { rwa [←card_pos, hs'₂] },
  obtain ⟨P', hP'₁, hP'₂, hP'₃, hP'₄, hP'₅, hP'₆⟩ :=
    @ih (s \ s')
    (sdiff_ssubset hs'₁ ‹s'.nonempty›)
    (A.image (λ t, t \ s'))
    (if 0 < a then a-1 else a)
    (if 0 < a then b else b-1)
    _ _ _ _,
  rotate,
  { rw [card_sdiff ‹s' ⊆ s›, hs'₂, h', ←hs],
    split_ifs,
    { rw [nat.mul_sub_right_distrib, one_mul,
        nat.sub_add_eq_add_sub (nat.le_mul_of_pos_left ‹0 < a›)] },
    rw [nat.mul_sub_right_distrib, one_mul, ←nat.add_sub_assoc],
    exact nat.le_mul_of_pos_left (‹0 < a ∨ 0 < b›.resolve_left ‹¬0 < a›) },
  { intros x hx,
    simp only [mem_sdiff] at hx,
    obtain ⟨y, hy, hy'⟩ := all x hx.1,
    simp only [mem_image, exists_prop, mem_sdiff, exists_exists_and_eq_and],
    refine ⟨_, hy, hy', hx.2⟩ },
  { simp only [mem_image, and_imp, exists_prop, exists_imp_distrib],
    rintro x₁ x₂ x hx rfl x' hx' rfl i hi₁ hi₂,
    simp only [mem_sdiff] at hi₁ hi₂,
    rw disj _ _ hx hx' i hi₁.1 hi₂.1 },
  { simp only [mem_image, and_imp, forall_apply_eq_imp_iff₂, exists_imp_distrib],
    intros a ha,
    apply sdiff_subset_sdiff (subs a ha) (refl _) },
  refine ⟨insert s' P', _, _, _, _, _, _⟩,
  { simp only [mem_insert, forall_eq_or_imp, and_iff_left hP'₁, hs'₂, h'],
    split_ifs,
    { left, refl },
    right, refl },
  { intros x hx,
    refine le_trans (card_le_of_subset (sdiff_subset _ _)) _,
    rw ←nat.lt_succ_iff,
    exact h _ hx },
  { intros x hx,
    by_cases x ∈ s',
    { refine ⟨_, by simp only [mem_insert, true_or, eq_self_iff_true], h⟩ },
    obtain ⟨w, hw, hw'⟩ := hP'₃ x (by simp only [hx, h, mem_sdiff, not_false_iff, and_self]),
    exact ⟨w, by simp only [hw, mem_insert, or_true], hw'⟩ },
  { simp only [mem_insert],
    rintro _ _ (rfl | hx₁) (rfl | hx₂) i hi₁ hi₂,
    { refl },
    { apply ((mem_sdiff.1 (hP'₅ _ hx₂ hi₂)).2 hi₁).elim },
    { apply ((mem_sdiff.1 (hP'₅ _ hx₁ hi₁)).2 hi₂).elim },
    exact hP'₄ _ _ hx₁ hx₂ _ hi₁ hi₂ },
  { simp only [hs'₁, true_and, mem_insert, forall_eq_or_imp],
    intros x hx,
    apply finset.subset.trans (hP'₅ x hx) (sdiff_subset _ _) },
  rw [filter_insert, hs'₂, h'],
  by_cases 0 < a,
  { rw [if_pos h, if_neg, hP'₆, if_pos h],
    simp only [nat.one_ne_zero, self_eq_add_right, not_false_iff] },
  rw [if_neg h, if_pos rfl, card_insert_of_not_mem, hP'₆, if_neg h, nat.sub_add_cancel],
  apply ‹0 < a ∨ 0 < b›.resolve_left h,
  simp only [mem_filter, hs'₂, h', if_neg h, eq_self_iff_true, and_true],
  intro t,
  obtain ⟨i, hi⟩ := ‹s'.nonempty›,
  exact (mem_sdiff.1 (hP'₅ _ t hi)).2 hi,
end.

namespace finpartition_on

/--
Given a partition `Q` of `s`, as well as a proof that `a*m + b*(m+1) = s.card`, build a new
partition `P` of `s` where each part has size `m` or `m+1`, every part of `Q` is the union of
parts of `P` plus at most `m` extra elements, there are `b` parts of size `m+1` and provided
`m > 0`, there are `a` parts of size `m` and hence `a+b` parts in total.
The `m > 0` condition is required since there may be zero or one parts of size `0`, while `a` could
be arbitrary.
-/
noncomputable def mk_equitable (Q : finpartition_on s) {m a b : ℕ}
  (h : a*m + b*(m+1) = s.card) :
  finpartition_on s :=
begin
  let P := classical.some (mk_equitable_aux h Q.parts Q.cover Q.disjoint Q.subset),
  have hP := classical.some_spec (mk_equitable_aux h Q.parts Q.cover Q.disjoint Q.subset),
  refine ⟨P.erase ∅,
    λ a b ha hb x hxa hxb, hP.2.2.2.1 a b (erase_subset _ _ ha) (erase_subset _ _ hb) x hxa hxb,
    λ u hu, _, λ u hu, hP.2.2.2.2.1 _ (erase_subset _ _ hu), not_mem_erase _ _⟩,
  obtain ⟨a, ha, hua⟩ := hP.2.2.1 u hu,
  exact ⟨a, mem_erase.2 ⟨nonempty_iff_ne_empty.1 ⟨u, hua⟩, ha⟩, hua⟩,
end

lemma card_eq_of_mem_parts_mk_equitable {Q : finpartition_on s} {m a b : ℕ}
  (h : a*m + b*(m+1) = s.card) {u : finset α} (hu : u ∈ (Q.mk_equitable h).parts) :
  u.card = m ∨ u.card = m + 1 :=
(classical.some_spec (mk_equitable_aux h Q.parts Q.cover Q.disjoint Q.subset)).1
  u (mem_of_mem_erase hu)

lemma mk_equitable.is_equipartition (Q : finpartition_on s) {m a b : ℕ}
  (h : a*m + b*(m+1) = s.card) :
  (Q.mk_equitable h).is_equipartition :=
begin
  rw [is_equipartition, equitable_on_iff_almost_eq_constant],
  exact ⟨m, λ u hu, card_eq_of_mem_parts_mk_equitable h hu⟩,
end

lemma card_filter_mk_equitable_big (Q : finpartition_on s) {m a b : ℕ}
  (h : a*m + b*(m+1) = s.card) :
  ((Q.mk_equitable h).parts.filter (λ u : finset α, u.card = m + 1)).card = b :=
begin
  convert (classical.some_spec (mk_equitable_aux h Q.parts Q.cover Q.disjoint
    Q.subset)).2.2.2.2.2 using 2,
  ext u,
  rw [mem_filter, mem_filter, finpartition_on.mk_equitable, mem_erase, and_assoc,
    and_iff_right_iff_imp],
  rintro hu rfl,
  rw finset.card_empty at hu,
  exact nat.succ_ne_zero _ hu.2.symm,
end

lemma card_filter_mk_equitable_small (Q : finpartition_on s) {m a b : ℕ} (hm : 0 < m)
  (h : a*m + b*(m+1) = s.card) :
  ((Q.mk_equitable h).parts.filter (λ u : finset α, u.card = m)).card = a :=
begin
  refine (mul_eq_mul_right_iff.1 $ (add_left_inj $ b * (m + 1)).1 _).resolve_right hm.ne.symm,
  rw [h, ←(Q.mk_equitable h).sum_card_parts],
  have hunion : (Q.mk_equitable h).parts = (Q.mk_equitable h).parts.filter (λ u, u.card = m) ∪
    (Q.mk_equitable h).parts.filter (λ u, u.card = m + 1),
  { rw [←filter_or, filter_true_of_mem],
    exact λ x hx, card_eq_of_mem_parts_mk_equitable h hx },
  nth_rewrite 1 hunion,
  rw [sum_union, sum_const_nat (λ x hx, (mem_filter.1 hx).2),
    sum_const_nat (λ x hx, (mem_filter.1 hx).2), Q.card_filter_mk_equitable_big],
  refine λ x hx, nat.succ_ne_self m _,
  rw [inf_eq_inter, mem_inter, mem_filter, mem_filter] at hx,
  rw [nat.succ_eq_add_one, ←hx.2.2, hx.1.2],
end

lemma mk_equitable.size {Q : finpartition_on s} {m a b : ℕ} (hm : 0 < m)
  (h : a * m + b * (m + 1) = s.card) :
  (Q.mk_equitable h).size = a + b :=
begin
  have hunion : (Q.mk_equitable h).parts = (Q.mk_equitable h).parts.filter (λ u, u.card = m) ∪
    (Q.mk_equitable h).parts.filter (λ u, u.card = m + 1),
  { rw [←filter_or, filter_true_of_mem],
    exact λ x hx, card_eq_of_mem_parts_mk_equitable h hx },
  rw [finpartition_on.size, hunion, card_union_eq, Q.card_filter_mk_equitable_small hm,
    Q.card_filter_mk_equitable_big],
  refine λ x hx, nat.succ_ne_self m _,
  rw [inf_eq_inter, mem_inter, mem_filter, mem_filter] at hx,
  rw [nat.succ_eq_add_one, ←hx.2.2, hx.1.2],
end

lemma almost_in_atoms_of_mem_parts_mk_equitable {Q : finpartition_on s} {m a b : ℕ}
  (h : a * m + b * (m + 1) = s.card) {u : finset α} (hu : u ∈ Q.parts) :
  (u \ finset.bUnion ((Q.mk_equitable h).parts.filter (λ x, x ⊆ u)) id).card ≤ m :=
begin
  have := (classical.some_spec (mk_equitable_aux h Q.parts Q.cover Q.disjoint
    Q.subset)).2.1,
  refine (card_le_of_subset _).trans ((classical.some_spec (mk_equitable_aux h Q.parts Q.cover
    Q.disjoint Q.subset)).2.1 u hu),
  intros x,
  simp only [not_exists, mem_bUnion, and_imp, mem_filter, mem_sdiff, id.def, ne.def],
  refine λ hxu hx, ⟨hxu, λ a ha hau, _⟩,
  obtain rfl | hanemp := eq_or_ne a ∅,
  { exact not_mem_empty _ },
  exact hx _ (mem_erase.2 ⟨hanemp, ha⟩) hau,
end

end finpartition_on

end

section atomise
variables {α : Type*} [decidable_eq α] {s : finset α}

/-- Cuts `s` along the finsets in `Q`: Two elements of `s` will be in the same -/
def atomise (s : finset α) (Q : finset (finset α)) :
  finpartition_on s :=
{ parts := Q.powerset.image (λ P, s.filter (λ i, ∀ x ∈ Q, x ∈ P ↔ i ∈ x)) \ {∅},
  disjoint := begin
    rintro x y hx hy i hi₁ hi₂,
    simp only [mem_sdiff, mem_powerset, mem_image, exists_prop] at hx hy,
    obtain ⟨P, hP, rfl⟩ := hx.1,
    obtain ⟨P', hP', rfl⟩ := hy.1,
    suffices h : P = P',
    { subst h },
    rw mem_filter at hi₁ hi₂,
    ext j,
    refine ⟨λ hj, _, λ hj, _⟩,
    { rwa [hi₂.2 _ (hP hj), ←hi₁.2 _ (hP hj)] },
    rwa [hi₁.2 _ (hP' hj), ←hi₂.2 _ (hP' hj)],
  end,
  cover := begin
    rintro x hx,
    simp only [mem_sdiff, mem_powerset, mem_image, exists_prop, mem_filter, and_assoc],
    rw exists_exists_and_eq_and,
    have h : x ∈ s.filter (λ i, ∀ y ∈ Q, (y ∈ Q.filter (λ t, x ∈ t) ↔ i ∈ y)),
    { simp only [mem_filter, and_iff_right_iff_imp],
      exact ⟨hx, λ y hy _, hy⟩ },
    refine ⟨Q.filter (λ t, x ∈ t), filter_subset _ _, _, h⟩,
    rw [mem_singleton, ←ne.def, ←nonempty_iff_ne_empty],
    exact ⟨x, h⟩,
  end,
  subset := begin
    rintro x hx,
    simp only [mem_sdiff, mem_powerset, mem_image, exists_prop] at hx,
    obtain ⟨P, hP, rfl⟩ := hx.1,
    exact filter_subset _ s,
  end,
  not_empty_mem := λ h, (mem_sdiff.1 h).2 (mem_singleton_self _) }

lemma mem_atomise {s : finset α} {Q : finset (finset α)} {A : finset α} :
  A ∈ (atomise s Q).parts ↔ A.nonempty ∧ ∃ (P ⊆ Q), s.filter (λ i, ∀ x ∈ Q, x ∈ P ↔ i ∈ x) = A :=
by { simp only [atomise, mem_sdiff, nonempty_iff_ne_empty, mem_singleton, and_comm, mem_image,
  mem_powerset, exists_prop] }

lemma atomise_empty (hs : s.nonempty) : (atomise s ∅).parts = {s} :=
begin
  rw [atomise],
  simp,
  apply disjoint.sdiff_eq_left,
  rwa [disjoint_singleton, mem_singleton, ←ne.def, ne_comm, ←nonempty_iff_ne_empty],
end

lemma atomise_disjoint {s : finset α} {Q : finset (finset α)} {x y : finset α}
  (hx : x ∈ (atomise s Q).parts) (hy : y ∈ (atomise s Q).parts) : disjoint x y ∨ x = y :=
begin
  rw or_iff_not_imp_left,
  simp only [disjoint_left, not_forall, and_imp, exists_prop, not_not, exists_imp_distrib],
  intros i hi₁ hi₂,
  simp only [mem_atomise] at hx hy,
  obtain ⟨P, hP, rfl⟩ := hx.2,
  obtain ⟨P', hP', rfl⟩ := hy.2,
  simp only [mem_filter] at hi₁ hi₂,
  suffices h : P = P',
  { subst h },
  ext j,
  refine ⟨λ hj, _, λ hj, _⟩,
  { rwa [hi₂.2 _ (hP hj), ←hi₁.2 _ (hP hj)] },
  { rwa [hi₁.2 _ (hP' hj), ←hi₂.2 _ (hP' hj)] },
end

lemma atomise_covers {s : finset α} (Q : finset (finset α)) {x : α} (hx : x ∈ s) :
  ∃ Y ∈ (atomise s Q).parts, x ∈ Y :=
(atomise s Q).cover hx

lemma atomise_unique_covers {s : finset α} {Q : finset (finset α)} {x : α} (hx : x ∈ s) :
  ∃! Y ∈ (atomise s Q).parts, x ∈ Y :=
begin
  obtain ⟨Y, hY₁, hY₂⟩ := atomise_covers Q hx,
  refine exists_unique.intro2 Y hY₁ hY₂ (λ Y' hY'₁ hY'₂,
    or.resolve_left (atomise_disjoint ‹Y' ∈ _› ‹Y ∈ _›) _),
  simp only [disjoint_left, exists_prop, not_not, not_forall],
  exact ⟨_, hY'₂, hY₂⟩,
end

lemma card_atomise {s : finset α} {Q : finset (finset α)} :
  ((atomise s Q).parts).card ≤ 2^Q.card :=
begin
  apply (card_le_of_subset (sdiff_subset _ _)).trans,
  apply finset.card_image_le.trans,
  simp,
end

lemma union_of_atoms_aux {s : finset α} {Q : finset (finset α)} {A : finset α}
  (hA : A ∈ Q) (hs : A ⊆ s) (i : α) :
  (∃ (B ∈ (atomise s Q).parts), B ⊆ A ∧ i ∈ B) ↔ i ∈ A :=
begin
  split,
  { rintro ⟨B, hB₁, hB₂, hB₃⟩,
    exact hB₂ hB₃ },
  intro hi,
  obtain ⟨B, hB₁, hB₂⟩ := atomise_covers Q (hs hi),
  refine ⟨B, hB₁, λ j hj, _, hB₂⟩,
  obtain ⟨P, hP, rfl⟩ := (mem_atomise.1 hB₁).2,
  simp only [mem_filter] at hB₂ hj,
  rwa [←hj.2 _ hA, hB₂.2 _ hA]
end

lemma union_of_atoms {s : finset α} {Q : finset (finset α)} {A : finset α}
  (hA : A ∈ Q) (hs : A ⊆ s) :
  s.filter (λ i, ∃ B ∈ (atomise s Q).parts, B ⊆ A ∧ i ∈ B) = A :=
begin
  ext i,
  simp only [mem_filter, union_of_atoms_aux hA hs],
  exact and_iff_right_iff_imp.2 (@hs i),
end

instance {B : finset α} : decidable B.nonempty :=
decidable_of_iff' _ finset.nonempty_iff_ne_empty

lemma union_of_atoms' {s : finset α} {Q : finset (finset α)} (A : finset α)
  (hx : A ∈ Q) (hs : A ⊆ s) :
  ((atomise s Q).parts.filter (λ B, B ⊆ A ∧ B.nonempty)).bUnion id = A :=
begin
  ext x,
  rw mem_bUnion,
  simp only [exists_prop, mem_filter, id.def, and_assoc],
  rw ←union_of_atoms_aux hx hs,
  simp only [exists_prop],
  exact exists_congr (λ a, and_congr_right (λ b, and_congr_right (λ c,
    and_iff_right_of_imp (λ h, ⟨_, h⟩)))),
end

lemma partial_atomise {s : finset α} {Q : finset (finset α)} (A : finset α)
  (hA : A ∈ Q) (hs : A ⊆ s) :
  ((atomise s Q).parts.filter (λ B, B ⊆ A ∧ B.nonempty)).card ≤ 2^(Q.card - 1) :=
begin
  suffices h :
    (atomise s Q).parts.filter (λ B, B ⊆ A ∧ B.nonempty) ⊆
      (Q.erase A).powerset.image (λ P, s.filter (λ i, ∀ x ∈ Q, x ∈ insert A P ↔ i ∈ x)),
  { apply (card_le_of_subset h).trans (card_image_le.trans _),
    rw [card_powerset, card_erase_of_mem hA],
    refl },
  rw subset_iff,
  simp only [mem_erase, mem_sdiff, mem_powerset, mem_image, exists_prop, mem_filter, and_assoc,
    finset.nonempty, exists_imp_distrib, and_imp, mem_atomise, forall_apply_eq_imp_iff₂],
  rintro P' i hi P PQ rfl hy₂ j hj,
  refine ⟨P.erase A, erase_subset_erase _ PQ, _⟩,
  have : A ∈ P,
  { rw mem_filter at hi,
    rw hi.2 _ hA,
    apply hy₂,
    exact mem_filter.2 hi },
  simp only [insert_erase this, filter_congr_decidable],
end

end atomise

/-- Arbitrary equipartition into `t` parts -/
lemma dummy_equipartition {V : Type*} [decidable_eq V] (s : finset V) {t : ℕ}
  (ht : 0 < t) (hs : t ≤ s.card) :
  ∃ (P : finpartition_on s), P.is_equipartition ∧ P.size = t :=
begin
  have : (t - s.card % t) * (s.card / t) + (s.card % t) * (s.card / t + 1) = s.card,
  { rw [nat.mul_sub_right_distrib, mul_add, ←add_assoc, nat.sub_add_cancel, mul_one, add_comm,
      nat.mod_add_div],
    exact nat.mul_le_mul_right _ ((nat.mod_lt _ ht).le) },
  refine ⟨(indiscrete_finpartition_on $ finset.card_pos.1 (ht.trans_le hs)).mk_equitable this,
    finpartition_on.mk_equitable.is_equipartition _ _, _⟩,
  rw [finpartition_on.mk_equitable.size (nat.div_pos hs ht), nat.sub_add_cancel
    (nat.mod_lt _ ht).le],
end

/-! ### The actual proof -/

/-- Auxiliary function to explicit the bound on the size of the equipartition in the proof of
Szemerédi's Regularity Lemma -/
def exp_bound (n : ℕ) : ℕ := n * 4^n

lemma le_exp_bound :
 id ≤ exp_bound :=
λ n, nat.le_mul_of_pos_right (pow_pos (by norm_num) n)

lemma exp_bound_mono :
  monotone exp_bound :=
λ a b h, nat.mul_le_mul h (nat.pow_le_pow_of_le_right (by norm_num) h)

lemma exp_bound_pos {n : ℕ} (hn : 0 < n) : 0 < exp_bound n :=
hn.trans_le (le_exp_bound n)

open_locale classical
variables {V : Type u} [fintype V] {G : simple_graph V} {P : finpartition V} {ε : ℝ}

local notation `m` := card V/exp_bound P.size
local notation `a` := card V/P.size - m * 4^P.size

private lemma card_aux₀ :
  a + 1 ≤ 4^P.size :=
begin
  have h : 1 ≤ 4^P.size := one_le_pow_of_one_le (by norm_num) _,
  rw [exp_bound, ←nat.div_div_eq_div_mul, nat.add_le_to_le_sub _ h],
  apply nat.sub_le_left_of_le_add,
  rw ←nat.add_sub_assoc h,
  exact nat.le_pred_of_lt (lt_div_mul_add h),
end

private lemma card_aux₁ :
  m * 4^P.size + a = (4^P.size - a) * m + a * (m + 1) :=
by rw [mul_add, mul_one, ←add_assoc, ←add_mul, nat.sub_add_cancel
  ((nat.le_succ _).trans card_aux₀), mul_comm]

private lemma card_aux₂ {U : finset V} (hUcard : U.card = m * 4^P.size + a) :
  (4^P.size - a) * m + a * (m + 1) = U.card :=
by rw [hUcard, card_aux₁]

private lemma card_aux₃ (hP : P.is_equipartition) {U : finset V} (hU : U ∈ P.parts)
  (hUcard : ¬U.card = m * 4^P.size + a) :
  (4^P.size - (a + 1)) * m + (a + 1) * (m + 1) = U.card :=
begin
  have aux :
    m * 4^finpartition_on.size P + a = card V/P.size,
  { apply nat.add_sub_cancel',
    rw [exp_bound, ←nat.div_div_eq_div_mul],
    exact nat.div_mul_le_self _ _ },
  rw aux at hUcard,
  rw P.is_equipartition_iff_card_parts_eq_average at hP,
  rw [(hP U hU).resolve_left hUcard, mul_add, mul_one, ←add_assoc, ←add_mul,
    nat.sub_add_cancel card_aux₀, ←add_assoc, mul_comm, nat.add_sub_cancel', ←aux],
  rw ←aux,
  exact nat.le_add_right _ _,
end

/-- The work-horse of SRL. This says that if we have an equipartition which is *not* uniform, then
we can make a (much bigger) equipartition with a slightly higher index. This is helpful since the
index is bounded by a constant (see `index_le_half`), so this process eventually terminates and
yields a not-too-big uniform equipartition. -/
noncomputable def finpartition_on.is_equipartition.increment (hP : P.is_equipartition)
  (G : simple_graph V) (ε : ℝ) :
  finpartition V :=
begin
  let R : ∀ U, finpartition_on U := λ U, atomise U (finset.image
    (λ W, (G.witness ε U W).1) (P.parts.filter (λ W, ¬G.is_uniform ε U W))),
  exact P.bind (λ U hU, dite (U.card = m * 4^P.size + a)
    (λ hUcard, (R U).mk_equitable $ card_aux₂ hUcard)
    (λ hUcard, (R U).mk_equitable $ card_aux₃ hP hU hUcard)),
end

open finpartition_on.is_equipartition

namespace increment

protected lemma size (hP : P.is_equipartition)
  (hε : 100 < ε^5 * 4^P.size) (hPV : P.size * 16^P.size ≤ card V) (hPG : ¬P.is_uniform G ε) :
  (hP.increment G ε).size = exp_bound P.size :=
begin
  let R : ∀ U, finpartition_on U := λ U, atomise U (finset.image
    (λ W, (G.witness ε U W).1) (P.parts.filter (λ W, ¬G.is_uniform ε U W))),
  have hPV' : exp_bound P.size ≤ card V :=
    (nat.mul_le_mul_of_nonneg_left $ nat.pow_le_pow_of_le_left (by norm_num) _).trans hPV,
  have hPpos : 0 < exp_bound P.size := exp_bound_pos ((nat.eq_zero_or_pos _).resolve_left $ λ h,
    hPG $ finpartition_on.empty_is_uniform (by rw [←finset.card_eq_zero, ←finpartition_on.size, h])
    _ _),
  rw [is_equipartition, equitable_on_finset_iff_eq_average] at hP,
  rw [increment, bind_size],
  simp_rw [apply_dite finpartition_on.size],
  rw [sum_dite, sum_const_nat, sum_const_nat, card_attach, card_attach], rotate,
  exact λ x hx, finpartition_on.mk_equitable.size (nat.div_pos hPV' hPpos) _,
  exact λ x hx, finpartition_on.mk_equitable.size (nat.div_pos hPV' hPpos) _,
  rw [nat.sub_add_cancel card_aux₀, nat.sub_add_cancel ((nat.le_succ _).trans card_aux₀), ←add_mul],
  congr,
  rw [filter_card_add_filter_neg_card_eq_card, card_attach, finpartition_on.size],
end

protected lemma is_equipartition (hP : P.is_equipartition) (G : simple_graph V) (ε : ℝ) :
  (hP.increment G ε).is_equipartition :=
begin
  let R : ∀ U, finpartition_on U := λ U, atomise U (finset.image
    (λ W, (G.witness ε U W).1) (P.parts.filter (λ W, ¬G.is_uniform ε U W))),
  rw [is_equipartition, equitable_on_iff_almost_eq_constant],
  refine ⟨m, λ A hA, _⟩,
  rw [mem_coe, increment, mem_bind_parts] at hA,
  obtain ⟨U, hU, hA⟩ := hA,
  by_cases hUcard : U.card = m * 4^P.size + a,
  { rw dif_pos hUcard at hA,
    exact finpartition_on.card_eq_of_mem_parts_mk_equitable _ hA },
  rw dif_neg hUcard at hA,
  exact finpartition_on.card_eq_of_mem_parts_mk_equitable _ hA,
end

protected lemma index (hP : P.is_equipartition)
  (hε : 100 < ε^5 * 4^P.size) (hPV : P.size * 16^P.size ≤ card V) (hPG : ¬P.is_uniform G ε) :
  P.index G + ε^5 / 8 ≤ (hP.increment G ε).index G :=
begin
  let R : ∀ U, finpartition_on U := λ U, atomise U (finset.image
    (λ W, (G.witness ε U W).1) (P.parts.filter (λ W, ¬G.is_uniform ε U W))),
  sorry
end

end increment

/-- The maximal number of times we need to blow up an equipartition to make it uniform -/
noncomputable def iteration_bound (ε : ℝ) (l : ℕ) : ℕ :=
max l (nat_floor (real.log (100/ε^5) / real.log 4) + 1)

lemma le_iteration_bound (ε : ℝ) (l : ℕ) : l ≤ iteration_bound ε l := le_max_left l _
lemma iteration_bound_pos (ε : ℝ) (l : ℕ) : 0 < iteration_bound ε l :=
nat.succ_pos'.trans_le (le_max_right _ _)

lemma const_lt_mul_pow_iteration_bound {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
  100 < ε^5 * 4^iteration_bound ε l :=
begin
  rw [←real.rpow_nat_cast 4, ←div_lt_iff' (pow_pos hε 5), real.lt_rpow_iff_log_lt, ←div_lt_iff,
    iteration_bound, nat.cast_max],
  { exact lt_max_of_lt_right (lt_nat_floor_add_one _) },
  { apply real.log_pos,
    norm_num },
  { exact div_pos (by norm_num) (pow_pos hε 5) },
  norm_num,
end

/-- An explicit bound on the size of the equipartition in the proof of Szemerédi's Regularity Lemma
-/
noncomputable def szemeredi_bound (ε : ℝ) (l : ℕ) : ℕ :=
(exp_bound^[nat_floor (4/ε^5)] (iteration_bound ε l)) *
  16^(exp_bound^[nat_floor (4/ε^5)] (iteration_bound ε l))

lemma iteration_bound_le_szemeredi_bound (ε l) :
  iteration_bound ε l ≤ szemeredi_bound ε l :=
(id_le_iterate_of_id_le le_exp_bound _ _).trans
  (nat.le_mul_of_pos_right (pow_pos (by norm_num) _))

/-- Effective Szemerédi's Regularity Lemma: For any sufficiently big graph, there is an ε-uniform
equipartition of bounded size (where the bound does not depend on the graph). -/
theorem szemeredi_regularity {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1) (l : ℕ) (hG : l ≤ card V) :
  ∃ (P : finpartition V),
    P.is_equipartition ∧ l ≤ P.size ∧ P.size ≤ szemeredi_bound ε l ∧ P.is_uniform G ε :=
begin
  obtain hV | hV := le_total (card V) (szemeredi_bound ε l),
  { refine ⟨discrete_finpartition_on _, discrete_finpartition_on.is_equipartition _, _⟩,
    rw [discrete_finpartition_on.size, card_univ],
    exact ⟨hG, hV, discrete_finpartition_on.is_uniform _ G hε⟩ },
  let t := iteration_bound ε l,
  have ht : 0 < t := iteration_bound_pos _ _,
  suffices h : ∀ i, ∃ (P : finpartition V), P.is_equipartition ∧
    t ≤ P.size ∧ P.size ≤ (exp_bound^[i]) t ∧ (P.is_uniform G ε ∨ ε^5 / 8 * i ≤ P.index G),
  { obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := h (nat_floor (4/ε^5) + 1),
    refine ⟨P, hP₁, (le_iteration_bound _ _).trans hP₂, hP₃.trans _, _⟩,
    { rw function.iterate_succ_apply',
      exact mul_le_mul_left' (pow_le_pow_of_le_left (by norm_num) (by norm_num) _) _ },
    apply hP₄.resolve_right,
    rintro hPindex,
    apply lt_irrefl (1/2 : ℝ),
    calc
      1/2 = ε ^ 5 / 8 * (4 / ε ^ 5)
          : by { rw [mul_comm, div_mul_div_cancel 4 (pow_pos hε 5).ne'], norm_num }
      ... < ε ^ 5 / 8 * (nat_floor (4 / ε ^ 5) + 1)
          : (mul_lt_mul_left (div_pos (pow_pos hε 5) (by norm_num))).2 (lt_nat_floor_add_one _)
      ... ≤ P.index G : hPindex
      ... ≤ 1/2 : P.index_le_half G },
  intro i,
  induction i with i ih,
  { have : t ≤ (univ : finset V).card :=
      (iteration_bound_le_szemeredi_bound _ _).trans (by rwa finset.card_univ),
    obtain ⟨P, hP₁, hP₂⟩ := dummy_equipartition (univ : finset V) ht this,
    refine ⟨P, hP₁, hP₂.ge, hP₂.le, or.inr _⟩,
    rw [nat.cast_zero, mul_zero],
    exact index_nonneg _ _ },
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := ih,
  by_cases huniform : P.is_uniform G ε,
  { refine ⟨P, hP₁, hP₂, _, or.inl huniform⟩,
    rw function.iterate_succ_apply',
    exact hP₃.trans (le_exp_bound _) },
  replace hP₄ := hP₄.resolve_left huniform,
  have hεl' : 100 < ε ^ 5 * 4 ^ P.size,
  { apply lt_of_lt_of_le (const_lt_mul_pow_iteration_bound hε l),
    rw mul_le_mul_left (pow_pos hε 5),
    refine pow_le_pow (by norm_num) hP₂ },
  have hi : (i : ℝ) ≤ 4 / ε^5,
  { have hi := hP₄.trans (index_le_half G P),
    rw [div_mul_eq_mul_div, div_le_iff (show (0:ℝ) < 8, by norm_num)] at hi,
    norm_num at hi,
    rwa le_div_iff' (pow_pos hε _) },
  have hsize : P.size ≤ (exp_bound^[nat_floor (4/ε^5)] t) :=
    hP₃.trans (iterate_le_iterate_of_id_le le_exp_bound (le_nat_floor_of_le hi) _),
  have hPV : P.size * 16^P.size ≤ card V :=
    (nat.mul_le_mul hsize (nat.pow_le_pow_of_le_right (by norm_num) hsize)).trans hV,
  refine ⟨hP₁.increment G ε, increment.is_equipartition hP₁ G ε, _, _,
    or.inr (le_trans _ (increment.index hP₁ hεl' hPV huniform))⟩,
  { rw increment.size hP₁ hεl' hPV huniform,
    exact hP₂.trans (le_exp_bound _) },
  { rw [increment.size hP₁ hεl' hPV huniform, function.iterate_succ_apply'],
    exact exp_bound_mono hP₃ },
  rw [nat.cast_succ, mul_add, mul_one],
  exact add_le_add_right hP₄ _,
end
