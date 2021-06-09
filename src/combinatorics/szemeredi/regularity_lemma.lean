/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.basic
import analysis.special_functions.exp_log
import analysis.special_functions.pow

/-!
# Szemerédi's Regularity Lemma

In this file, we define edge density, equipartitions, and prove Szemerédi's Regularity Lemma.
-/

universe u

open_locale big_operators
open finset fintype

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
  apply hxy.2
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

/-- The natural floor. Equal to ⌊x⌋ for positive numbers and to 0 for negative ones. -/
noncomputable def nat_floor (x : ℝ) : ℕ := ⌊x⌋.to_nat

lemma lt_nat_floor_add_one (x : ℝ) : x < nat_floor x + 1 :=
begin
  refine (lt_floor_add_one x).trans_le (add_le_add_right _ 1),
  norm_cast,
  exact int.le_to_nat _,
end

lemma le_nat_floor_of_le {n : ℕ} {x : ℝ} (h : ↑n ≤ x): n ≤ nat_floor x :=
begin
  have := int.le_to_nat n,
  norm_cast at this,
  refine this.trans (int.to_nat_le_to_nat _),
  rwa le_floor,
end

namespace real

lemma lt_pow_iff_log_lt {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) :
  a < b^c ↔ (log a) < c * (log b) :=
by rw [←log_lt_log_iff ha (rpow_pos_of_pos hb c), log_rpow hb]

lemma lt_pow_of_log_lt {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (h : log a < c * (log b)) :
  a < b^c :=
begin
  obtain ha | rfl := ha.lt_or_eq,
  { exact (lt_pow_iff_log_lt ha hb).2 h },
  exact rpow_pos_of_pos hb c,
end

lemma le_pow_iff_log_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) :
  a ≤ b^c ↔ log a ≤ c * (log b) :=
by rw [←log_le_log ha (rpow_pos_of_pos hb c), log_rpow hb]

lemma le_pow_of_log_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (h : log a ≤ c * (log b)) :
  a ≤ b^c :=
begin
  obtain ha | rfl := ha.lt_or_eq,
  { exact (le_pow_iff_log_le ha hb).2 h },
  exact (rpow_pos_of_pos hb c).le,
end

lemma le_exp_iff_log_le {a b : ℝ} (ha : 0 < a) :
  log a ≤ b ↔ a ≤ exp b :=
by rw [←exp_le_exp, exp_log ha]

end real

lemma lt_max_of_lt_right {α : Type*} [linear_order α] {a b c : α} (h : a < c) :
  a < max b c :=
lt_of_lt_of_le h (le_max_right b c)

lemma lt_max_of_lt_left {α : Type*} [linear_order α] {a b c : α} (h : a < b) :
  a < max b c :=
lt_of_lt_of_le h (le_max_left b c)

theorem abs_sub_le_abs_add_abs {α : Type*} [linear_ordered_add_comm_group α] (a b : α) :
  abs (a - b) ≤ abs a + abs b :=
begin
  rw [sub_eq_add_neg, ←abs_neg b],
  exact abs_add a _,
end

lemma iterate_extensive_of_extensive {α : Type} [preorder α] {f : α → α}
  (h : id ≤ f) :
  ∀ n, id ≤ (f^[n])
| 0 := by { rw function.iterate_zero, exact le_rfl }
| (n + 1) := λ x,
  begin
    rw function.iterate_succ_apply',
    apply le_trans (iterate_extensive_of_extensive n x) (h _),
  end

lemma iterate_le_of_extensive {α : Type} [preorder α] {f : α → α}
  (h : id ≤ f) {m n : ℕ} (hmn : m ≤ n) :
  f^[m] ≤ (f^[n]) :=
begin
  rw [←nat.add_sub_cancel' hmn, add_comm, function.iterate_add],
  intro x,
  apply iterate_extensive_of_extensive h (n-m) _,
end

/-! ### Prerequisites for SRL -/

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

lemma equitable_iff_almost_eq_constant {α : Type*} (s : set α) (f : α → ℕ) :
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
  rw equitable_iff_almost_eq_constant,
  split,
  { rintro ⟨b, hb⟩,
    by_cases h : ∀ a ∈ s, f a = b+1,
    { clear hb,
      intros a ha,
      left,
      symmetry,
      apply nat.div_eq_of_eq_mul_left (finset.card_pos.2 ⟨_, ha⟩),
      rw [mul_comm, sum_const_nat],
      intros c hc,
      rw [h _ ha, h _ hc] },
    { suffices : b = (∑ i in s, f i) / s.card,
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
      simp } },
  { intro h,
    refine ⟨_, h⟩ }
end

lemma equitable_on_finset_iff {α : Type*} (s : finset α) (f : α → ℕ) :
  equitable_on (s : set α) f ↔
    ∀ a ∈ s, (∑ i in s, f i) / s.card ≤ f a ∧ f a ≤ (∑ i in s, f i) / s.card + 1 :=
begin
  rw equitable_on_finset_iff_eq_average,
  simp_rw [between_nat_iff],
end

namespace simple_graph
variables {V : Type u} [decidable_eq V] (G : simple_graph V) [decidable_rel G.adj]

/-- Finset of edges between two finsets of vertices -/
def edges_pair_finset (U W : finset V) : finset (V × V) :=
(U.product W).filter (λ e, G.adj e.1 e.2)

lemma mem_edges_pair_finset (U W : finset V) (x : V × V) :
  x ∈ G.edges_pair_finset U W ↔ x.1 ∈ U ∧ x.2 ∈ W ∧ G.adj x.1 x.2 :=
by simp [edges_pair_finset, and_assoc]

lemma mem_edges_pair_finset' (U W : finset V) (x y : V) :
  (x, y) ∈ G.edges_pair_finset U W ↔ x ∈ U ∧ y ∈ W ∧ G.adj x y :=
mem_edges_pair_finset _ _ _ _

/-- Number of edges between two finsets of vertices -/
def edges_count_pair (U W : finset V) : ℕ :=
(G.edges_pair_finset U W).card

lemma edges_count_pair_symm (U W : finset V) :
  G.edges_count_pair U W = G.edges_count_pair W U :=
begin
  apply finset.card_congr (λ (i : V × V) hi, (i.2, i.1)) _ _ _,
  { rintro ⟨i, j⟩ h,
    simp only [mem_edges_pair_finset'] at h ⊢,
    rwa [G.edge_symm, and.left_comm] },
  { rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h₁ h₂ h,
    rcases h,
    refl },
  rintro ⟨i₁, j₁⟩ h,
  refine ⟨⟨j₁, i₁⟩, _, rfl⟩,
  simp only [mem_edges_pair_finset'] at h ⊢,
  rwa [G.edge_symm, and.left_comm],
end

/-- Number of edges between a pair of finsets of vertices. `sym2` variant of `edges_count_pair`. -/
def edges_count_sym2 : sym2 (finset V) → ℕ :=
quotient.lift (function.uncurry (edges_count_pair G))
  (by { rintros _ _ ⟨_, _⟩, { refl }, apply edges_count_pair_symm })

/-- Edge density between two finsets of vertices -/
noncomputable def density_pair (U W : finset V) : ℝ :=
G.edges_count_pair U W / (U.card * W.card)

lemma density_pair_symm (U W : finset V) : G.density_pair U W = G.density_pair W U :=
begin
  rw [density_pair, mul_comm, edges_count_pair_symm],
  refl
end

lemma density_pair_nonneg (U W : finset V) :
  0 ≤ G.density_pair U W :=
begin
  apply div_nonneg;
  exact_mod_cast nat.zero_le _,
end

lemma density_pair_le_one (U W : finset V) :
  G.density_pair U W ≤ 1 :=
begin
  refine div_le_one_of_le _ (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)),
  norm_cast,
  rw [edges_count_pair, edges_pair_finset, ←finset.card_product],
  exact finset.card_filter_le _ _,
end

/-- Edge density between a pair of finsets of vertices. `sym2` variant of `density_pair`. -/
noncomputable def density_sym2 : sym2 (finset V) → ℝ :=
quotient.lift (function.uncurry (density_pair G))
  (by { rintros _ _ ⟨_, _⟩, { refl }, apply density_pair_symm })

lemma density_sym2_nonneg (s : sym2 (finset V)) :
  0 ≤ G.density_sym2 s :=
quotient.induction_on s (λ xy, density_pair_nonneg _ _ _)

lemma density_sym2_le_one (s : sym2 (finset V)) :
  G.density_sym2 s ≤ 1 :=
quotient.induction_on s (λ xy, density_pair_le_one _ _ _)

private lemma mul_abs_density_sub_le_aux {A B A' B' : finset V} (hA : A' ⊆ A) (hB : B' ⊆ B) :
  (A.card : ℝ) * B.card * abs (G.density_pair A B - G.density_pair A' B') ≤
  A.card * B.card - A'.card * B'.card :=
begin
  obtain rfl | hA'nemp := A'.eq_empty_or_nonempty,
  {
    sorry
  },
  obtain rfl | hB'nemp := B'.eq_empty_or_nonempty,
  {
    sorry
  },
  have hABpos' : (0 : ℝ) < A'.card * B'.card := sorry,
  have hABpos : (0 : ℝ) < A.card * B.card := sorry,
  rw [density_pair, density_pair],
  rw div_sub_div _ _ hABpos.ne.symm hABpos'.ne.symm,
  rw abs_div,
  rw abs_mul,
  rw abs_of_nonneg hABpos.le,
  have := mul_div_mul_left _ (abs (A'.card * B'.card : ℝ)) hABpos.ne.symm, -- rw fails @Bhavik
  have : (A.card : ℝ) * B.card * (abs (G.edges_count_pair A B * (A'.card * B'.card) - A.card *
    B.card * G.edges_count_pair A' B')) / (A.card * B.card * abs (A'.card * B'.card)) =
    abs (G.edges_count_pair A B * (A'.card * B'.card) - A.card * B.card * G.edges_count_pair A' B')
    / (abs (A'.card * B'.card)) := sorry,
  sorry,
  sorry
  /-
  rw this,
  apply div_le_of_nonneg_of_le_mul,-/
end

lemma abs_density_sub_le {A B A' B' : finset V} (hA : A' ⊆ A) (hB : B' ⊆ B) :
  abs (G.density_pair A B - G.density_pair A' B') ≤ 1 - A'.card/A.card * (B'.card/B.card) :=
begin
  obtain rfl | hAnemp := A.eq_empty_or_nonempty,
  {
    sorry
  },
  obtain rfl | hBnemp := B.eq_empty_or_nonempty,
  {
    sorry
  },
  rw [density_pair, density_pair],
  rw div_sub_div,
  rw abs_div,
  apply div_le_of_nonneg_of_le_mul,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry
end

lemma LemmaB {A B A' B' : finset V} (hAnemp : A.nonempty) (hBnemp : B.nonempty) (hA : A' ⊆ A)
  (hB : B' ⊆ B) {δ : ℝ} (hA' : (1 - δ) * A.card ≤ A'.card) (hB' : (1 - δ) * B.card ≤ B'.card) :
  abs (G.density_pair A B - G.density_pair A' B') ≤ 2 * δ :=
begin
  cases le_total 1 δ,
  { apply (abs_sub_le_abs_add_abs _ _).trans,
    rw [abs_of_nonneg (G.density_pair_nonneg A B), abs_of_nonneg (G.density_pair_nonneg _ _),
      two_mul],
    exact add_le_add ((G.density_pair_le_one A B).trans h) ((G.density_pair_le_one _ _).trans h) },
  rw ←le_div_iff at hA' hB',
  { apply (G.abs_density_sub_le hA hB).trans,
    calc
    (1 : ℝ) - A'.card/A.card * (B'.card/B.card)
        ≤ 1 - (1 - δ) * (1 - δ)
        : sub_le_sub_left (mul_le_mul hA' hB' (sub_nonneg_of_le h) (div_nonneg (nat.cast_nonneg _)
          (nat.cast_nonneg _))) 1
    ... = 2 * δ - δ^2
        : by ring
    ... ≤ 2 * δ - 0
        : sub_le_sub_left (sq_nonneg δ) _
    ... = 2 * δ
        : by rw sub_zero },
  all_goals { rwa [nat.cast_pos, card_pos] },
end

/-- A pair of finsets of vertices is ε-uniform iff their edge density is close to the density of any
big enough pair of subsets. Intuitively, the edges between them are random-like. -/
def is_uniform (ε : ℝ) (U W : finset V) : Prop :=
∀ U', U' ⊆ U → ∀ W', W' ⊆ W → ε * U.card ≤ U'.card → ε * W.card ≤ W'.card →
abs (density_pair G U' W' - density_pair G U W) < ε

/-- If the pair `(U,W)` is `ε`-uniform and `ε ≤ ε'`, then it is `ε'`-uniform. -/
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
  rw density_pair_symm _ W',
  rw density_pair_symm _ W,
  apply h _ hU' _ hW' hU hW,
end

/-- `sym2` variant of `is_uniform` -/
def is_uniform_sym2 (ε : ℝ) : sym2 (finset V) → Prop :=
sym2.from_rel (is_uniform_symmetric G ε)

end simple_graph

/-- An partition of a finite set `S` is a collection of disjoint subsets of `S` which cover it. -/
@[ext]
structure finpartition {V : Type u} (s : finset V) :=
(parts : finset (finset V))
(disjoint : ∀ (a₁ a₂ ∈ parts) x, x ∈ a₁ → x ∈ a₂ → a₁ = a₂)
(covering : ∀ u ∈ s, ∃ (a ∈ parts), u ∈ a)
(subset : ∀ u ∈ parts, u ⊆ s)

/-- A `finpartition' V` is a partition of the entire finite type `V` -/
abbreviation finpartition' (V : Type u) [fintype V] := finpartition (univ : finset V)

namespace finpartition
variables {V : Type u} {s : finset V} [decidable_eq V] (P : finpartition s)

/-- The size of a finpartition is its number of parts. -/
protected def size : ℕ := P.parts.card

lemma bUnion_subset_of_forall_subset {α β : Type*} [decidable_eq β]
  {s : finset α} (t : finset β) (f : α → finset β) (h : ∀ x ∈ s, f x ⊆ t) : s.bUnion f ⊆ t :=
begin
  intros i hi,
  simp only [mem_bUnion, exists_prop] at hi,
  rcases hi with ⟨a, ha₁, ha₂⟩,
  apply h _ ha₁ ha₂
end

lemma union_eq : P.parts.bUnion id = s :=
begin
  apply subset.antisymm,
  { refine bUnion_subset_of_forall_subset _ _ (λ i, P.subset _) },
  { intros x hx,
    rw mem_bUnion,
    apply P.covering _ hx }
end

def is_equipartition : Prop :=
equitable_on (P.parts : set (finset V)) card

/-- `sym2` variant of `equipartition.parts`. We exclude the diagonal, as these do not make sense nor
behave well in the context of Szemerédi's Regularity Lemma. -/
def distinct_unordered_parts_pairs :
  finset (sym2 (finset V)) :=
((P.parts.product P.parts).image quotient.mk).filter (λ (a : sym2 _), ¬a.is_diag)

lemma mem_distinct_unordered_parts_pairs (U W : finset V) :
  ⟦(U, W)⟧ ∈ P.distinct_unordered_parts_pairs ↔ U ∈ P.parts ∧ W ∈ P.parts ∧ U ≠ W :=
begin
  rw [finpartition.distinct_unordered_parts_pairs, finset.mem_filter],
  simp only [mem_image, exists_prop, sym2.is_diag_iff_proj_eq, sym2.eq_iff, prod.exists,
    mem_product],
  split,
  { rintro ⟨⟨U, W, ⟨_, _⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, _⟩;
    exact ⟨‹_›, ‹_›, ‹_›⟩ },
  rintro ⟨h₁, h₂, h₃⟩,
  exact ⟨⟨_, _, ⟨h₁, h₂⟩, or.inl ⟨rfl, rfl⟩⟩, h₃⟩,
end

lemma distinct_unordered_parts_pairs_size :
  P.distinct_unordered_parts_pairs.card = P.size.choose 2 :=
by rw [distinct_unordered_parts_pairs, finpartition.size, prod_quotient_sym2_not_diag]

variables (G : simple_graph V)
open_locale classical

noncomputable def non_uniform_parts (ε : ℝ) :
  finset (sym2 (finset V)) :=
P.distinct_unordered_parts_pairs.filter (λ a, ¬G.is_uniform_sym2 ε a)

lemma mem_non_uniform_parts (U W : finset V) (ε : ℝ) :
  ⟦(U, W)⟧ ∈ P.non_uniform_parts G ε ↔ U ∈ P.parts ∧ W ∈ P.parts ∧ U ≠ W ∧ ¬G.is_uniform ε U W :=
begin
  rw [non_uniform_parts, mem_filter, mem_distinct_unordered_parts_pairs, and_assoc, and_assoc],
  refl
end

/-- An equipartition is ε-uniform iff at most a proportion of ε of its pairs of parts are
not ε-uniform. -/
def is_uniform (ε : ℝ) : Prop :=
((P.non_uniform_parts G ε).card : ℝ) ≤ ε * P.size.choose 2

/-- The index is the auxiliary quantity that drives the induction process in the proof of
Szemerédi's Regularity Lemma (see `increment`). As long as we do not have a suitable equipartition,
we will find a new one that has an index greater than the previous one plus some fixed constant.
Then `index_le_half` ensures this process only happens finitely many times. -/
noncomputable def index (P : finpartition s) : ℝ :=
(∑ x in P.distinct_unordered_parts_pairs, G.density_sym2 x^2)/P.size^2

lemma index_nonneg (P : finpartition s) :
  0 ≤ P.index G :=
div_nonneg (finset.sum_nonneg (λ _ _, sq_nonneg _)) (sq_nonneg _)

-- TODO: change for `choose_le_pow` once PR has landed
lemma nat.choose_le_pow (n k : ℕ) : (n.choose k : ℝ) ≤ n^k / (k.factorial) :=
begin
  sorry
  /-rw le_div_iff (show 0 < (2:ℝ), by norm_num),
  norm_cast,
  induction n with n ih,
  { simp },
  { rw [nat.choose_succ_succ, nat.choose_one_right, add_mul],
    apply le_trans (add_le_add_left ih _) _,
    rw [nat.succ_eq_one_add, add_sq, one_pow, add_assoc, mul_one, mul_comm 2 n],
    apply nat.le_add_left, }-/
end

lemma index_le_half (P : finpartition s) :
  P.index G ≤ 1/2 :=
begin
  rw finpartition.index,
  apply div_le_of_nonneg_of_le_mul (sq_nonneg _),
  { norm_num },
  suffices h : (∑ (x : sym2 (finset V)) in P.distinct_unordered_parts_pairs, G.density_sym2 x ^ 2) ≤
    P.distinct_unordered_parts_pairs.card,
  { apply h.trans,
    rw [distinct_unordered_parts_pairs_size, div_mul_eq_mul_div, one_mul],
    convert nat.choose_le_pow _ 2,
    norm_num },
  rw [finset.card_eq_sum_ones, sum_nat_cast, nat.cast_one],
  apply finset.sum_le_sum,
  rintro s _,
  rw [sq, ←abs_le_one_iff_mul_self_le_one, abs_eq_self.2 (G.density_sym2_nonneg _)],
  exact G.density_sym2_le_one _,
end

end finpartition

open finpartition

/-! ### Simple equipartitions -/

/-- The discrete equipartition of a fintype is the partition in singletons. -/
@[simps]
def discrete_finpartition {V : Type*} [decidable_eq V] (s : finset V) : finpartition s :=
{ parts := s.image singleton,
  disjoint :=
  begin
    simp only [mem_image, exists_true_left, exists_imp_distrib],
    rintro a₁ a₂ i hi rfl j hj rfl k,
    simp only [mem_singleton],
    rintro rfl rfl,
    refl
  end,
  covering := λ v hv, ⟨{v}, mem_image.2 ⟨v, hv, rfl⟩, finset.mem_singleton_self v⟩,
  subset := by simp }

@[simps]
def trivial_finpartition {V : Type*} [decidable_eq V] (s : finset V) : finpartition s :=
{ parts := {s},
  disjoint :=
  begin
    simp only [mem_singleton],
    rintro _ _ rfl rfl _ _ _,
    refl
  end,
  covering := λ u hu, ⟨s, mem_singleton_self _, hu⟩,
  subset := by simp }

namespace discrete_finpartition
variables {V : Type u} [decidable_eq V] (s : finset V) (G : simple_graph V)

lemma is_equipartition : (discrete_finpartition s).is_equipartition :=
(equitable_iff_almost_eq_constant _ _).2 ⟨1, by simp⟩

protected lemma size : (discrete_finpartition s).size = s.card :=
begin
  change finset.card (s.image _) = _,
  rw [finset.card_image_of_injective],
  intros i j k,
  rwa singleton_inj at k,
end

lemma non_uniform_parts {ε : ℝ} (hε : 0 < ε) :
  (discrete_finpartition s).non_uniform_parts G ε = ∅ :=
begin
  rw eq_empty_iff_forall_not_mem,
  intro z,
  apply quotient.induction_on z,
  rintro ⟨U, W⟩,
  simp only [finpartition.mem_non_uniform_parts, discrete_finpartition_parts, mem_image, and_imp,
    exists_prop, not_and, not_not, ne.def, exists_imp_distrib],
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
  (discrete_finpartition s).is_uniform G ε :=
begin
  rw [finpartition.is_uniform, discrete_finpartition.size, non_uniform_parts _ _ hε,
    finset.card_empty, nat.cast_zero],
  exact mul_nonneg hε.le (nat.cast_nonneg _),
end

end discrete_finpartition

section
variables {α : Type*} [decidable_eq α] {s : finset α}

lemma sdiff_ssubset {x y : finset α} (hx : y ⊆ x) (hy : y.nonempty) : x \ y ⊂ x :=
begin
  rcases hy with ⟨i, hi⟩,
  rw ssubset_iff_of_subset (sdiff_subset _ _),
  refine ⟨i, hx hi, λ t, (mem_sdiff.1 t).2 hi⟩,
end

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

lemma mk_equitable_aux (m a b : ℕ) (hs : a*m + b*(m+1) = s.card) (A : finset (finset α))
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
  { refine mk_equitable_aux1 hs A subs h },
  cases (nat.eq_zero_or_pos m) with h m_pos,
  { refine mk_equitable_aux2 hs A subs h },
  have : 0 < a ∨ 0 < b,
  { by_contra,
    push_neg at h,
    simp only [le_zero_iff] at h,
    rw [h.1, h.2] at hs,
    simp only [add_zero, zero_mul, eq_comm, card_eq_zero] at hs,
    apply hs_ne.ne_empty hs },
  set p'_size := if 0 < a then m else m+1 with h',
  have : 0 < p'_size,
  { rw h',
    split_ifs,
    { apply m_pos },
    { apply nat.succ_pos' } },
  by_cases ∃ p ∈ A, m+1 ≤ finset.card p,
  { rcases h with ⟨p, hp₁, hp₂⟩,
    have : p'_size ≤ p.card,
    { apply le_trans _ hp₂,
      rw h',
      split_ifs,
      { apply nat.le_succ },
      { refl } },
    obtain ⟨p', hp'₁, hp'₂⟩ := exists_smaller_set _ _ this,
    have : p'.nonempty,
    { rwa [←card_pos, hp'₂] },
    obtain ⟨P', hP'₁, hP'₂, hP'₃, hP'₄, hP'₅, hP'₆⟩ :=
      ih (s \ p')
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
      { obtain ⟨y, hy₁, hy₂⟩ := all x hx₁,
        refine ⟨y, or.inr ⟨λ t, _, hy₁⟩, hy₂⟩,
        apply h,
        rw ←t,
        apply hy₂ } },
    { simp only [mem_insert, mem_erase, ne.def],
      rintro x₁ x₂ (rfl | hx₁) (rfl | hx₂) i hi₁ hi₂,
      { refl },
      { apply (hx₂.1 (disj _ _ hx₂.2 hp₁ i hi₂ (sdiff_subset _ _ hi₁))).elim },
      { apply (hx₁.1 (disj _ _ hx₁.2 hp₁ i hi₁ (sdiff_subset _ _ hi₂))).elim },
      { apply disj _ _ hx₁.2 hx₂.2 _ hi₁ hi₂ } },
    { simp only [and_imp, mem_insert, forall_eq_or_imp, mem_erase, ne.def],
      split,
      { apply sdiff_subset_sdiff (subs _ hp₁) (refl _) },
      intros i hi₁ hi₂ x hx,
      simp only [mem_sdiff, subs i hi₂ hx, true_and],
      intro q,
      apply hi₁ (disj _ _ hi₂ hp₁ _ hx (hp'₁ q)) },
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
      { intros x hx,
        apply (card_le_of_subset _).trans (hP'₂ x (mem_insert_of_mem hx)),
        apply sdiff_subset_sdiff (finset.subset.refl _) (bUnion_subset_bUnion_of_subset_left _ _),
        refine filter_subset_filter _ (subset_insert _ _) } },
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
      { apply hP'₄ _ _ hx₁ hx₂ } },
    { simp only [mem_insert, forall_eq_or_imp],
      refine ⟨finset.subset.trans hp'₁ (subs _ hp₁),
        λ x hx i hi, (mem_sdiff.1 (hP'₅ x hx hi)).1⟩ },
    { rw [filter_insert, hp'₂, h'],
      by_cases 0 < a,
      { rw [if_pos h, if_neg, hP'₆, if_pos h],
        simp only [nat.one_ne_zero, self_eq_add_right, not_false_iff] },
      { rw [if_neg h, if_pos rfl, card_insert_of_not_mem, hP'₆, if_neg h, nat.sub_add_cancel],
        apply ‹0 < a ∨ 0 < b›.resolve_left h,
        simp only [mem_filter, hp'₂, h', if_neg h, eq_self_iff_true, and_true],
        intro t,
        obtain ⟨i, hi⟩ := ‹p'.nonempty›,
        apply (mem_sdiff.1 (hP'₅ _ t hi)).2 hi } } },
  { push_neg at h,
    have : p'_size ≤ s.card,
    { rw [←hs, h'],
      split_ifs,
      { apply le_add_right (nat.le_mul_of_pos_left ‹0 < a›) },
      { apply le_add_left (nat.le_mul_of_pos_left (‹0 < a ∨ 0 < b›.resolve_left ‹¬0 < a›)) } },
    obtain ⟨s', hs'₁, hs'₂⟩ := exists_smaller_set _ _ this,
    have : s'.nonempty,
    { rwa [←card_pos, hs'₂] },
    obtain ⟨P', hP'₁, hP'₂, hP'₃, hP'₄, hP'₅, hP'₆⟩ :=
      ih (s \ s')
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
      { rw [nat.mul_sub_right_distrib, one_mul, ←nat.add_sub_assoc],
        apply nat.le_mul_of_pos_left (‹0 < a ∨ 0 < b›.resolve_left ‹¬0 < a›) } },
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
      { right, refl } },
    { intros x hx,
      refine le_trans (card_le_of_subset (sdiff_subset _ _)) _,
      rw ←nat.lt_succ_iff,
      apply h _ hx },
    { intros x hx,
      by_cases x ∈ s',
      { refine ⟨_, by simp only [mem_insert, true_or, eq_self_iff_true], h⟩ },
      { obtain ⟨w, hw, hw'⟩ := hP'₃ x (by simp only [hx, h, mem_sdiff, not_false_iff, and_self]),
        refine ⟨w, by simp only [hw, mem_insert, or_true], hw'⟩ } },
    { simp only [mem_insert],
      rintro _ _ (rfl | hx₁) (rfl | hx₂) i hi₁ hi₂,
      { refl },
      { apply ((mem_sdiff.1 (hP'₅ _ hx₂ hi₂)).2 hi₁).elim },
      { apply ((mem_sdiff.1 (hP'₅ _ hx₁ hi₁)).2 hi₂).elim },
      { apply hP'₄ _ _ hx₁ hx₂ _ hi₁ hi₂ } },
    { simp only [hs'₁, true_and, mem_insert, forall_eq_or_imp],
      intros x hx,
      apply finset.subset.trans (hP'₅ x hx) (sdiff_subset _ _) },
    { rw [filter_insert, hs'₂, h'],
      by_cases 0 < a,
      { rw [if_pos h, if_neg, hP'₆, if_pos h],
        simp only [nat.one_ne_zero, self_eq_add_right, not_false_iff] },
      { rw [if_neg h, if_pos rfl, card_insert_of_not_mem, hP'₆, if_neg h, nat.sub_add_cancel],
        apply ‹0 < a ∨ 0 < b›.resolve_left h,
        simp only [mem_filter, hs'₂, h', if_neg h, eq_self_iff_true, and_true],
        intro t,
        obtain ⟨i, hi⟩ := ‹s'.nonempty›,
        apply (mem_sdiff.1 (hP'₅ _ t hi)).2 hi } } }
end.

/--
Given a partition `Q` of `s`, as well as a proof that `a*m + b*(m+1) = s.card`, build a new
partition `P` of `s` where each part has size `m` or `m+1`, every part of `Q` is the union of
parts of `P` plus at most `m` extra elements, there are `b` parts of size `m+1` and provided
`m > 0`, there are `a` parts of size `m` and hence `a+b` parts in total.
The `m > 0` condition is required since there may be zero or one parts of size `0`, while `a` could
be arbitrary.
-/
lemma mk_equitable {m a b : ℕ} (hs : a*m + b*(m+1) = s.card) (Q : finpartition s) :
  ∃ (P : finpartition s),
    (∀ (x : finset α), x ∈ P.parts → x.card = m ∨ x.card = m+1) ∧
    P.is_equipartition ∧
    (∀ x ∈ Q.parts, (x \ finset.bUnion (P.parts.filter (λ y, y ⊆ x)) id).card ≤ m) ∧
    ((P.parts.filter (λ i, finset.card i = m+1)).card = b) ∧
    (0 < m → (P.parts.filter (λ i, finset.card i = m)).card = a ∧ P.size = a+b) :=
begin
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄, hP₅, hP₆⟩ :=
    mk_equitable_aux m a b hs Q.parts Q.covering Q.disjoint Q.subset,
  let P' : finpartition s := ⟨P, hP₄, hP₃, hP₅⟩,
  have h₁ : ∑ i in P'.parts, i.card = s.card,
  { rw [←card_bUnion],
    { apply congr_arg finset.card P'.union_eq },
    intros x hx y hy t,
    rw disjoint_left,
    intros i hix hiy,
    apply t,
    apply hP₄ _ _ hx hy _ hix hiy },
  have h₂ :
    P'.parts.filter (λ i, i.card = m) ∪ P'.parts.filter (λ i, i.card = m+1) = P,
  { rw [←filter_or, filter_true_of_mem hP₁] },
  have h₃ : disjoint (P'.parts.filter (λ i, i.card = m)) (P'.parts.filter (λ i, i.card = m+1)),
  { simp only [disjoint_left, and_imp, mem_filter, not_and],
    intros x hx₁ hx₂ hx₃,
    rw hx₂,
    simp },
  have h₄ :
    ∑ i in P'.parts.filter (λ i, finset.card i = m), i.card +
      ∑ i in P'.parts.filter (λ i, finset.card i = m+1), i.card =
        s.card,
  { rw [←sum_union h₃, h₂, h₁] },
  have hm : ∀ (x : finset α), x ∈ filter (λ (i : finset α), i.card = m) P'.parts → x.card = m,
  { simp },
  have hm' : ∀ (x : finset α), x ∈ filter (λ (i : finset α), i.card = m+1) P'.parts → x.card = m+1,
  { simp },
  rw [sum_const_nat hm, sum_const_nat hm', hP₆, ←hs] at h₄,
  simp only [add_left_inj, mul_eq_mul_right_iff] at h₄,
  refine ⟨P', hP₁, _, hP₂, hP₆, λ t, _⟩,
  { change equitable_on _ _,
    rw equitable_iff_almost_eq_constant,
    refine ⟨m, hP₁⟩ },
  refine ⟨h₄.resolve_right t.ne', _⟩,
  change P.card = _,
  rw [←h₂, card_disjoint_union h₃, h₄.resolve_right t.ne', hP₆],
end

end

section
variables {α : Type*} [decidable_eq α] {s : finset α}

def atomise (s : finset α) (Q : finset (finset α)) :
  finset (finset α) :=
Q.powerset.image (λ P, s.filter (λ i, ∀ x ∈ Q, x ∈ P ↔ i ∈ x))

lemma mem_atomise {s : finset α} {Q : finset (finset α)} (A : finset α) :
  A ∈ atomise s Q ↔ ∃ (P ⊆ Q), s.filter (λ i, ∀ x ∈ Q, x ∈ P ↔ i ∈ x) = A :=
by simp only [atomise, mem_powerset, mem_image, exists_prop]

lemma atomise_empty : atomise s ∅ = {s} :=
begin
  rw [atomise],
  simp,
end

lemma atomise_disjoint {s : finset α} {Q : finset (finset α)} {x y : finset α}
  (hx : x ∈ atomise s Q) (hy : y ∈ atomise s Q) : disjoint x y ∨ x = y :=
begin
  rw or_iff_not_imp_left,
  simp only [disjoint_left, not_forall, and_imp, exists_prop, not_not, exists_imp_distrib],
  intros i hi₁ hi₂,
  simp only [mem_atomise] at hx hy,
  obtain ⟨P, hP, rfl⟩ := hx,
  obtain ⟨P', hP', rfl⟩ := hy,
  simp only [mem_filter] at hi₁ hi₂,
  have : P = P',
  { ext j,
    refine ⟨λ hj, _, λ hj, _⟩,
    { rwa [hi₂.2 _ (hP hj), ←hi₁.2 _ (hP hj)] },
    { rwa [hi₁.2 _ (hP' hj), ←hi₂.2 _ (hP' hj)] } },
  subst this
end

lemma atomise_covers {s : finset α} (Q : finset (finset α)) {x : α} (hx : x ∈ s) :
  ∃ Y ∈ atomise s Q, x ∈ Y :=
begin
  simp only [mem_atomise, exists_prop, mem_filter, exists_exists_and_eq_and],
  refine ⟨Q.filter (λ t, x ∈ t), filter_subset _ _, hx, λ y hy, _⟩,
  simp only [mem_filter, and_iff_right_iff_imp],
  intro,
  apply hy
end

lemma atomise_unique_covers {s : finset α} {Q : finset (finset α)} {x : α} (hx : x ∈ s) :
  ∃! Y ∈ atomise s Q, x ∈ Y :=
begin
  obtain ⟨Y, hY₁, hY₂⟩ := atomise_covers Q hx,
  apply exists_unique.intro2 Y hY₁ hY₂,
  intros Y' hY'₁ hY'₂,
  apply or.resolve_left (atomise_disjoint ‹Y' ∈ _› ‹Y ∈ _›),
  simp only [disjoint_left, exists_prop, not_not, not_forall],
  refine ⟨_, hY'₂, hY₂⟩,
end

lemma card_atomise {s : finset α} {Q : finset (finset α)} :
  (atomise s Q).card ≤ 2^Q.card :=
begin
  apply le_trans finset.card_image_le,
  simp,
end

lemma union_of_atoms_aux {s : finset α} {Q : finset (finset α)} {A : finset α}
  (hA : A ∈ Q) (hs : A ⊆ s) (i : α) :
  (∃ (B ∈ atomise s Q), B ⊆ A ∧ i ∈ B) ↔ i ∈ A :=
begin
  split,
  { rintro ⟨B, hB₁, hB₂, hB₃⟩,
    apply hB₂,
    apply hB₃ },
  { intro hi,
    simp only [exists_prop],
    rcases atomise_covers Q (hs hi) with ⟨B, hB₁, hB₂⟩,
    refine ⟨B, hB₁, _, hB₂⟩,
    rw [mem_atomise] at hB₁,
    rcases hB₁ with ⟨P, hP, rfl⟩,
    simp only [mem_filter] at hB₂,
    intros j hj,
    simp only [mem_filter] at hj,
    rwa [←hj.2 _ hA, hB₂.2 _ hA] }
end

lemma union_of_atoms {s : finset α} {Q : finset (finset α)} {A : finset α}
  (hA : A ∈ Q) (hs : A ⊆ s) :
  s.filter (λ i, ∃ B ∈ atomise s Q, B ⊆ A ∧ i ∈ B) = A :=
begin
  ext i,
  simp only [mem_filter, union_of_atoms_aux hA hs],
  { rw and_iff_right_iff_imp,
    apply hs }
end

instance {B : finset α} : decidable B.nonempty :=
decidable_of_iff' _ finset.nonempty_iff_ne_empty

lemma union_of_atoms' {s : finset α} {Q : finset (finset α)} (A : finset α)
  (hx : A ∈ Q) (hs : A ⊆ s) :
  ((atomise s Q).filter (λ B, B ⊆ A ∧ B.nonempty)).bUnion id = A :=
begin
  ext x,
  rw mem_bUnion,
  simp only [exists_prop, mem_filter, id.def, and_assoc],
  rw ←union_of_atoms_aux hx hs,
  simp only [exists_prop],
  refine exists_congr (λ a, and_congr_right (λ b, and_congr_right (λ c, _))),
  apply and_iff_right_of_imp,
  intro h,
  refine ⟨_, h⟩,
end

lemma partial_atomise {s : finset α} {Q : finset (finset α)} (A : finset α)
  (hA : A ∈ Q) (hs : A ⊆ s) :
  ((atomise s Q).filter (λ B, B ⊆ A ∧ B.nonempty)).card ≤ 2^(Q.card - 1) :=
begin
  have :
    (atomise s Q).filter (λ B, B ⊆ A ∧ B.nonempty) ⊆
      (Q.erase A).powerset.image (λ P, s.filter (λ i, ∀ x ∈ Q, x ∈ insert A P ↔ i ∈ x)),
  { rw subset_iff,
    simp only [mem_erase, mem_powerset, mem_image, exists_prop, mem_filter, and_assoc,
      finset.nonempty, exists_imp_distrib, and_imp, mem_atomise, forall_apply_eq_imp_iff₂],
    intros P PQ hA y hy₁ hy₂,
    refine ⟨P.erase A, erase_subset_erase _ PQ, _⟩,
    have : A ∈ P,
    { rw hy₂ _ ‹A ∈ Q›,
      apply hA,
      apply mem_filter.2 ⟨hy₁, hy₂⟩ },
    simp only [insert_erase this, filter_congr_decidable] },
  apply le_trans (card_le_of_subset this) (le_trans card_image_le _),
  rw [card_powerset, card_erase_of_mem hA],
  refl
end

end

/-- Arbitrary equipartition into `t` parts -/
lemma dummy_equipartition {V : Type*} [decidable_eq V] (s : finset V) {t : ℕ}
  (ht : 0 < t) (hs : t ≤ s.card) :
  ∃ (P : finpartition s), P.is_equipartition ∧ P.size = t :=
begin
  have : (t - s.card % t) * (s.card / t) + (s.card % t) * (s.card / t + 1) = s.card,
  { rw [nat.mul_sub_right_distrib, mul_add, ←add_assoc, nat.sub_add_cancel, mul_one, add_comm,
      nat.mod_add_div],
    apply nat.mul_le_mul_right,
    apply (nat.mod_lt _ ht).le },
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄, hP₅⟩ := mk_equitable this (trivial_finpartition s),
  have : 0 < s.card / t := nat.div_pos hs ht,
  refine ⟨P, hP₂, _⟩,
  rw [(hP₅ this).2, nat.sub_add_cancel (nat.mod_lt _ ht).le],
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

private lemma bound_mono_aux {ε : ℝ} {a b : ℕ} (hε : 100 < ε^5 * 4^a) (h : a ≤ b) :
  ε^5 * 4^a ≤ ε^5 * 4^b := sorry
--mul_le_mul_of_nonneg_left (pow_le_pow (by norm_num) h) (nonneg_of_mul_pos_right (lt_trans (by norm_num) hε) (pow_nonneg (by norm_num) a))
/-begin
  replace hε : 0 < ε^5 * 4^a := lt_trans (by norm_num) hε,
  refine mul_le_mul_of_nonneg_left (pow_le_pow (by norm_num) h) _,
  refine mul_le_mul_of_nonneg_left (pow_le_pow (by norm_num) h) (nonneg_of_mul_pos_right hε (pow_nonneg (by norm_num) a)),
  sorry,
  exact pow_nonneg (by norm_num) a,
  apply nonneg_of_mul_pos_right (lt_trans (by norm_num) hε : 0 < ε^5 * 4^a),
  sorry
end-/

open_locale classical
variables {V : Type u} [fintype V] {G : simple_graph V} {P : finpartition' V} {ε : ℝ}

/-- The work-horse of SRL. This says that if we have an equipartition which is *not* uniform, then
we can make a (much bigger) equipartition with a slightly higher index. This is helpful since the
index is bounded by a constant (see `index_le_half`), so this process eventually terminates and
yields a not-too-big uniform equipartition. -/
theorem increment (hP : P.is_equipartition)
  (hε : 100 < ε^5 * 4^P.size) (hPV : P.size * 16^P.size ≤ card V) (hPG : ¬P.is_uniform G ε) :
  ∃ (Q : finpartition' V),
    Q.is_equipartition ∧ Q.size = exp_bound P.size ∧ P.index G + ε^5 / 8 ≤ Q.index G :=
begin
  sorry
end

/-- The maximal number of times we need to blow up an equipartition to make it uniform -/
noncomputable def iteration_bound (ε : ℝ) (l : ℕ) : ℕ :=
max l (nat_floor (real.log (100/ε^5) / real.log 4) + 1) -- change to nat_floor

lemma le_iteration_bound (ε : ℝ) (l : ℕ) : l ≤ iteration_bound ε l := le_max_left l _
lemma iteration_bound_pos (ε : ℝ) (l : ℕ) : 0 < iteration_bound ε l :=
nat.succ_pos'.trans_le (le_max_right _ _)

lemma const_lt_mul_pow_iteration_bound {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
  100 < ε^5 * 4^iteration_bound ε l :=
begin
  rw [←real.rpow_nat_cast 4, ←div_lt_iff' (pow_pos hε 5), real.lt_pow_iff_log_lt, ←div_lt_iff,
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
  16^(exp_bound^[nat_floor (4/ε^5)] (iteration_bound ε l)) -- change to floor after PR

lemma iteration_bound_le_szemeredi_bound (ε l) :
  iteration_bound ε l ≤ szemeredi_bound ε l :=
(iterate_extensive_of_extensive le_exp_bound _ _).trans
  (nat.le_mul_of_pos_right (pow_pos (by norm_num) _))

/-- Effective Szemerédi's Regularity Lemma: For any sufficiently big graph, there is an ε-uniform
equipartition of bounded size (where the bound does not depend on the graph). -/
theorem szemeredi_regularity {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1) (l : ℕ) (hG : l ≤ card V) :
  ∃ (P : finpartition' V),
    P.is_equipartition ∧ l ≤ P.size ∧ P.size ≤ szemeredi_bound ε l ∧ P.is_uniform G ε :=
begin
  obtain hV | hV := le_total (card V) (szemeredi_bound ε l),
  { refine ⟨discrete_finpartition _, discrete_finpartition.is_equipartition _, _⟩,
    rw [discrete_finpartition.size, card_univ],
    exact ⟨hG, hV, discrete_finpartition.is_uniform _ G hε⟩ },
  let t := iteration_bound ε l,
  have ht : 0 < t := iteration_bound_pos _ _,
  suffices h : ∀ i, ∃ (P : finpartition' V), P.is_equipartition ∧
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
    hP₃.trans (iterate_le_of_extensive le_exp_bound (le_nat_floor_of_le hi) _),
  have hPV : P.size * 16^P.size ≤ card V :=
    (nat.mul_le_mul hsize (nat.pow_le_pow_of_le_right (by norm_num) hsize)).trans hV,
  obtain ⟨Q, hQ₁, hQ₂, hQ₃⟩ := increment hP₁ hεl' hPV huniform,
  refine ⟨Q, hQ₁, _, _, or.inr (le_trans _ hQ₃)⟩,
  { rw hQ₂,
    exact hP₂.trans (le_exp_bound _) },
  { rw [hQ₂, function.iterate_succ_apply'],
    exact exp_bound_mono hP₃ },
  rw [nat.cast_succ, mul_add, mul_one],
  exact add_le_add_right hP₄ _,
end
