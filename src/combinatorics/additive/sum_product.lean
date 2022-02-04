/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import analysis.special_functions.pow
import tactic.by_contra
import combinatorics.double_counting

/-!
# The sum-product problem

This file proves Elekes' bound on the sum-product problem following Solymosi's proof.
-/

open_locale pointwise big_operators

section
variables {α β : Type*} {A B : finset α}

lemma erase_eq_empty_iff [decidable_eq α] (a : α) : A.erase a = ∅ ↔ A = ∅ ∨ A = {a} :=
begin
  rw [←finset.sdiff_singleton_eq_erase, finset.sdiff_eq_empty_iff_subset],
  simp,
end

@[to_additive] lemma finset.left_le_card_mul [decidable_eq α] [right_cancel_semigroup α]
  {A B : finset α} (hB : B.nonempty) : A.card ≤ (A * B).card :=
let ⟨x, xB⟩ := hB
  in finset.card_le_card_of_inj_on (λ a, a * x) (λ a ha, finset.mul_mem_mul ha xB) (by simp)

lemma finset.left_le_card_mul' [decidable_eq α] [cancel_monoid_with_zero α]
  (A : finset α) {B : finset α} (hB : ∃ x ∈ B, x ≠ (0:α)) :
  A.card ≤ (A * B).card :=
let ⟨x, xB, xn⟩ := hB
in finset.card_le_card_of_inj_on (λ a, a * x) (λ a ha, finset.mul_mem_mul ha xB)
    (λ _ _ _ _, (mul_left_inj' xn).1)

@[to_additive] lemma finset.right_le_card_mul [decidable_eq α] [left_cancel_semigroup α]
  {A B : finset α} (hA : A.nonempty) :
  B.card ≤ (A * B).card :=
let ⟨x, xB⟩ := hA
  in finset.card_le_card_of_inj_on (λ a, x * a) (λ a ha, finset.mul_mem_mul xB ha) (by simp)

lemma finset.right_le_card_mul' [decidable_eq α] [cancel_monoid_with_zero α]
  (A : finset α) {B : finset α} (hB : ∃ x ∈ B, x ≠ (0:α)) :
  A.card ≤ (A * B).card :=
let ⟨x, xB, xn⟩ := hB
in finset.card_le_card_of_inj_on (λ a, a * x) (λ a ha, finset.mul_mem_mul ha xB)
    (λ _ _ _ _, (mul_left_inj' xn).1)

lemma sum_card_inter_le {α β : Type*} {s : finset α} {B : finset β}
  (g : β → α → Prop) [∀ b a, decidable (g b a)]
  {n : ℕ} (h : ∀ a ∈ s, (B.filter (λ b, g b a)).card ≤ n) :
  ∑ b in B, (s.filter (g b)).card ≤ s.card * n :=
(finset.sum_card_bipartite_above_eq_sum_card_bipartite_below _).le.trans (finset.sum_le_of_forall_le _ _ _ h)

end

lemma pow_left_monotone (n : ℕ) : monotone (λ (i:ℕ), i^n) := λ _ _ h, pow_le_pow_of_le_left' h _

noncomputable theory
open_locale classical

open finset

lemma real_covering₀_pos {ι : Type*} (s : finset ι) (x r : ι → ℝ)
  (disj : (s : set ι).pairwise (λ i j, r i ≤ abs (x i - x j))) :
  (s.filter (λ i, abs (x i) ≤ r i ∧ 0 < x i)).card ≤ 1 :=
begin
  rw card_le_one,
  simp only [and_imp, mem_filter],
  intros i hi₁ hi₂ hi₃ j hj₁ hj₂ hj₃,
  wlog : x i ≤ x j using i j,
  rw abs_of_pos hi₃ at hi₂,
  rw abs_of_pos hj₃ at hj₂,
  by_contra,
  have := disj hj₁ hi₁ (ne.symm h),
  rw abs_of_nonneg (sub_nonneg_of_le case) at this,
  apply not_le_of_lt hi₃ ((le_sub_self_iff _).1 (hj₂.trans this)),
end

lemma real_covering₀_neg {ι : Type*} (s : finset ι) (x r : ι → ℝ)
  (disj : (s : set ι).pairwise (λ i j, r i ≤ abs (x i - x j))) :
  (s.filter (λ i, abs (x i) ≤ r i ∧ x i < 0)).card ≤ 1 :=
begin
  convert real_covering₀_pos s (λ i, - x i) r _,
  { simp },
  refine disj.imp (λ a b hab, _),
  rwa [neg_sub_neg, abs_sub_comm],
end

lemma real_covering₀_zero {ι : Type*} (s : finset ι) {x r : ι → ℝ} (hr : ∀ i ∈ s, 0 < r i)
  (disj : (s : set ι).pairwise (λ i j, r i ≤ abs (x i - x j))) :
  (s.filter (λ i, abs (x i) ≤ r i ∧ x i = 0)).card ≤ 1 :=
begin
  rw card_le_one,
  simp only [and_imp, mem_filter],
  intros i hi₁ hi₂ hi₃ j hj₁ hj₂ hj₃,
  by_contra,
  apply not_le_of_lt (hr i hi₁),
  simpa [hi₃, hj₃] using disj hi₁ hj₁ h,
end

lemma real_covering₀ {ι : Type*} (s : finset ι) (x r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i)
  (disj : (s : set ι).pairwise (λ i j, r i ≤ abs (x i - x j))) :
  (s.filter (λ i, abs (x i) ≤ r i)).card ≤ 3 :=
begin
  apply le_trans _ (add_le_add_three (real_covering₀_neg s x r disj) (real_covering₀_pos s x r disj)
    (real_covering₀_zero s hr disj)),
  refine le_trans _ (add_le_add_right (card_union_le _ _) _),
  refine (card_le_of_subset _).trans (card_union_le _ _),
  intros i hi,
  rw [←filter_filter, ←filter_filter, ←filter_filter, filter_union_right, filter_union_right],
  rw mem_filter,
  refine ⟨hi, _⟩,
  simp only [lt_or_lt_iff_ne, em'],
end

lemma real_covering {ι : Type*} (s : finset ι) (x r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i)
  (disj : (s : set ι).pairwise (λ i j, r i ≤ abs (x i - x j))) (z : ℝ) :
  (s.filter (λ i, abs (x i - z) ≤ r i)).card ≤ 3 :=
begin
  apply real_covering₀ s (λ i, x i - z) r hr,
  simpa,
end

def finset.is_neighbouring (A : finset ℝ) (a a' : ℝ) : Prop :=
  a' ≠ a ∧ ∀ a'' ∈ A, abs (a'' - a) < abs (a' - a) → a = a''

lemma finset.is_neighbouring.le_of_ne {A : finset ℝ} {a a' a'' : ℝ} (hA : A.is_neighbouring a a') :
  a'' ∈ A → a ≠ a'' → abs (a' - a) ≤ abs (a'' - a) :=
begin
  intros ha'' i,
  rw ←not_lt,
  intro t,
  apply i (hA.2 _ ha'' t),
end

lemma finset.exists_is_neighbouring (A : finset ℝ) {a : ℝ} (hA : (A.erase a).nonempty):
  ∃ a' ∈ A, A.is_neighbouring a a' :=
begin
  obtain ⟨a', ha', ha''⟩ := (A.erase a).exists_min_image (λ a'', abs (a'' - a)) hA,
  simp only [ne.def, mem_erase] at ha',
  refine ⟨a', ha'.2, ha'.1, λ i hi hi', _⟩,
  by_contra,
  apply not_le_of_lt hi',
  exact ha'' i (mem_erase.2 ⟨ne.symm h, hi⟩),
end

def finset.neighbour (A : finset ℝ) (a : ℝ) : ℝ :=
if h : (A.erase a).nonempty
  then (A.exists_is_neighbouring h).some
  else a + 1

lemma neighbour_spec {A : finset ℝ} {a : ℝ} (h : (A.erase a).nonempty) :
  A.neighbour a ∈ A ∧ A.is_neighbouring a (A.neighbour a) :=
begin
  rw [finset.neighbour, dif_pos h],
  simpa using (A.exists_is_neighbouring h).some_spec,
end

lemma neighbour_ne {A : finset ℝ} {a : ℝ} : A.neighbour a ≠ a :=
begin
  by_cases (A.erase a).nonempty,
  { apply (neighbour_spec h).2.1 },
  rw [finset.neighbour, dif_neg h],
  simp,
end

def nearest_neighbours (A : finset ℝ) (a : ℝ) (n : ℕ) : finset ℝ :=
nat.rec_on n ∅ $ λ _ B,
  if h : (A \ B).nonempty
    then insert (exists_min_image _ (λ a', |a - a'|) h).some B
    else B

@[simp] lemma nearest_neighbours_zero {A a} :
  nearest_neighbours A a 0 = ∅ := rfl

lemma nearest_neighbours_succ_pos {A : finset ℝ} {a : ℝ} {n : ℕ}
  (h : (A \ nearest_neighbours A a n).nonempty) :
  nearest_neighbours A a (n+1) =
    insert (exists_min_image _ (λ a', |a - a'|) h).some (nearest_neighbours A a n) :=
dif_pos h

lemma nearest_neighbours_succ_neg {A : finset ℝ} {a : ℝ} {n : ℕ}
  (h : ¬(A \ nearest_neighbours A a n).nonempty) :
  nearest_neighbours A a (n+1) = nearest_neighbours A a n :=
dif_neg h

lemma nearest_neighbours_subset {A a n} : nearest_neighbours A a n ⊆ A :=
begin
  induction n with n ih,
  { simp },
  by_cases h : (A \ nearest_neighbours A a n).nonempty,
  { simp only [nearest_neighbours_succ_pos h, insert_subset, ih, and_true],
    apply sdiff_subset _ _ (exists_min_image _ (λ a', |a - a'|) h).some_spec.some },
  { rwa nearest_neighbours_succ_neg h }
end

lemma card_nearest_neighbours_eq {A : finset ℝ} {a : ℝ} {n : ℕ} :
  (nearest_neighbours A a n).card = min A.card n :=
begin
  rw eq_comm,
  induction n with n ih,
  { simp },
  by_cases h : (A \ nearest_neighbours A a n).nonempty,
  { rw [nearest_neighbours_succ_pos h, card_insert_of_not_mem
      (mem_sdiff.1 (exists_min_image _ (λ a', |a - a'|) h).some_spec.some).2],
    rw [←card_pos, card_sdiff nearest_neighbours_subset, tsub_pos_iff_lt] at h,
    simp only [min_eq_iff, h.ne', false_and, false_or] at ih,
    rw [←ih.1, min_eq_right],
    apply nat.succ_le_of_lt,
    rwa ←ih.1 at h },
  { rw nearest_neighbours_succ_neg h,
    simp only [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at h,
    have : nearest_neighbours A a n = A := nearest_neighbours_subset.antisymm h,
    rw this at *,
    rw [min_eq_left_iff, ←ih],
    apply (min_le_right _ _).trans (nat.le_succ _) }
end

lemma card_nearest_neighbours_le {A : finset ℝ} {a : ℝ} {n : ℕ} :
  (nearest_neighbours A a n).card ≤ n :=
begin
  rw card_nearest_neighbours_eq,
  apply min_le_right,
end

lemma nearest_neighbours_subset_succ {A a n} :
  nearest_neighbours A a n ⊆ nearest_neighbours A a (n+1) :=
begin
  by_cases h : (A \ nearest_neighbours A a n).nonempty,
  { rw [nearest_neighbours_succ_pos h],
    apply subset_insert },
  { rw [nearest_neighbours_succ_neg h],
    simp }
end

lemma nearest_neighbours_down_closed {A : finset ℝ} {a : ℝ} {n : ℕ} :
  ∀ x y, x ∈ nearest_neighbours A a n → y ∈ A → |a - y| < |a - x| →
    y ∈ nearest_neighbours A a n :=
begin
  induction n with n ih,
  { simp },
  intros x y,
  by_cases h : (A \ nearest_neighbours A a n).nonempty,
  { rw [nearest_neighbours_succ_pos h, mem_insert, mem_insert],
    rintro (hx | hx) hy hxy,
    { by_contra' q,
      have := (exists_min_image _ (λ a', |a - a'|) h).some_spec,
      rw [exists_prop, ←hx] at this,
      dsimp at this,
      apply not_le_of_lt hxy (this.2 y (by simp [hy, q.2])) },
    apply or.inr (ih _ _ hx hy hxy) },
  { rw [nearest_neighbours_succ_neg h],
    apply ih }
end

variables {A B Q : finset ℝ}

def add_good_triple (A B : finset ℝ) (a b : ℝ) : Prop :=
(((A + B).filter (λ u, |a + b - u| ≤ |A.neighbour a - a|)).card : ℝ) ≤
  (12 * (A + B).card / A.card : ℝ)

def mul_good_triple (A Q : finset ℝ) (a q : ℝ) : Prop :=
(((A * Q).filter (λ v, abs (a * q - v) ≤ abs (A.neighbour a * q - a * q))).card : ℝ) ≤
  (12 * (A * Q).card / A.card : ℝ)

lemma add_good_triple_set_subset_nearest_neighbours {a b : ℝ}
  (hA : (A.erase a).nonempty) (hB : b ∈ B) :
  ((A + B).filter (λ u, |a + b - u| ≤ |A.neighbour a - a|)).card ≤ 12 * ((A + B).card) / (A.card) →
  A.neighbour a + b ∈ nearest_neighbours (A + B) (a + b) (12 * (A + B).card / A.card) :=
begin
  intro h,
  set U₁ := (A + B).filter (λ u, |a + b - u| ≤ |A.neighbour a - a|),
  set U₂ := nearest_neighbours (A + B) (a + b) (12 * (A + B).card / A.card),
  have U₁₂ : U₁ ⊆ U₂ ∨ U₂ ⊆ U₁,
  { by_contra q,
    simp only [not_or_distrib, subset_iff, not_forall, exists_prop] at q,
    obtain ⟨⟨x, hx₁, hx₂⟩, y, hy₁, hy₂⟩ := q,
    cases lt_or_le (|a + b - x|) (|a + b - y|) with xy yx,
    { apply hx₂ (nearest_neighbours_down_closed y x hy₁ (filter_subset _ _ hx₁) xy) },
    { apply hy₂,
      rw mem_filter,
      refine ⟨nearest_neighbours_subset hy₁, _⟩,
      apply yx.trans,
      rw [mem_filter] at hx₁,
      apply hx₁.2 } },
  have : U₁ ⊆ U₂,
  { suffices : ¬ U₂ ⊂ U₁,
    { rw finset.ssubset_iff_subset_ne at this,
      simp only [not_and_distrib, not_not] at this,
      cases this,
      { apply U₁₂.resolve_right this },
      apply ge_of_eq this },
    intro t,
    apply not_le_of_lt (card_lt_card t),
    rw [card_nearest_neighbours_eq, le_min_iff],
    exact ⟨card_filter_le _ _, h⟩ },
  apply this,
  simp only [mem_filter, add_sub_add_right_eq_sub, abs_sub_comm a, le_refl, and_true],
  apply add_mem_add (neighbour_spec hA).1 hB,
end

lemma mul_good_triple_set_subset_nearest_neighbours {a q : ℝ}
  (hA : (A.erase a).nonempty) (hQ : q ∈ Q) :
  ((A * Q).filter (λ v, |a * q - v| ≤ |A.neighbour a * q - a * q|)).card ≤ 12 * ((A * Q).card) / (A.card) →
  A.neighbour a * q ∈ nearest_neighbours (A * Q) (a * q) (12 * (A * Q).card / A.card) :=
begin
  intro h,
  set U₁ := (A * Q).filter (λ v, |a * q - v| ≤ |A.neighbour a * q - a * q|),
  set U₂ := nearest_neighbours (A * Q) (a * q) (12 * (A * Q).card / A.card),
  have U₁₂ : U₁ ⊆ U₂ ∨ U₂ ⊆ U₁,
  { by_contra q,
    simp only [not_or_distrib, subset_iff, not_forall, exists_prop] at q,
    obtain ⟨⟨x, hx₁, hx₂⟩, y, hy₁, hy₂⟩ := q,
    cases lt_or_le (|a * q - x|) (|a * q - y|) with xy yx,
    { apply hx₂ (nearest_neighbours_down_closed y x hy₁ (filter_subset _ _ hx₁) xy) },
    { apply hy₂,
      rw mem_filter,
      refine ⟨nearest_neighbours_subset hy₁, _⟩,
      apply yx.trans,
      rw [mem_filter] at hx₁,
      apply hx₁.2 } },
  have : U₁ ⊆ U₂,
  { suffices : ¬ U₂ ⊂ U₁,
    { rw finset.ssubset_iff_subset_ne at this,
      simp only [not_and_distrib, not_not] at this,
      cases this,
      { apply U₁₂.resolve_right this },
      apply ge_of_eq this },
    intro t,
    apply not_le_of_lt (card_lt_card t),
    rw [card_nearest_neighbours_eq, le_min_iff],
    exact ⟨card_filter_le _ _, h⟩ },
  apply this,
  simp only [mem_filter, add_sub_add_right_eq_sub, abs_sub_comm (a * q), le_refl, and_true],
  apply mul_mem_mul (neighbour_spec hA).1 hQ,
end

def good_triple (A B Q : finset ℝ) (a b q : ℝ) : Prop :=
add_good_triple A B a b ∧ mul_good_triple A Q a q

lemma add_sum_le (A B : finset ℝ) (b : ℝ) :
  ∑ a in A, ((A + B).filter (λ u, abs (a + b - u) ≤ |A.neighbour a - a|)).card
    ≤ 3 * (A + B).card := -- should be 7 *
begin
  rw mul_comm,
  apply sum_card_inter_le _ (λ u hu, _),
  apply real_covering,
  { intros i hi,
    rw [abs_pos, sub_ne_zero],
    apply neighbour_ne },
  simp only [add_sub_add_right_eq_sub],
  intros i hi j hj diff,
  rw abs_sub_comm i,
  apply (neighbour_spec _).2.le_of_ne hj diff,
  exact ⟨j, mem_erase.2 ⟨diff.symm, hj⟩⟩,
end

-- if Q = {0} and q = 0 and A is big this breaks
lemma mul_sum_le (A : finset ℝ) (q : ℝ) (hQ : Q ≠ {0}) :
  ∑ a in A, ((A * Q).filter (λ v, abs (a * q - v) ≤ abs (A.neighbour a * q - a * q))).card
    ≤ 3 * (A * Q).card := -- should be 7 *
begin
  rcases eq_or_ne q 0 with rfl | hq,
  { simp only [abs_nonpos_iff, algebra.id.smul_eq_mul, zero_sub, sum_const, abs_neg,
      abs_zero, filter_congr_decidable, mul_zero],
    rcases Q.eq_empty_or_nonempty with rfl | hQ',
    { simp },
    have : ¬(Q ⊆ {0}),
    { simp only [subset_singleton_iff, not_or_distrib, hQ, not_false_iff, and_true],
      apply hQ'.ne_empty },
    have : ∃ x ∈ Q, x ≠ (0:ℝ),
    { simpa [subset_iff] using this },
    rw mul_comm,
    apply nat.mul_le_mul _ (finset.left_le_card_mul' A this),
    apply le_trans _ (show 1 ≤ 3, by norm_num),
    { rw card_le_one,
      simp only [and_imp, mem_filter],
      rintro a - rfl b - rfl,
      refl } },
  rw mul_comm 3,
  apply sum_card_inter_le _ (λ u hu, _),
  apply real_covering,
  { intros i hi,
    rw [←sub_mul, abs_mul],
    apply mul_pos,
    { rw [abs_pos, sub_ne_zero],
      apply neighbour_ne },
    rwa abs_pos },
  intros i hi j hj diff,
  rw [←sub_mul, ←sub_mul, abs_mul, abs_mul, abs_sub_comm i],
  refine mul_le_mul_of_nonneg_right _ (abs_nonneg _),
  apply (neighbour_spec _).2.le_of_ne hj diff,
  exact ⟨j, by simpa [diff.symm] using hj⟩,
end

lemma many_mul_good_triple {q : ℝ} (hQ : Q ≠ {0}) (hQ' : Q.nonempty) :
  ((A.filter (λ a, ¬mul_good_triple A Q a q)).card : ℝ) ≤ 1/4 * (A.card : ℝ) :=
begin
  rcases A.eq_empty_or_nonempty with rfl | hA,
  { simp },
  have hA' : (0 : ℝ) < A.card, rwa [nat.cast_pos, card_pos],
  have hQ'' : (0 : ℝ) < (A * Q).card,
  { simp [mul_nonempty_iff, hA, hQ', card_pos] },
  rw ←not_lt,
  intro h,
  apply not_le_of_lt _ (mul_sum_le A q hQ),
  apply lt_of_lt_of_le _ (sum_le_sum_of_subset (filter_subset (λ a, ¬mul_good_triple A Q a q) _)),
  suffices :
    (3:ℝ) * (A * Q).card < ∑ (x : ℝ) in filter (λ (a : ℝ), ¬mul_good_triple A Q a q) A,
      (filter (λ (v : ℝ), |x * q - v| ≤ |A.neighbour x * q - x * q|) (A * Q)).card,
  { exact_mod_cast this },
  have : ∀ x ∈ A.filter (λ (a : ℝ), ¬mul_good_triple A Q a q), 12 * ((A * Q).card : ℝ) / A.card ≤
      (filter (λ (v : ℝ), |x * q - v| ≤ |A.neighbour x * q - x * q|) (A * Q)).card,
  { intros a ha,
    simp only [mem_filter] at ha,
    apply (not_le.1 ha.2).le },
  apply lt_of_lt_of_le _ (le_sum_of_forall_le _ _ _ this),
  rw nsmul_eq_mul,
  rw mul_div_assoc',
  rw lt_div_iff hA',
  rw mul_right_comm,
  rw ←mul_assoc,
  apply mul_lt_mul_of_pos_right _ hQ'',
  linarith [h]
end

lemma many_add_good_triple {b : ℝ} (hB : B.nonempty) :
  ((A.filter (λ a, ¬add_good_triple A B a b)).card : ℝ) ≤ 1/4 * (A.card : ℝ) :=
begin
  rcases A.eq_empty_or_nonempty with rfl | hA,
  { simp },
  have hA' : (0 : ℝ) < A.card, rwa [nat.cast_pos, card_pos],
  have hB'' : (0 : ℝ) < (A + B).card,
  { simp [add_nonempty_iff, hA, hB, card_pos] },
  rw ←not_lt,
  intro h,
  apply not_le_of_lt _ (add_sum_le A B b),
  apply lt_of_lt_of_le _ (sum_le_sum_of_subset (filter_subset (λ a, ¬add_good_triple A B a b) _)),
  suffices :
    (3:ℝ) * (A + B).card < ∑ (x : ℝ) in filter (λ (a : ℝ), ¬add_good_triple A B a b) A,
      (filter (λ (u : ℝ), |x + b - u| ≤ |A.neighbour x - x|) (A + B)).card,
  { exact_mod_cast this },
  have : ∀ x ∈ A.filter (λ (a : ℝ), ¬add_good_triple A B a b), 12 * ((A + B).card : ℝ) / A.card ≤
      (filter (λ (u : ℝ), |x + b - u| ≤ |A.neighbour x - x|) (A + B)).card,
  { intros a ha,
    simp only [mem_filter] at ha,
    exact_mod_cast (not_le.1 ha.2).le },
  apply lt_of_lt_of_le _ (le_sum_of_forall_le _ _ _ this),
  rw [nsmul_eq_mul, mul_div_assoc', lt_div_iff hA', mul_right_comm, ←mul_assoc],
  apply mul_lt_mul_of_pos_right _ hB'',
  linarith [h]
end

lemma many_good_quad (A B Q : finset ℝ) {b q : ℝ} (hB : B.nonempty)
  (hQ : Q.nonempty) (hQ' : Q ≠ {0}):
  (1/2) * (A.card : ℝ) ≤ (A.filter (λ a, good_triple A B Q a b q)).card :=
begin
  suffices : ((A.filter (λ a, ¬good_triple A B Q a b q)).card : ℝ) ≤ 1/2 * (A.card : ℝ),
  { rw [←add_le_add_iff_right ((A.filter (λ a, ¬good_triple A B Q a b q)).card : ℝ),
      ←nat.cast_add, ←card_disjoint_union, filter_union_filter_neg_eq, ←le_sub_iff_add_le'],
    { apply this.trans,
      rw [le_sub_iff_add_le', ←add_mul],
      norm_num },
    rw [disjoint_iff_inter_eq_empty, filter_inter_filter_neg_eq] },
  have : ∀ a, ¬good_triple A B Q a b q ↔ ¬add_good_triple A B a b ∨ ¬mul_good_triple A Q a q,
  { intro a,
    simp only [good_triple, not_and_distrib] },
  simp_rw [this],
  rw filter_or,
  refine le_trans (nat.cast_le.2 (card_union_le _ _)) _,
  rw nat.cast_add,
  apply le_trans (add_le_add (many_add_good_triple hB) (many_mul_good_triple hQ' hQ)) _,
  rw ←add_mul,
  norm_num,
end

def good_triples (A B Q : finset ℝ) : finset (ℝ × ℝ × ℝ) :=
  ((A.product (B.product Q)).filter (λ (abq : ℝ × ℝ × ℝ), good_triple A B Q abq.1 abq.2.1 abq.2.2))

lemma many_good_triples (A B Q : finset ℝ) (hB : B.nonempty)
  (hQ : Q.nonempty) (hQ' : Q ≠ {0}):
  A.card * B.card * Q.card ≤ (good_triples A B Q).card * 2 :=
begin
  rw [mul_assoc, ←card_product],
  have : (good_triples A B Q).card =
    ((B.product Q).sigma (λ bq, A.filter (λ a, good_triple A B Q a bq.1 bq.2))).card,
  { rw eq_comm,
    refine card_congr (λ abq _, ⟨abq.2, abq.1⟩) _ _ _,
    { simp only [good_triples, and_imp, prod.forall, mem_filter, sigma.forall, mem_sigma,
        mem_product],
      tauto },
    { rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩,
      simp only [mem_sigma, mem_product, prod.mk.inj_iff, and_imp, mem_filter, heq_iff_eq],
      tauto },
    rintro ⟨a, b, q⟩,
    simp only [good_triples, mem_filter, mem_product, exists_prop, mem_sigma, and_assoc],
    rintro ⟨ha, hb, hq, h⟩,
    exact ⟨⟨⟨b, q⟩, a⟩, hb, hq, ha, h, rfl⟩ },
  rw [this, card_sigma, mul_comm, sum_mul],
  apply le_sum_of_forall_le,
  rintro ⟨b, q⟩ -,
  suffices : (A.card : ℝ) ≤ (A.filter (λ a, good_triple A B Q a b q)).card * 2,
  { exact_mod_cast this },
  rw [←div_le_iff, div_eq_mul_one_div, mul_comm],
  apply many_good_quad _ _ _ hB hQ hQ',
  exact zero_lt_two
end

lemma inj_on_aux_q {a b q x y z w : ℝ} (hx : x = a + b) (hy : y = A.neighbour a + b)
  (hz : z = a * q) (hw : w = A.neighbour a * q) : q = (w - z) / (y - x) :=
begin
  have : w - z = (A.neighbour a - a) * q,
  { rw [sub_mul, ←hw, ←hz] },
  rw this,
  have : y - x = A.neighbour a - a,
  { rw [hy, hx, add_sub_add_right_eq_sub] },
  rw [this, mul_div_cancel_left],
  rw sub_ne_zero,
  apply neighbour_ne,
end

lemma inj_on_aux_a {a b q x y z w : ℝ} (hx : x = a + b) (hy : y = A.neighbour a + b)
  (hz : z = a * q) (hw : w = A.neighbour a * q) (hq : q ≠ 0) :
  a = z * (y - x) / (w - z) :=
by rw [mul_div_assoc, ←inv_div, ←inj_on_aux_q hx hy hz hw, eq_mul_inv_iff_mul_eq₀ hq, hz]

def three_to_four_map (A : finset ℝ) : ℝ × ℝ × ℝ → (ℝ × ℝ) × ℝ × ℝ :=
λ ⟨a, b, q⟩, ⟨⟨a + b, A.neighbour a + b⟩, a * q, A.neighbour a * q⟩

lemma three_to_four_map_inj_on (hQ : (0 : ℝ) ∉ Q) :
  set.inj_on (three_to_four_map A) (A.product (B.product Q)) :=
begin
  rintro ⟨a₁, b₁, q₁⟩ h₁ ⟨a₂, b₂, q₂⟩ h₂ t,
  simp only [mem_coe, mem_product] at h₁ h₂,
  simp only [three_to_four_map, prod.mk.inj_iff] at t,
  simp only [prod.mk.inj_iff],
  have : q₁ = q₂,
  { rw inj_on_aux_q t.1.1 t.1.2 t.2.1 t.2.2,
    apply inj_on_aux_q rfl rfl rfl rfl },
  subst q₁,
  have : q₂ ≠ 0 := ne_of_mem_of_not_mem h₁.2.2 hQ,
  have : a₁ = a₂,
  { rw inj_on_aux_a t.1.1 t.1.2 t.2.1 t.2.2 this,
    apply inj_on_aux_a rfl rfl rfl rfl this },
  subst a₁,
  simpa using t.1,
end

def good_quads (A B Q : finset ℝ) : finset ((ℝ × ℝ) × ℝ × ℝ) :=
(good_triples A B Q).image (three_to_four_map A)

lemma good_quads_card (hQ : (0:ℝ) ∉ Q) : (good_quads A B Q).card = (good_triples A B Q).card :=
begin
  rw [good_quads, card_image_of_inj_on],
  exact set.inj_on.mono (coe_subset.2 (filter_subset _ _)) (three_to_four_map_inj_on hQ),
end

def left_good_quads (A B Q : finset ℝ) : finset (ℝ × ℝ) := (good_quads A B Q).image prod.fst
def right_good_quads (A B Q : finset ℝ) : finset (ℝ × ℝ) := (good_quads A B Q).image prod.snd

lemma left_good_quads_subset (hA : 2 ≤ A.card) :
  (left_good_quads A B Q).card ≤
    ((A + B).sigma (λ u, nearest_neighbours (A + B) u (12 * (A+B).card / A.card))).card :=
begin
  refine card_le_card_of_inj_on _ _ _,
  { rintro x,
    exact ⟨x.1, x.2⟩ },
  { simp only [left_good_quads, mem_image, mem_sigma, and_imp, exists_prop, prod.forall,
      forall_exists_index, exists_and_distrib_right, prod.mk.inj_iff, prod.exists, good_quads,
      good_triples, three_to_four_map, mem_filter, good_triple, add_good_triple, mem_product],
    rintro _ _ _ _ _ _ a b q ha hb hq hU - rfl rfl rfl rfl rfl rfl,
    refine ⟨add_mem_add ha hb, _⟩,
    rw ←nat.le_floor_iff at hU,
    apply add_good_triple_set_subset_nearest_neighbours _ hb,
    { apply hU.trans (le_of_eq _),
      convert nat.floor_div_eq_div _ _ using 3,
      rw nat.cast_mul,
      norm_cast },
    { rw [←card_pos, card_erase_of_mem ha, ←nat.succ_le_iff],
      exact nat.le_pred_of_lt hA },
    refine mul_nonneg (mul_nonneg (by norm_num1) (nat.cast_nonneg _)) (inv_nonneg.2 _),
    exact nat.cast_nonneg _ },
  simp [-and_imp],
end

lemma right_good_quads_subset (hA : 2 ≤ A.card) :
  (right_good_quads A B Q).card ≤
    ((A * Q).sigma (λ u, nearest_neighbours (A * Q) u (12 * (A*Q).card / A.card))).card :=
begin
  refine card_le_card_of_inj_on _ _ _,
  { rintro x,
    exact ⟨x.1, x.2⟩ },
  { simp only [right_good_quads, mem_image, mem_sigma, and_imp, exists_prop, prod.forall,
      forall_exists_index, exists_and_distrib_right, prod.mk.inj_iff, prod.exists, good_quads,
      good_triples, three_to_four_map, mem_filter, good_triple, mul_good_triple, mem_product],
    rintro _ _ _ _ _ _ a b q ha hb hq - hU rfl rfl rfl rfl rfl rfl,
    refine ⟨mul_mem_mul ha hq, _⟩,
    rw ←nat.le_floor_iff at hU,
    apply mul_good_triple_set_subset_nearest_neighbours _ hq,
    { apply hU.trans (le_of_eq _),
      convert nat.floor_div_eq_div _ _ using 3,
      rw nat.cast_mul,
      norm_cast },
    { rw [←card_pos, card_erase_of_mem ha, ←nat.succ_le_iff],
      exact nat.le_pred_of_lt hA },
    refine mul_nonneg (mul_nonneg (by norm_num1) (nat.cast_nonneg _)) (inv_nonneg.2 _),
    exact nat.cast_nonneg _ },
  simp [-and_imp],
end

lemma left_good_quads_card (hA : 2 ≤ A.card) :
  (left_good_quads A B Q).card ≤ 12 * (A + B).card^2 / A.card :=
begin
  apply (left_good_quads_subset hA).trans,
  rw card_sigma,
  have : ∀ x ∈ A + B, (nearest_neighbours (A + B) x (12 * (A + B).card / A.card)).card ≤
    (12 * (A + B).card / A.card),
  { intros x hx,
    rw card_nearest_neighbours_eq,
    apply min_le_right },
  apply (sum_le_of_forall_le _ _ _ this).trans,
  simp only [algebra.id.smul_eq_mul],
  apply (nat.mul_div_le_mul_div_assoc _ _ _).trans,
  rw [mul_left_comm, sq],
end

lemma right_good_quads_card (hA : 2 ≤ A.card) :
  (right_good_quads A B Q).card ≤ 12 * (A * Q).card^2 / A.card :=
begin
  apply (right_good_quads_subset hA).trans,
  rw card_sigma,
  have : ∀ x ∈ A * Q, (nearest_neighbours (A * Q) x (12 * (A * Q).card / A.card)).card ≤
    (12 * (A * Q).card / A.card),
  { intros x hx,
    rw card_nearest_neighbours_eq,
    apply min_le_right },
  apply (sum_le_of_forall_le _ _ _ this).trans,
  simp only [algebra.id.smul_eq_mul],
  apply (nat.mul_div_le_mul_div_assoc _ _ _).trans,
  rw [mul_left_comm, sq],
end

lemma good_quads_card_le (hA : 2 ≤ A.card) :
  (good_quads A B Q).card ≤ 12 * 12 * (A + B).card^2 * (A * Q).card^2 / A.card^2 :=
begin
  refine (card_le_of_subset subset_product).trans _,
  rw [card_product],
  apply (nat.mul_le_mul (left_good_quads_card hA) (right_good_quads_card hA)).trans,
  apply (nat.mul_div_le_mul_div_assoc _ _ _).trans,
  rw [sq A.card, ←nat.div_div_eq_div_mul, mul_right_comm 12 12, mul_assoc],
  apply nat.div_le_div_right,
  rw [mul_comm, mul_comm (12 * (A + B).card^2)],
  apply nat.mul_div_le_mul_div_assoc,
end

lemma few_good_quad (A B Q : finset ℝ) (hA : 2 ≤ A.card) (hQ : (0:ℝ) ∉ Q) :
  (good_triples A B Q).card ≤
    12 * 12 * (A + B).card^2 * (A * Q).card^2 / A.card^2 :=
begin
  rw ←good_quads_card hQ,
  apply good_quads_card_le hA,
end

lemma restricted_bound (A B Q : finset ℝ) (hA : 2 ≤ A.card) (hB : B.nonempty) (hQ : (0:ℝ) ∉ Q)
  (hQ' : Q.nonempty) :
  A.card^3 * B.card * Q.card ≤ 288 * (A + B).card ^ 2 * (A * Q).card ^ 2 :=
begin
  have hA' : 0 < A.card := zero_lt_two.trans_le hA,
  have hQ'' : Q ≠ {0},
  { rintro rfl,
    simpa using hQ },
  suffices : (A.card * B.card * Q.card) * A.card^2 ≤ 2 * (144 * (A + B).card^2 * (A * Q).card^2),
  { refine le_trans (by ring_nf) (this.trans _),
    rw [←mul_assoc, ←mul_assoc],
    refl },
  apply (nat.mul_le_mul_right _ (many_good_triples A B Q hB hQ' hQ'')).trans,
  rw [mul_comm _ 2, mul_assoc],
  apply nat.mul_le_mul_left,
  rw ←nat.le_div_iff_mul_le _ _ (sq_pos_of_pos hA'),
  apply few_good_quad A B Q hA hQ,
end

-- This fails when A = {0}, B = {1}, |Q| > 288
lemma real_bound_but_not_really (A B Q : finset ℝ) (hA : A ≠ {0}) (hQ : (0:ℝ) ∉ Q) :
  A.card^3 * B.card * Q.card ≤ 288 * (A + B).card ^ 2 * (A * Q).card ^ 2 :=
begin
  rcases B.eq_empty_or_nonempty with rfl | hB,
  { simp },
  rcases Q.eq_empty_or_nonempty with rfl | hQ',
  { simp },
  rcases lt_or_le A.card 2 with hA | hA,
  { rw [nat.lt_succ_iff, card_le_one_iff_subset_singleton] at hA,
    obtain ⟨x, hx⟩ := hA,
    rcases subset_singleton_iff.1 hx with rfl | rfl,
    { simp },
    rw finset.singleton_injective.ne_iff at hA,
    rw [card_singleton, one_pow, one_mul, singleton_add,
      card_image_of_injective _ (add_right_injective _), singleton_mul,
      card_image_of_injective _ (mul_right_injective₀ hA), mul_assoc, ←mul_pow],
    refine le_trans _ (nat.le_mul_of_pos_left (by norm_num1)),
    rw sq,
    apply nat.le_mul_self },
  apply restricted_bound _ _ _ hA hB hQ hQ',
end

lemma real_bound_with_zero (A B Q : finset ℝ) (hA : A ≠ {0}) (hQ : (0 : ℝ) ∉ Q) (hQ' : Q.nonempty) :
  A.card^3 * B.card * (insert (0 : ℝ) Q).card ≤ 576 * (A + B).card ^ 2 * (A * Q).card ^ 2 :=
begin
  change _ ≤ (2 * 288) * _ * _,
  rw [mul_assoc 2, mul_assoc 2, two_mul, card_insert_of_not_mem hQ, mul_add, mul_one],
  apply add_le_add (real_bound_but_not_really A B Q hA hQ),
  have AAQ : A.card ≤ (A * Q).card,
  { apply left_le_card_mul',
    obtain ⟨q, hq⟩ := hQ',
    exact ⟨q, hq, ne_of_mem_of_not_mem hq hQ⟩ },
  have := real_bound_but_not_really A B {1} hA (by simp),
  simp only [image_id', mul_one, mul_singleton, card_singleton] at this,
  exact le_trans this (nat.mul_le_mul_left _ (nat.pow_le_pow_of_le_left AAQ _)),
end

lemma real_bound_almost (A B Q : finset ℝ) (hA : A ≠ {0}) (hQ : (Q.erase 0).nonempty) :
  A.card^3 * B.card * Q.card ≤ 576 * (A + B).card ^ 2 * (A * Q).card ^ 2 :=
begin
  cases em' ((0 : ℝ) ∈ Q) with hQ₀ hQ₀,
  { apply (real_bound_but_not_really _ _ _ hA hQ₀).trans _,
    rw [mul_assoc, mul_assoc],
    exact nat.mul_le_mul_right _ (by norm_num1) },
  rw ←insert_erase hQ₀,
  apply (real_bound_with_zero A B (Q.erase 0) hA (not_mem_erase _ _) hQ).trans,
  apply nat.mul_le_mul_left _ (nat.pow_le_pow_of_le_left (card_le_of_subset _) _),
  apply finset.mul_subset_mul (finset.subset.refl _) (subset_insert _ _),
end

-- strictly speaking this works if A = {0} and Q = {0} so the condition could be strengthened to
-- A = {0} ↔ Q = {0}. If only one is {0}, we can make B = {1} and the other large (more than 600
-- elements) and derive a contradiction.
lemma real_bound (A B Q : finset ℝ) (hA : A ≠ {0}) (hQ : Q ≠ {0}) :
  A.card^3 * B.card * Q.card ≤ 576 * (A + B).card ^ 2 * (A * Q).card ^ 2 :=
begin
  rcases Q.eq_empty_or_nonempty with rfl | hQ',
  { simp },
  apply real_bound_almost _ _ _ hA,
  rw [nonempty_iff_ne_empty, ne.def, erase_eq_empty_iff],
  simp only [hQ'.ne_empty, hQ, false_or, not_false_iff],
end

variables (A)

lemma real_specific_bound : A.card ^ 5 ≤ 576 * (A + A).card ^ 2 * (A * A).card ^ 2 :=
begin
  rcases eq_or_ne A {0} with rfl | hA,
  { simp },
  exact le_trans (le_of_eq (by ring)) (real_bound A A A hA hA),
end

lemma specific_max_bound :
  A.card ^ 5 ≤ (5 * max (A + A).card (A * A).card) ^ 4 :=
begin
  rcases A.eq_empty_or_nonempty with rfl | hA,
  { simp },
  rw [mul_pow, (show _ ^ 4 = _, from (pow_left_monotone 4).map_max),
    mul_max_of_nonneg _ _ (nat.zero_le _), ←not_lt, max_lt_iff],
  rintro ⟨h₁, h₂⟩,
  apply not_lt_of_le (real_specific_bound A),
  rw ←(nat.pow_left_strict_mono one_le_two).lt_iff_lt,
  dsimp,
  rw sq (A.card ^ 5),
  apply lt_of_le_of_lt _ (nat.mul_lt_mul h₁ h₂.le _),
  { rw [mul_mul_mul_comm, mul_pow, mul_pow, mul_assoc, ←pow_mul, ←pow_mul],
    apply nat.mul_le_mul_right,
    norm_num1 },
  refine mul_pos (by norm_num1) (pow_pos _ _),
  simpa [card_pos],
end

-- We cannot have both A + A and A * A linear in A. Note that it is possible for either of them
-- linear, by taking an arithmetic or geometric progression respectively, but not simultaneously
lemma max_bound :
  1 / 5 * (A.card : ℝ)^(5 / 4 : ℝ) ≤ max (A + A).card (A * A).card :=
begin
  rw [←not_lt, mul_comm (1 / 5 : ℝ), mul_one_div, lt_div_iff'],
  intro h,
  have : (5 * max (A + A).card (A * A).card)^4 < (A.card)^5,
  { suffices : (5 * max (A + A).card (A * A).card : ℝ)^4 < (A.card)^5,
    { exact_mod_cast this },
    rw [←real.rpow_nat_cast, ←real.rpow_nat_cast],
    simp only [nat.cast_bit1, nat.cast_bit0, nat.cast_one],
    apply (real.rpow_lt_rpow _ h _).trans_le,
    { rw [←real.rpow_mul (nat.cast_nonneg _), div_mul_cancel],
      norm_num1 },
    { exact_mod_cast (nat.zero_le _) },
    { norm_num1 } },
  apply not_le_of_lt this (specific_max_bound A),
  norm_num
end

-- lemma real_specific_bound_nat_card (A : set ℝ) :
--   (nat.card A)^5 ≤ 576 * (nat.card (A + A : set ℝ))^2 * (nat.card (A * A : set ℝ))^2 :=
-- begin
--   casesI fintype_or_infinite A,
--   { simp,
--     have := set.fintype_mul,
--   }
-- end
