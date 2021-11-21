import data.complex.basic
import analysis.complex.basic
import topology.instances.real
import tactic.by_contra
import algebra.pointwise
import analysis.special_functions.pow

open_locale pointwise big_operators

@[simp, to_additive] lemma finset.empty_mul
  {α : Type*} [decidable_eq α] [has_mul α] {A : finset α} : ∅ * A = ∅ :=
finset.eq_empty_of_forall_not_mem (by simp [finset.mem_mul])

@[simp, to_additive] lemma finset.mul_empty
  {α : Type*} [decidable_eq α] [has_mul α] {A : finset α} : A * ∅ = ∅ :=
finset.eq_empty_of_forall_not_mem (by simp [finset.mem_mul])

@[simp, to_additive] lemma finset.mul_nonempty_iff
  {α : Type*} [decidable_eq α] [has_mul α] {A B : finset α} :
    (A * B).nonempty ↔ A.nonempty ∧ B.nonempty :=
by simp [finset.mul_def]

lemma sum_card_inter_le {α β : Type*} {s : finset α} {B : finset β}
  (g : β → α → Prop) [∀ b a, decidable (g b a)]
  {n : ℕ} (h : ∀ a ∈ s, (B.filter (λ b, g b a)).card ≤ n) :
  ∑ b in B, (s.filter (g b)).card ≤ s.card * n :=
begin
  simp_rw [finset.card_eq_sum_ones (finset.filter _ _), finset.sum_filter],
  rw [finset.sum_comm],
  apply finset.sum_le_of_forall_le,
  simpa,
end

noncomputable theory
open_locale classical

lemma real_covering₀_pos {ι : Type*} (s : finset ι) (x r : ι → ℝ)
  (disj : (s : set ι).pairwise (λ i j, r i ≤ abs (x i - x j))) :
  (s.filter (λ i, 0 < x i ∧ abs (x i) ≤ r i)).card ≤ 1 :=
begin
  rw finset.card_le_one,
  simp only [and_imp, finset.mem_filter],
  intros i hi₁ hi₂ hi₃ j hj₁ hj₂ hj₃,
  wlog : x i ≤ x j using i j,
  rw abs_of_pos hi₂ at hi₃,
  rw abs_of_pos hj₂ at hj₃,
  by_contra,
  have := disj j hj₁ i hi₁ (ne.symm h),
  rw abs_of_nonneg (sub_nonneg_of_le case) at this,
  apply not_le_of_lt hi₂ ((le_sub_self_iff _).1 (hj₃.trans this)),
end

lemma real_covering₀_neg {ι : Type*} (s : finset ι) (x r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i)
  (disj : (s : set ι).pairwise (λ i j, r i ≤ abs (x i - x j))) :
  (s.filter (λ i, x i < 0 ∧ abs (x i) ≤ r i)).card ≤ 1 :=
begin
  convert real_covering₀_pos s (λ i, - x i) r _,
  { simp },
  refine disj.imp _,
  intros a b hab,
  rwa [neg_sub_neg, abs_sub_comm],
end

lemma real_covering₀ {ι : Type*} (s : finset ι) (x r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i)
  (disj : (s : set ι).pairwise (λ i j, r i ≤ abs (x i - x j))) :
  (s.filter (λ i, abs (x i) ≤ r i)).card ≤ 3 :=
begin
end

lemma real_covering {ι : Type*} (s : finset ι) (x r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i)
  (disj : (s : set ι).pairwise (λ i j, r i ≤ abs (x i - x j))) (z : ℝ) :
  (s.filter (λ i, abs (x i - z) ≤ r i)).card ≤ 3 :=
begin
  apply real_covering₀ s (λ i, x i - z) r hr,
  simpa,
end

def finset.is_neighbouring (A : finset ℝ) (a a' : ℝ) : Prop :=
  a' ≠ a ∧ ∀ a'' ∈ A, abs (a - a'') < abs (a - a') → a = a''

structure good_quad (A B Q : finset ℝ) (a a' b q : ℝ) : Prop :=
(ha : a ∈ A)
(ha' : a' ∈ A)
(hb : b ∈ B)
(hq : q ∈ Q)
(neighbour : A.is_neighbouring a a')
(ab_sparse :
  ((A + B).filter (λ u, abs (a + b - u) ≤ abs (a - a'))).card * A.card ≤ 28 * (A + B).card)
(aq_sparse :
  ((A * Q).filter (λ v, abs (a * q - v) ≤ abs (a * q - a' * q))).card * A.card ≤ 28 * (A + Q).card)

lemma many_good_quad (A B Q : finset ℝ) {b q : ℝ} (hb : b ∈ B) (hq : q ∈ Q) :
  (A.card : ℝ) / 2 ≤ ((A.product A).filter (λ (a : ℝ × ℝ), good_quad A B Q a.1 a.2 b q)).card :=
begin

end

#exit

theorem complex_bound : ∃ (c : ℝ), 0 < c ∧ ∀ A B Q : finset ℝ,
  c * A.card ^ (3/2 : ℝ) * B.card ^ (1/2 : ℝ) * Q.card ^ (1/2 : ℝ) ≤ (A + B).card * (A * Q).card :=
begin
  sorry
end

theorem complex_specific_bound : ∃ (c : ℝ), 0 < c ∧ ∀ A : finset ℝ,
  c * A.card ^ (5/4 : ℝ) ≤ max (A + A).card (A * A).card :=
begin
  obtain ⟨c, c_pos, hc⟩ := complex_bound,
  refine ⟨c^(1/2 : ℝ), real.rpow_pos_of_pos c_pos _, λ A, _⟩,
  rcases A.eq_empty_or_nonempty with rfl | hA,
  { rw [finset.add_empty, finset.mul_empty, finset.card_empty, nat.cast_zero, max_self,
      real.zero_rpow, mul_zero],
    norm_num },
  by_contra' t,
  rw max_lt_iff at t,
  have := hc A A A,
  have hA' : 0 < (A.card : ℝ),
  { rwa [nat.cast_pos, finset.card_pos] },
  apply not_lt_of_le this,
  rw [mul_assoc, mul_assoc, ←real.rpow_add hA', add_halves, ←real.rpow_add hA',
    div_add_one (show (2:ℝ) ≠ 0, from two_ne_zero)],
  apply (mul_lt_mul t.1 t.2.le _ _).trans_le,
  { rw [←sq, mul_pow, ←real.rpow_nat_cast, ←real.rpow_nat_cast, ←real.rpow_mul c_pos.le,
      ←real.rpow_mul hA'.le, nat.cast_two, div_mul_cancel _ (show (2:ℝ) ≠ 0, from two_ne_zero),
      real.rpow_one],
    norm_num },
  { simpa [finset.card_pos] },
  exact mul_nonneg (real.rpow_nonneg_of_nonneg c_pos.le _) (real.rpow_nonneg_of_nonneg hA'.le _),
end
