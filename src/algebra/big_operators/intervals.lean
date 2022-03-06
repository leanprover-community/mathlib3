/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import algebra.big_operators.basic
import algebra.module.basic
import data.nat.interval
import tactic.linarith
import tactic.abel

/-!
# Results about big operators over intervals

We prove results about big operators over intervals (mostly the `ℕ`-valued `Ico m n`).
-/

universes u v w

open_locale big_operators nat

namespace finset

section generic

variables {α : Type u} {β : Type v} {γ : Type w} {s₂ s₁ s : finset α} {a : α}
  {g f : α → β}

variables [comm_monoid β]

@[to_additive]
lemma prod_Ico_add' [ordered_cancel_add_comm_monoid α] [has_exists_add_of_le α]
  [locally_finite_order α] (f : α → β) (a b c : α) :
  (∏ x in Ico a b, f (x + c)) = (∏ x in Ico (a + c) (b + c), f x) :=
begin
  classical,
  rw [←image_add_right_Ico, prod_image (λ x hx y hy h, add_right_cancel h)],
end

@[to_additive]
lemma prod_Ico_add [ordered_cancel_add_comm_monoid α] [has_exists_add_of_le α]
  [locally_finite_order α] (f : α → β) (a b c : α) :
  (∏ x in Ico a b, f (c + x)) = (∏ x in Ico (a + c) (b + c), f x) :=
begin
  convert prod_Ico_add' f a b c,
  simp_rw add_comm,
end

lemma sum_Ico_succ_top {δ : Type*} [add_comm_monoid δ] {a b : ℕ}
  (hab : a ≤ b) (f : ℕ → δ) : (∑ k in Ico a (b + 1), f k) = (∑ k in Ico a b, f k) + f b :=
by rw [nat.Ico_succ_right_eq_insert_Ico hab, sum_insert right_not_mem_Ico, add_comm]

@[to_additive]
lemma prod_Ico_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → β) :
  (∏ k in Ico a (b + 1), f k) = (∏ k in Ico a b, f k) * f b :=
@sum_Ico_succ_top (additive β) _ _ _ hab _

lemma sum_eq_sum_Ico_succ_bot {δ : Type*} [add_comm_monoid δ] {a b : ℕ}
  (hab : a < b) (f : ℕ → δ) : (∑ k in Ico a b, f k) = f a + (∑ k in Ico (a + 1) b, f k) :=
have ha : a ∉ Ico (a + 1) b, by simp,
by rw [← sum_insert ha, nat.Ico_insert_succ_left hab]

@[to_additive]
lemma prod_eq_prod_Ico_succ_bot {a b : ℕ} (hab : a < b) (f : ℕ → β) :
  (∏ k in Ico a b, f k) = f a * (∏ k in Ico (a + 1) b, f k) :=
@sum_eq_sum_Ico_succ_bot (additive β) _ _ _ hab _

@[to_additive]
lemma prod_Ico_consecutive (f : ℕ → β) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
  (∏ i in Ico m n, f i) * (∏ i in Ico n k, f i) = (∏ i in Ico m k, f i) :=
Ico_union_Ico_eq_Ico hmn hnk ▸ eq.symm $ prod_union $ Ico_disjoint_Ico_consecutive m n k

@[to_additive]
lemma prod_range_mul_prod_Ico (f : ℕ → β) {m n : ℕ} (h : m ≤ n) :
  (∏ k in range m, f k) * (∏ k in Ico m n, f k) = (∏ k in range n, f k) :=
nat.Ico_zero_eq_range ▸ nat.Ico_zero_eq_range ▸ prod_Ico_consecutive f m.zero_le h

@[to_additive]
lemma prod_Ico_eq_mul_inv {δ : Type*} [comm_group δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
  (∏ k in Ico m n, f k) = (∏ k in range n, f k) * (∏ k in range m, f k)⁻¹ :=
eq_mul_inv_iff_mul_eq.2 $ by rw [mul_comm]; exact prod_range_mul_prod_Ico f h

lemma sum_Ico_eq_sub {δ : Type*} [add_comm_group δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
  (∑ k in Ico m n, f k) = (∑ k in range n, f k) - (∑ k in range m, f k) :=
by simpa only [sub_eq_add_neg] using sum_Ico_eq_add_neg f h

/-- The two ways of summing over `(i,j)` in the range `a<=i<=j<b` are equal. -/
lemma sum_Ico_Ico_comm {M : Type*} [add_comm_monoid M]
  (a b : ℕ) (f : ℕ → ℕ → M) :
  ∑ i in finset.Ico a b, ∑ j in finset.Ico i b, f i j =
  ∑ j in finset.Ico a b, ∑ i in finset.Ico a (j+1), f i j :=
begin
  rw [finset.sum_sigma', finset.sum_sigma'],
  refine finset.sum_bij'
    (λ (x : Σ (i : ℕ), ℕ) _, (⟨x.2, x.1⟩ : Σ (i : ℕ), ℕ)) _ (λ _ _, rfl)
    (λ (x : Σ (i : ℕ), ℕ) _, (⟨x.2, x.1⟩ : Σ (i : ℕ), ℕ)) _
    (by rintro ⟨⟩ _; refl) (by rintro ⟨⟩ _; refl);
  simp only [finset.mem_Ico, sigma.forall, finset.mem_sigma];
  rintros a b ⟨⟨h₁,h₂⟩, ⟨h₃, h₄⟩⟩; refine ⟨⟨_, _⟩, ⟨_, _⟩⟩; linarith
end

@[to_additive]
lemma prod_Ico_eq_prod_range (f : ℕ → β) (m n : ℕ) :
  (∏ k in Ico m n, f k) = (∏ k in range (n - m), f (m + k)) :=
begin
  by_cases h : m ≤ n,
  { rw [←nat.Ico_zero_eq_range, prod_Ico_add, zero_add, tsub_add_cancel_of_le h] },
  { replace h : n ≤ m :=  le_of_not_ge h,
     rw [Ico_eq_empty_of_le h, tsub_eq_zero_iff_le.mpr h, range_zero, prod_empty, prod_empty] }
end

lemma prod_Ico_reflect (f : ℕ → β) (k : ℕ) {m n : ℕ} (h : m ≤ n + 1) :
  ∏ j in Ico k m, f (n - j) = ∏ j in Ico (n + 1 - m) (n + 1 - k), f j :=
begin
  have : ∀ i < m, i ≤ n,
  { intros i hi,
    exact (add_le_add_iff_right 1).1 (le_trans (nat.lt_iff_add_one_le.1 hi) h) },
  cases lt_or_le k m with hkm hkm,
  { rw [← nat.Ico_image_const_sub_eq_Ico (this _ hkm)],
    refine (prod_image _).symm,
    simp only [mem_Ico],
    rintros i ⟨ki, im⟩ j ⟨kj, jm⟩ Hij,
    rw [← tsub_tsub_cancel_of_le (this _ im), Hij, tsub_tsub_cancel_of_le (this _ jm)] },
  { simp [Ico_eq_empty_of_le, tsub_le_tsub_left, hkm] }
end

lemma sum_Ico_reflect {δ : Type*} [add_comm_monoid δ] (f : ℕ → δ) (k : ℕ) {m n : ℕ}
  (h : m ≤ n + 1) :
  ∑ j in Ico k m, f (n - j) = ∑ j in Ico (n + 1 - m) (n + 1 - k), f j :=
@prod_Ico_reflect (multiplicative δ) _ f k m n h

lemma prod_range_reflect (f : ℕ → β) (n : ℕ) :
  ∏ j in range n, f (n - 1 - j) = ∏ j in range n, f j :=
begin
  cases n,
  { simp },
  { simp only [←nat.Ico_zero_eq_range, nat.succ_sub_succ_eq_sub, tsub_zero],
    rw prod_Ico_reflect _ _ le_rfl,
    simp }
end

lemma sum_range_reflect {δ : Type*} [add_comm_monoid δ] (f : ℕ → δ) (n : ℕ) :
  ∑ j in range n, f (n - 1 - j) = ∑ j in range n, f j :=
@prod_range_reflect (multiplicative δ) _ f n

@[simp] lemma prod_Ico_id_eq_factorial : ∀ n : ℕ, ∏ x in Ico 1 (n + 1), x = n!
| 0 := rfl
| (n+1) := by rw [prod_Ico_succ_top $ nat.succ_le_succ $ zero_le n,
  nat.factorial_succ, prod_Ico_id_eq_factorial n, nat.succ_eq_add_one, mul_comm]

@[simp] lemma prod_range_add_one_eq_factorial : ∀ n : ℕ, ∏ x in range n, (x+1) = n!
| 0 := rfl
| (n+1) := by simp [finset.range_succ, prod_range_add_one_eq_factorial n]

section gauss_sum

/-- Gauss' summation formula -/
lemma sum_range_id_mul_two (n : ℕ) :
  (∑ i in range n, i) * 2 = n * (n - 1) :=
calc (∑ i in range n, i) * 2 = (∑ i in range n, i) + (∑ i in range n, (n - 1 - i)) :
  by rw [sum_range_reflect (λ i, i) n, mul_two]
... = ∑ i in range n, (i + (n - 1 - i)) : sum_add_distrib.symm
... = ∑ i in range n, (n - 1) : sum_congr rfl $ λ i hi, add_tsub_cancel_of_le $
  nat.le_pred_of_lt $ mem_range.1 hi
... = n * (n - 1) : by rw [sum_const, card_range, nat.nsmul_eq_mul]

/-- Gauss' summation formula -/
lemma sum_range_id (n : ℕ) : (∑ i in range n, i) = (n * (n - 1)) / 2 :=
by rw [← sum_range_id_mul_two n, nat.mul_div_cancel]; exact dec_trivial

end gauss_sum

end generic

section nat

variable {β : Type*}
variables (f g : ℕ → β) {m n : ℕ}

section group

variable [comm_group β]

@[to_additive]
lemma prod_range_succ_div_prod : (∏ i in range (n+1), f i) / ∏ i in range n, f i = f n :=
div_eq_iff_eq_mul'.mpr $ prod_range_succ f n

@[to_additive]
lemma prod_range_succ_div_top : (∏ i in range (n+1), f i) / f n = ∏ i in range n, f i :=
div_eq_iff_eq_mul.mpr $ prod_range_succ f n

@[to_additive]
lemma prod_Ico_div_bot (hmn : m < n) : (∏ i in Ico m n, f i) / f m = ∏ i in Ico (m+1) n, f i :=
div_eq_iff_eq_mul'.mpr $ prod_eq_prod_Ico_succ_bot hmn _

@[to_additive]
lemma prod_Ico_succ_div_top (hmn : m ≤ n) : (∏ i in Ico m (n+1), f i) / f n = ∏ i in Ico m n, f i :=
div_eq_iff_eq_mul.mpr $ prod_Ico_succ_top hmn _

end group

end nat

section module

variables {R M : Type*} [ring R] [add_comm_group M] [module R M] (f : ℕ → R) (g : ℕ → M) {m n : ℕ}
open finset
-- The partial sum of `g`, starting from zero
local notation `G` n:80 := ∑ i in range n, g i

/-- **Summation by parts**, also known as **Abel's lemma** or an **Abel transformation** -/
theorem sum_Ico_by_parts (hmn : m < n) :
  ∑ i in Ico m n, f i • g i =
  f (n-1) • G n - f m • G m - ∑ i in Ico m (n-1), (f (i+1) - f i) • G (i+1) :=
begin
  have h₁ : ∑ i in Ico (m+1) n, (f i • G i) = ∑ i in Ico m (n-1), (f (i+1) • G (i+1)),
  { conv in n { rw ←nat.sub_add_cancel (nat.one_le_of_lt hmn) },
    rw ←sum_Ico_add' },
  have h₂ : ∑ i in Ico (m+1) n, (f i • G (i+1))
          = ∑ i in Ico m (n-1), (f i • G (i+1)) + f (n-1) • G n - f m • G (m+1) :=
  by rw [←sum_Ico_sub_bot _ hmn, ←sum_Ico_succ_sub_top _ (nat.le_pred_of_lt hmn),
         nat.sub_add_cancel (pos_of_gt hmn), sub_add_cancel],
  rw sum_eq_sum_Ico_succ_bot hmn,
  conv { for (f _ • g _) [2] { rw ← sum_range_succ_sub_sum g } },
  simp_rw [smul_sub, sum_sub_distrib, h₂, h₁],
  conv_lhs { congr, skip, rw [←add_sub, add_comm, ←add_sub, ←sum_sub_distrib] },
  have : ∀ i, f i • G (i+1) - f (i+1) • G (i+1) = -((f (i+1) - f i) • G (i+1)),
  { intro i,
    rw sub_smul,
    abel },
  simp_rw [this, sum_neg_distrib, sum_range_succ, smul_add],
  abel,
end

/-- **Summation by parts** for ranges -/
lemma sum_range_by_parts (hn : 0 < n) :
  ∑ i in range n, (f i • g i) = f (n-1) • G n - ∑ i in range (n-1), (f (i+1) - f i) • G (i+1) :=
by rw [range_eq_Ico, sum_Ico_by_parts f g hn, sum_range_zero, smul_zero, sub_zero, range_eq_Ico]

end module

end finset
