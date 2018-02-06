/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import data.nat.basic algebra.group data.real.cau_seq tactic.ring

open nat is_absolute_value
variables {α : Type*} {β : Type*}

def series [has_add α] (f : ℕ → α) : ℕ → α
| 0        := f 0
| (succ i) := series i + f (succ i)

def nat.sum [has_add α] (f : ℕ → α) (i j : ℕ) := series (λ k, f (k + i)) (j - i)

@[simp]
lemma series_zero [has_add α] (f : ℕ → α) : series f 0 = f 0 := by unfold series

lemma series_succ [has_add α] (f : ℕ → α) (i : ℕ) : series f (succ i) = series f i + f (succ i):= by unfold series

lemma series_eq_sum_zero [has_add α] (f : ℕ → α) (i : ℕ) : series f i = nat.sum f 0 i := by unfold nat.sum;simp

lemma series_succ₁ [add_comm_monoid α] (f : ℕ → α) (i : ℕ) : series f (succ i) = f 0 + series (λ i, f (succ i)) i := begin
 induction i with i' hi,
 simp!,simp!,rw ←hi,simp!,
end

lemma series_comm {α : Type*} [add_comm_monoid α] (f : ℕ → α) (n : ℕ) : series f n = series (λ i, f (n - i)) n := begin
  induction n with n' hi,
  simp!,simp!,rw hi,
  have : (λ (i : ℕ), f (succ n' - i)) (succ n') = f (n' - n'),simp,
  rw ←this,have : (λ (i : ℕ), f (succ n' - i)) (succ n') + series (λ (i : ℕ), f (succ n' - i)) n' = series (λ (i : ℕ), f (succ n' - i)) (succ n'),simp!,
  rw this,
  have : (λ i, f (n' - i)) = (λ i, f (succ n' - succ i)) := by
   {apply funext,assume i,rw succ_sub_succ},
  rw this,clear this,
  have : f (succ n') = (λ (i : ℕ), f (succ n' - i)) 0,simp,rw this,rw ←series_succ₁,
end

lemma series_neg [ring α] (f : ℕ → α) (n : ℕ) : -series f n = series (λ m, -f m) n := begin
  induction n with n' hi, simp!,simp![hi],
end

lemma series_sub_series [ring α] (f : ℕ → α) {i j : ℕ} : i < j → series f j - series f i = nat.sum f (i + 1) j := begin
  unfold nat.sum,assume ij,
  induction i with i' hi,
  cases j with j',exact absurd ij dec_trivial,
  rw sub_eq_iff_eq_add',
  exact series_succ₁  _ _,
  rw [series_succ,sub_add_eq_sub_sub,hi (lt_of_succ_lt ij),sub_eq_iff_eq_add'],
  have : (j - (i' + 1)) = succ (j - (succ i' + 1)) := by
    {rw [←nat.succ_sub ij,succ_sub_succ]},
  rw this,
  have : f (succ i') = (λ (k : ℕ), f (k + (i' + 1))) 0 := by simp,
  rw this,simp[succ_add,add_succ],
  rw series_succ₁,simp,
end

lemma series_const_zero [has_zero α] (i : ℕ): series (λ j, 0) i = 0 := begin
  induction i with i' hi,simp,simpa [series_succ],
end

lemma series_add [add_comm_monoid α] (f g : ℕ → α) (n : ℕ) : series (λ i, f i + g i) n = series f n + series g n := begin
  induction n with n' hi,simp[series_zero],simp[series_succ,hi],
end

lemma series_mul_left [semiring α] (f : ℕ → α) (a : α) (n : ℕ) : series (λ i, a * f i) n = a * series f n := begin
  induction n with n' hi,simp[series_zero],simp[series_succ,hi,mul_add],
end
 
lemma series_mul_right [semiring α] (f : ℕ → α) (a : α) (n : ℕ) : series (λ i, f i * a) n = series f n * a:= begin
  induction n with n' hi,simp[series_zero],simp[series_succ,hi,add_mul],
end

lemma series_le [add_comm_monoid α] {f g : ℕ → α} {n : ℕ} : (∀ i : ℕ, i ≤ n → f i = g i) → series f n = series g n := begin
  assume h, induction n with n' hi,simp,exact h 0 (le_refl _),
  simp[series_succ],rw [h (succ n') (le_refl _),hi (λ i h₁,h i (le_succ_of_le h₁))],
end

lemma abv_series_le_series_abv [discrete_linear_ordered_field α] [ring β] {f : ℕ → β}
{abv : β → α} [is_absolute_value abv] (n : ℕ) : abv (series f n) ≤ series (λ i, abv (f i)) n := begin
  induction n with n' hi,
  simp,simp[series_succ],
  exact le_trans (abv_add _ _ _) (add_le_add_left hi _),
end

lemma series_mul_series [semiring α] (f g : ℕ → α) (n m : ℕ) : series f n * series g m
= series (λ i, f i * series g m) n := begin
  induction n with n' hi,
  simp,simp[series_succ,mul_add,add_mul,hi],
end

lemma series_le_series [ordered_cancel_comm_monoid α] {f g : ℕ → α} {n : ℕ} : (∀ m ≤ n, f m ≤ g m) → 
series f n ≤ series g n := begin
  assume h,induction n with n' hi,exact h 0 (le_refl _),
  unfold series,exact add_le_add (hi (λ m hm, h m (le_succ_of_le hm))) (h _ (le_refl _)),
end

lemma series_congr [has_add α] {f g : ℕ → α} {i : ℕ} : (∀ j ≤ i, f j = g j) → series f i = series g i := begin
  assume h,induction i with i' hi,exact h 0 (zero_le _),
  unfold series,rw h _ (le_refl (succ i')),
  rw hi (λ j ji, h j (le_succ_of_le ji)),
end

lemma series_nonneg [ordered_cancel_comm_monoid α] {f : ℕ → α} {n : ℕ} : (∀ m ≤ n, 0 ≤ f m) → 0 ≤ series f n := begin
  induction n with n' hi,simp,assume h,exact h 0 (le_refl _),
  assume h,unfold series,refine add_nonneg (hi (λ m hm, h m (le_succ_of_le hm))) (h _ (le_refl _)),
end

-- proof that two different ways of representing a sum across a 2D plane are equal, used
-- in proof of exp (x + y) = exp x * exp y
lemma series_series_diag_flip [add_comm_monoid α] (f : ℕ → ℕ → α) (n : ℕ) : series (λ i, 
series (λ k, f k (i - k)) i) n = series (λ i, series (λ k, f i k) (n - i)) n := begin
  have : ∀ m : ℕ, m ≤ n → series (λ (i : ℕ), series (λ k, f k (i - k)) (min m i)) n =
  series (λ i, series (λ k, f i k) (n - i)) m := by
  { assume m mn, induction m with m' hi,
    simp[series_succ,series_zero,mul_add,max_eq_left (zero_le n)],
    simp only [series_succ _ m'],rw ←hi (le_of_succ_le mn),clear hi,
    induction n with n' hi,
    simp[series_succ],exact absurd mn dec_trivial,cases n' with n₂,
    simp [series_succ],rw [min_eq_left mn,series_succ,min_eq_left (le_of_succ_le mn)],
    rw eq_zero_of_le_zero (le_of_succ_le_succ mn),simp,
    cases lt_or_eq_of_le mn,
    simp [series_succ _ (succ n₂),min_eq_left mn,hi (le_of_lt_succ h)],rw [←add_assoc,←add_assoc],
    suffices : series (f (succ m')) (n₂ - m') + series (λ (k : ℕ), f k (succ (succ n₂) - k)) (succ m')
    = series (f (succ m')) (succ n₂ - m') +
        series (λ (k : ℕ), f k (succ (succ n₂) - k)) (min m' (succ (succ n₂))),
      rw this,rw[min_eq_left (le_of_succ_le mn),series_succ,succ_sub_succ,succ_sub (le_of_succ_le_succ (le_of_lt_succ h)),series_succ],
      rw [add_comm (series (λ (k : ℕ), f k (succ (succ n₂) - k)) m'),add_assoc],      
    rw ←h,simp[nat.sub_self],clear hi mn h,simp[series_succ,nat.sub_self],
    suffices : series (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min (succ m') i)) m' = series (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min m' i)) m',
      rw [this,min_eq_left (le_succ _)],clear n₂,
    have h₁ : ∀ i ≤ m', (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min (succ m') i)) i = (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min m' i)) i,
      assume i im,simp, rw [min_eq_right im,min_eq_right (le_succ_of_le im)],
    rw series_congr h₁},
  specialize this n (le_refl _),
  rw ←this,refine series_congr _,assume i ni,rw min_eq_right ni,
end

lemma nat.sum_succ [has_add α] (f : ℕ → α) (i j : ℕ) : i ≤ j → nat.sum f i (succ j) = nat.sum f i j + f (succ j) := begin
  assume ij,unfold nat.sum,rw [succ_sub ij,series_succ,←succ_sub ij,nat.sub_add_cancel (le_succ_of_le ij)],
end

lemma nat.sum_le_sum [ordered_cancel_comm_monoid α] {f g : ℕ → α} {i j : ℕ} : i ≤ j → 
(∀ k ≤ j, i ≤ k → f k ≤ g k) → nat.sum f i j ≤ nat.sum g i j := begin
  assume ij h ,unfold nat.sum,
  refine series_le_series _,
  assume m hm,rw nat.le_sub_right_iff_add_le ij at hm,
  exact h (m + i) hm (le_add_left _ _),
end

def combin : ℕ → ℕ → ℕ
| _            0  := 1
| 0       (j + 1) := 0
| (i + 1) (j + 1) := combin i j + combin i (j + 1)

@[simp]
lemma combin_zero (i : ℕ) : combin i 0 = 1 := begin
  cases i with i,unfold combin,unfold combin,
end

lemma combin_eq_zero {i j : ℕ} : i < j → combin i j = 0 := begin
  revert j,
  induction i with i' hi,
  assume j ij,cases j,exact absurd ij dec_trivial,
  unfold combin,
  assume j ij,
  cases j with j',
  exact absurd ij dec_trivial,
  unfold combin,
  rw [@hi j' (lt_of_succ_lt_succ ij),@hi (j' + 1) (lt_of_succ_lt ij)],
end

@[simp]
lemma combin_self (i : ℕ) : combin i i = 1 := begin
  induction i with i' hi,simp!,simpa! [combin_eq_zero (lt_succ_self _)],
end

lemma combin_fact {i j : ℕ} : j ≤ i → combin i j * fact j * fact (i - j) = fact i := begin
  revert j,
  induction i with i' hi,assume j ij,
  simp!,rw eq_zero_of_le_zero ij,simp!,
  assume j ij,
  cases j with j',simp!,
  unfold combin,rw [succ_sub_succ,add_mul,add_mul],
  have : combin i' j' * fact (succ j') * fact (i' - j') = combin i' j' * fact j' * fact (i' - j') * succ j' := by
  { unfold fact,simp[mul_comm,mul_assoc,mul_left_comm]},
  rw [this,hi (le_of_succ_le_succ ij)],
  cases lt_or_eq_of_le ij with ij' ij',
  have : i' - j' = succ (i' - succ j') := by {rw [←succ_sub (le_of_succ_le_succ ij'),succ_sub_succ]},
  rw [this,fact_succ (i' - succ j'),mul_comm (succ (i' - succ j')),← mul_assoc,hi (le_of_succ_le_succ ij'),←mul_add],
  rw [←succ_sub (le_of_succ_le_succ ij')],rw nat.add_sub_cancel' ij,unfold fact,rw mul_comm,
  rw [add_one,ij',combin_eq_zero (lt_succ_self i'),zero_mul,zero_mul,add_zero,mul_comm],unfold fact,
end

open monoid

theorem series_binomial {α : Type*} [comm_semiring α] (x y : α) (i : ℕ) : pow (x + y) i = 
series (λ j, combin i j * pow x j * pow y (i - j)) i := begin
  induction i with i' hi,
  simp!,unfold monoid.pow,rw hi,
  rw [←series_mul_left],
  have : ∀ j : ℕ, j ≤ i' → (λ (i : ℕ), (x + y) * (↑(combin i' i) * pow x i * pow y (i' - i))) j
  = combin i' j * pow x (succ j) * pow y (i' - j) + combin i' j * pow x j * pow y (succ i' - j) := by
  { assume j ji,dsimp only,rw add_mul,
    have :  x * (↑(combin i' j) * pow x j * pow y (i' - j)) + y * (↑(combin i' j) * pow x j * pow y (i' - j))
    = ↑(combin i' j) * (x * pow x j) * pow y (i' - j) + ↑(combin i' j) * pow x j * (y * pow y (i' - j)),
      simp[mul_comm,_root_.mul_assoc,mul_left_comm],
    rw [this,←_root_.pow_succ,←_root_.pow_succ,succ_sub ji]},
  rw [series_congr this],clear this, 
  clear hi,rw series_add,
  have : series (λ (i : ℕ), ↑(combin i' i) * pow x i * pow y (succ i' - i)) i' = 
      series (λ (i : ℕ), ↑(combin i' i) * pow x i * pow y (succ i' - i)) (succ i') := by
  { simp[series_succ,combin_eq_zero (lt_succ_self i')]},
  rw [this,series_succ₁,series_succ₁],
  simp[combin_zero,combin_self,nat.sub_self],rw ←series_add,
  suffices : (λ (i : ℕ), ↑(combin i' i) * pow x (succ i) * pow y (i' - i) + ↑(combin i' (succ i)) * pow x (succ i) * pow y (i' - i))
  = (λ (i : ℕ), ↑(combin (succ i') (succ i)) * pow x (succ i) * pow y (i' - i)),
    rw this,
  apply funext,
  assume j,unfold combin,rw [nat.cast_add,add_mul,add_mul],
end
