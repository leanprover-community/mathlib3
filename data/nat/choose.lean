/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
Mostly based on Jeremy Avigad's choose file in lean 2
-/

import data.nat.basic data.finset

open nat

def choose : ℕ → ℕ → ℕ
| _             0 := 1
| 0       (k + 1) := 0
| (n + 1) (k + 1) := choose n k + choose n (succ k)

@[simp] lemma choose_zero_right (n : ℕ) : choose n 0 = 1 := by cases n; refl

@[simp] lemma choose_zero_succ (k : ℕ) : choose 0 (succ k) = 0 := rfl

lemma choose_succ_succ (n k : ℕ) : choose (succ n) (succ k) = choose n k + choose n (succ k) := rfl

lemma choose_eq_zero_of_lt : ∀ {n k}, n < k → choose n k = 0
| _             0 hk := absurd hk dec_trivial
| 0       (k + 1) hk := choose_zero_succ _
| (n + 1) (k + 1) hk := 
  have hnk : n < k, from lt_of_succ_lt_succ hk,
  have hnk1 : n < k + 1, from lt_of_succ_lt hk,
  by rw [choose_succ_succ, choose_eq_zero_of_lt hnk, choose_eq_zero_of_lt hnk1]

@[simp] lemma choose_self (n : ℕ) : choose n n = 1 :=
by induction n; simp [*, choose, choose_eq_zero_of_lt (lt_succ_self _)]

@[simp] lemma choose_succ_self (n : ℕ) : choose n (succ n) = 0 := 
choose_eq_zero_of_lt (lt_succ_self _)

@[simp] lemma choose_one_right (n : ℕ) : choose n 1 = n :=
by induction n; simp [*, choose]

lemma choose_pos : ∀ {n k}, k ≤ n → 0 < choose n k
| 0             _ hk := by rw [eq_zero_of_le_zero hk]; exact dec_trivial
| (n + 1)       0 hk := by simp; exact dec_trivial
| (n + 1) (k + 1) hk := add_pos_of_pos_of_nonneg (choose_pos (le_of_succ_le_succ hk)) (zero_le _)


lemma succ_mul_choose_eq : ∀ n k, succ n * choose n k = choose (succ n) (succ k) * succ k
| 0             0 := dec_trivial
| 0       (k + 1) := by simp [choose]
| (n + 1)       0 := by simp
| (n + 1) (k + 1) := 
  by rw [choose_succ_succ (succ n) (succ k), add_mul, ← succ_mul_choose_eq, mul_succ,
  ←succ_mul_choose_eq, add_right_comm, ←mul_add, ← choose_succ_succ, ← succ_mul] 

lemma choose_mul_fact_mul_fact : ∀ {n k}, k ≤ n → choose n k * fact k * fact (n - k) = fact n
| 0              _ hk := by simp [eq_zero_of_le_zero hk]
| (n + 1)        0 hk := by simp
| (n + 1) (succ k) hk := 
begin
  cases lt_or_eq_of_le hk with hk₁ hk₁,
  { have h : choose n k * fact (succ k) * fact (n - k) = succ k * fact n :=
      by rw ← choose_mul_fact_mul_fact (le_of_succ_le_succ hk);
      simp [fact_succ, mul_comm, mul_left_comm],
    have h₁ : fact (n - k) = (n - k) * fact (n - succ k) := 
      by rw [← succ_sub_succ, succ_sub (le_of_lt_succ hk₁), fact_succ],
    have h₂ : choose n (succ k) * fact (succ k) * ((n - k) * fact (n - succ k)) = (n - k) * fact n :=
      by rw ← choose_mul_fact_mul_fact (le_of_lt_succ hk₁); 
      simp [fact_succ, mul_comm, mul_left_comm, mul_assoc],
    have h₃ : k * fact n ≤ n * fact n := mul_le_mul_right _ (le_of_succ_le_succ hk),
  rw [choose_succ_succ, add_mul, add_mul, succ_sub_succ, h, h₁, h₂, ← add_one, add_mul, nat.mul_sub_right_distrib,
      fact_succ, ← nat.add_sub_assoc h₃, add_assoc, ← add_mul, nat.add_sub_cancel_left, add_comm] },
  { simp [hk₁, mul_comm, choose, nat.sub_self] } 
end

theorem choose_eq_fact_div_fact {n k : ℕ} (hk : k ≤ n) : choose n k = fact n / (fact k * fact (n - k)) :=
have h : fact n = choose n k * (fact k * fact (n - k)) :=
    by rw ← mul_assoc; exact (choose_mul_fact_mul_fact hk).symm,
(nat.div_eq_of_eq_mul_left (mul_pos (fact_pos _) (fact_pos _)) h).symm

theorem fact_mul_fact_dvd_fact {n k : ℕ} (hk : k ≤ n) : fact k * fact (n - k) ∣ fact n :=
by rw [←choose_mul_fact_mul_fact hk, mul_assoc]; exact dvd_mul_left _ _

open finset
variables {α : Type*} [decidable_eq α]

private theorem aux₀ (s : finset α) : filter (λ t, card t = 0) (powerset s) = {∅} :=
ext.2 $ λ t, by split; simp {contextual := tt}

private theorem aux₁ (k : ℕ) : filter (λ t, card t = nat.succ k) (powerset (∅ : finset α)) = ∅ :=
ext.2 $ λ t, by simp [(nat.succ_ne_zero k).symm] {contextual := tt}

private theorem aux₂ {a : α} {s t : finset α} (anins : a ∉ s) (tpows : t ∈ powerset s) : a ∉ t :=
λ h, by rw mem_powerset at *; exact anins (mem_of_subset tpows h)

private theorem aux₃ {a : α} {s : finset α} (anins : a ∉ s) (k : ℕ) :
    filter (λ t, card t = nat.succ k) (powerset (insert a s)) =
    filter (λ t, card t = nat.succ k) (powerset s) ∪ image (insert a) (filter (λ t, card t = k) (powerset s)) :=
ext.2 $ λ x, 
by rw [mem_filter, mem_union, mem_filter, mem_image, mem_powerset, mem_powerset];
exact show x ⊆ insert a s ∧ card x = succ k ↔ x ⊆ s ∧ card x = succ k ∨
    ∃ (u : finset α) (H : u ∈ filter (λ (t : finset α), card t = k) (powerset s)), 
    insert a u = x, from
⟨λ ⟨h, h₁⟩,
  or.cases_on (decidable.em (a ∈ x)) 
    (λ hax, or.inr ⟨erase x a, mem_filter.2 ⟨by rwa [mem_powerset, ← subset_insert_iff],
       by rw [card_erase_of_mem hax, h₁, nat.pred_succ]⟩, insert_erase hax⟩ ) $
  λ h₂, or.inl ⟨by rwa [subset_insert_iff, erase_eq_of_not_mem h₂] at h, h₁⟩, 
λ h, 
  or.cases_on h 
    (λ ⟨h, h₁⟩, ⟨subset.trans h (subset_insert _ _), h₁⟩) $
    λ ⟨t, ⟨ht₁, ht₂⟩⟩, begin 
      rw mem_filter at ht₁,
      rw [← ht₂, card_insert_of_not_mem (aux₂ anins ht₁.1), ht₁.2],
      exact ⟨insert_subset_insert _ (mem_powerset.1 ht₁.1), rfl⟩
    end⟩

private theorem aux₄ {a : α} {s : finset α} (anins : a ∉ s) (k : ℕ) :
disjoint (filter (λ t, card t = nat.succ k) (powerset s)) (image (insert a) (filter (λ t, card t = k) (powerset s))) :=
λ t h₁ h₂, 
let ⟨u, ⟨hu₁, hu₂⟩⟩ := mem_image.1 h₂ in
by rw mem_filter at h₁;
  exact (aux₂ anins h₁.1) (hu₂ ▸ mem_insert_self _ _)

private theorem aux₅ {a : α} {s : finset α} (anins : a ∉ s) (k : ℕ) :
  card (image (insert a) (filter (λ t, card t = k) (powerset s))) = card (filter (λ t, card t = k) (powerset s)) :=
begin
  rw card_image_of_inj_on,
  assume x hx y hy hxy,
  rw [mem_filter] at hx hy,
  exact insert_inj_of_not_mem (aux₂ anins hx.1) (aux₂ anins hy.1) hxy,
end

theorem card_subsets_eq_choose (s : finset α) : ∀ k, card (filter (λ t, card t = k) (powerset s)) = choose (card s) k :=
finset.induction_on s (λ k, nat.cases_on k (by rw aux₀; simp) (λ k, by rw aux₁; simp)) $ λ a s has hi k,
nat.cases_on k (by rw aux₀; simp) $ λ k, by
 rw [aux₃ has, card_disjoint_union (aux₄ has k), hi, aux₅ has, hi, 
    card_insert_of_not_mem has, choose_succ_succ, add_comm]
