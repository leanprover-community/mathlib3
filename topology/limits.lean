/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

A collection of limit properties.
-/
import algebra.big_operators algebra.group_power topology.real topology.infinite_sum
noncomputable theory

open classical set finset function filter
local attribute [instance] decidable_inhabited prop_decidable

infix ` ^ ` := pow_nat

section linear_ordered_field
variables {α : Type*} [linear_ordered_field α] {a : α}

lemma one_lt_inv (h₁ : 0 < a) (h₂ : a < 1) : 1 < a⁻¹ :=
by rw [inv_eq_one_div, lt_div_iff h₁]; simp [h₂]

end linear_ordered_field

section division_ring
variables {α : Type*} [division_ring α] {a b : α}

lemma div_eq_mul_inv : a / b = a * b⁻¹ :=
by rw [div_eq_mul_one_div, inv_eq_one_div]

lemma neg_inv (h : a ≠ 0) : - a⁻¹ = (- a)⁻¹ :=
by rwa [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

end division_ring

section of_nat
variables {α : Type*} [semiring α] {n : ℕ}

@[simp] def of_nat : ℕ → α
| 0            := 0
| (nat.succ n) := of_nat n + 1

@[simp] lemma of_nat_add : ∀{m}, of_nat (n + m) = (of_nat n + of_nat m : α)
| 0       := by simp
| (m + 1) := calc of_nat (n + (m + 1)) = of_nat (nat.succ (n + m)) :
    by rw [nat.succ_eq_add_one]; simp
  ... = (of_nat n + of_nat (nat.succ m) : α) :
    by simp [of_nat_add]

@[simp] lemma of_nat_one : of_nat 1 = (1 : α) :=
calc of_nat 1 = 0 + 1 : rfl
 ... = (1:α) : by simp

@[simp] lemma of_nat_mul : ∀{m}, of_nat (n * m) = (of_nat n * of_nat m : α)
| 0       := by simp
| (m + 1) := by simp [mul_add, of_nat_mul]

@[simp] lemma of_nat_bit0 : of_nat (bit0 n) = (bit0 (of_nat n) : α) := of_nat_add

@[simp] lemma of_nat_bit1 : of_nat (bit0 n) = (bit0 (of_nat n) : α) := of_nat_add

lemma of_nat_sub {α : Type*} [ring α] {n m : ℕ} (h : m ≤ n) :
  of_nat (n - m) = (of_nat n - of_nat m : α) :=
calc of_nat (n - m) = (of_nat ((n - m) + m) - of_nat m : α) : by simp
  ... = (of_nat n - of_nat m : α) : by rw [nat.sub_add_cancel h]

end of_nat

lemma int_of_nat_eq_of_nat : ∀{n : ℕ}, int.of_nat n = of_nat n
| 0       := rfl
| (n + 1) := by simp [int.of_nat_add, int.of_nat_one, @int_of_nat_eq_of_nat n]

lemma rat_of_nat_eq_of_nat : ∀{n : ℕ}, (↑(of_nat n : ℤ) : ℚ) = of_nat n
| 0       := rfl
| (n + 1) :=
  by rw [of_nat_add, rat.coe_int_add, of_nat_one, rat.coe_int_one, rat_of_nat_eq_of_nat]; simp

lemma rat_coe_eq_of_nat {n : ℕ} : (↑n : ℚ) = of_nat n :=
show ↑(int.of_nat n) = (of_nat n : ℚ), by rw [int_of_nat_eq_of_nat, rat_of_nat_eq_of_nat]

lemma real_of_rat_of_nat_eq_of_nat : ∀{n : ℕ}, of_rat (of_nat n) = of_nat n
| 0     := rfl
| (n+1) := by simp [of_rat_add.symm, of_rat_one.symm, real_of_rat_of_nat_eq_of_nat]

section of_nat_order
variables {α : Type*} [linear_ordered_semiring α]

lemma zero_le_of_nat : ∀{n}, 0 ≤ (of_nat n : α)
| 0       := le_refl 0
| (n + 1) := le_add_of_le_of_nonneg zero_le_of_nat (zero_le_one)

lemma of_nat_pos : ∀{n}, 0 < n → 0 < (of_nat n : α)
| 0       h := (lt_irrefl 0 h).elim
| (n + 1) h := by simp; exact lt_add_of_le_of_pos zero_le_of_nat zero_lt_one

lemma of_nat_le_of_nat {n m : ℕ} (h : n ≤ m) : of_nat n ≤ (of_nat m : α) :=
let ⟨k, hk⟩ := nat.le.dest h in
by simp [zero_le_of_nat, hk.symm]

lemma of_nat_le_of_nat_iff {n m : ℕ} : of_nat n ≤ (of_nat m : α) ↔ n ≤ m :=
suffices of_nat n ≤ (of_nat m : α) → n ≤ m,
  from iff.intro this of_nat_le_of_nat,
begin
  induction n generalizing m,
  case nat.zero { simp [nat.zero_le] },
  case nat.succ n ih {
    cases m,
    case nat.zero {
      exact assume h,
        have of_nat (n + 1) = (0:α), from le_antisymm h zero_le_of_nat,
        have 1 ≤ (0:α),
          from calc (1:α) ≤ of_nat n + 1 : le_add_of_nonneg_left zero_le_of_nat
            ... = (0:α) : this,
        absurd this $ not_le_of_gt zero_lt_one },
    case nat.succ m {
      exact assume h,
        have 1 + of_nat n ≤ (1 + of_nat m : α), by simp * at *,
        have of_nat n ≤ (of_nat m : α), from le_of_add_le_add_left this,
        show nat.succ n ≤ nat.succ m,
          from nat.succ_le_succ $ ih this } }
end

end of_nat_order

instance : linear_ordered_semiring ℝ := by apply_instance

lemma exists_lt_of_nat {r : ℝ} : ∃n, r < of_nat n :=
let ⟨q, hq⟩ := exists_lt_of_rat r in
⟨rat.nat_ceil q, calc r < of_rat q : hq
  ... ≤ of_rat (↑(int.of_nat $ rat.nat_ceil q)) : of_rat_le_of_rat.mpr $ rat.le_nat_ceil q
  ... = of_nat (rat.nat_ceil q) :
    by simp [int_of_nat_eq_of_nat, rat_of_nat_eq_of_nat, real_of_rat_of_nat_eq_of_nat]⟩

lemma mul_add_one_le_pow {r : ℝ} (hr : 0 ≤ r) : ∀{n}, (of_nat n) * r + 1 ≤ (r + 1) ^ n
| 0       := by simp; exact le_refl 1
| (n + 1) :=
  let h : of_nat n ≥ (0 : ℝ) := @zero_le_of_nat ℝ _ n in
  calc of_nat (n + 1) * r + 1 ≤ (of_nat (n + 1) * r + 1) + r * r * of_nat n :
      le_add_of_le_of_nonneg (le_refl _) (mul_nonneg (mul_nonneg hr hr) h)
    ... = (r + 1) * (of_nat n * r + 1) : by simp [mul_add, add_mul]
    ... ≤ (r + 1) * (r + 1) ^ n : mul_le_mul (le_refl _) mul_add_one_le_pow
      (add_nonneg (mul_nonneg h hr) zero_le_one) (add_nonneg hr zero_le_one)

lemma tendsto_pow_at_top_at_top_of_gt_1 {r : ℝ} (h : r > 1) : tendsto (λn:ℕ, r ^ n) at_top at_top :=
tendsto_infi $ assume p, tendsto_principal $
  let ⟨n, hn⟩ := @exists_lt_of_nat (p / (r - 1)) in
  have hn_nn : (0:ℝ) ≤ of_nat n, from (@zero_le_of_nat ℝ _ n),
  have r - 1 > 0, from sub_lt_iff.mp $ by simp; assumption,
  have p ≤ r ^ n,
    from calc p = (p / (r - 1)) * (r - 1) : (div_mul_cancel _ $ ne_of_gt this).symm
      ... ≤ of_nat n * (r - 1) : mul_le_mul (le_of_lt hn) (le_refl _) (le_of_lt this) hn_nn
      ... ≤ of_nat n * (r - 1) + 1 : le_add_of_le_of_nonneg (le_refl _) zero_le_one
      ... ≤ ((r - 1) + 1) ^ n : mul_add_one_le_pow $ le_of_lt this
      ... ≤ r ^ n : by simp; exact le_refl _,
  show {n | p ≤ r ^ n} ∈ at_top.sets,
    from mem_at_top_iff.mpr ⟨n, assume m hnm, le_trans this (pow_le_pow (le_of_lt h) hnm)⟩

lemma tendsto_inverse_at_top_nhds_0 : tendsto (λr:ℝ, r⁻¹) at_top (nhds 0) :=
tendsto_orderable_unbounded (no_top 0) (no_bot 0) $ assume l u hl hu,
  mem_at_top_iff.mpr ⟨u⁻¹ + 1, assume b hb,
    have u⁻¹ < b, from lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one) hb,
    ⟨lt_trans hl $ inv_pos $ lt_trans (inv_pos hu) this,
    lt_of_one_div_lt_one_div hu $
    begin
      rw [inv_eq_one_div],
      simp [-one_div_eq_inv, div_div_eq_mul_div, div_one],
      simp [this]
    end⟩⟩

lemma map_succ_at_top_eq : map nat.succ at_top = at_top :=
le_antisymm
  (assume s hs,
    let ⟨b, hb⟩ := mem_at_top_iff.mp hs in
    mem_at_top_iff.mpr ⟨b, assume c hc, hb (c + 1) $ le_trans hc $ nat.le_succ _⟩)
  (assume s hs,
    let ⟨b, hb⟩ := mem_at_top_iff.mp hs in
    mem_at_top_iff.mpr ⟨b + 1, assume c,
    match c with
    | 0     := assume h,
      have 0 > 0, from lt_of_lt_of_le (lt_add_of_le_of_pos (nat.zero_le _) zero_lt_one) h,
      (lt_irrefl 0 this).elim
    | (c+1) := assume h, hb _ (nat.le_of_succ_le_succ h)
    end⟩)

lemma tendsto_comp_succ_at_top_iff {α : Type*} {f : ℕ → α} {x : filter α} :
  tendsto (λn, f (nat.succ n)) at_top x ↔ tendsto f at_top x :=
calc tendsto (f ∘ nat.succ) at_top x ↔ tendsto f (map nat.succ at_top) x : by simp [tendsto, map_map]
 ... ↔ _ : by rw [map_succ_at_top_eq]

lemma tendsto_pow_at_top_nhds_0_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  tendsto (λn, r^n) at_top (nhds 0) :=
by_cases
  (assume : r = 0, tendsto_comp_succ_at_top_iff.mp $ by simp [pow_succ, this, tendsto_const_nhds])
  (assume : r ≠ 0,
    have tendsto (λn, (r⁻¹ ^ n)⁻¹) at_top (nhds 0),
      from tendsto_compose
        (tendsto_pow_at_top_at_top_of_gt_1 $ one_lt_inv (lt_of_le_of_ne h₁ this.symm) h₂)
        tendsto_inverse_at_top_nhds_0,
    tendsto_cong this $ univ_mem_sets' $ assume a, by simp [*, pow_inv])

lemma sum_geometric' {r : ℝ} (h : r ≠ 0) :
  ∀{n}, (upto n).sum (λi, (r + 1) ^ i) = ((r + 1) ^ n - 1) / r
| 0     := by simp [zero_div]
| (n+1) := by simp [@sum_geometric' n, h, pow_succ, add_div_eq_mul_add_div, add_mul]

lemma sum_geometric {r : ℝ} {n : ℕ} (h : r ≠ 1) :
  (upto n).sum (λi, r ^ i) = (r ^ n - 1) / (r - 1) :=
calc (upto n).sum (λi, r ^ i) = (upto n).sum (λi, ((r - 1) + 1) ^ i) :
    by simp
  ... = (((r - 1) + 1) ^ n - 1) / (r - 1) :
    sum_geometric' $ by simp [sub_eq_iff_eq_add, -sub_eq_add_neg, h]
  ... = (r ^ n - 1) / (r - 1) :
    by simp

lemma is_sum_geometric {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  is_sum (λn, r ^ n) (1 / (1 - r)) :=
have r ≠ 1, from ne_of_lt h₂,
have r + -1 ≠ 0,
  by rw [←sub_eq_add_neg, ne, sub_eq_iff_eq_add]; simp; assumption,
have tendsto (λn, (r ^ n - 1) * (r - 1)⁻¹) at_top (nhds ((0 - 1) * (r - 1)⁻¹)),
  from tendsto_mul
    (tendsto_sub (tendsto_pow_at_top_nhds_0_of_lt_1 h₁ h₂) tendsto_const_nhds) tendsto_const_nhds,
(is_sum_iff_tendsto_nat_of_nonneg $ pow_nonneg h₁).mpr $
  by simp [neg_inv, sum_geometric, div_eq_mul_inv, *] at *
