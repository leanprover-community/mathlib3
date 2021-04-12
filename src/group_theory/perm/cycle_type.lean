/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import group_theory.perm.cycles
import combinatorics.partition
import data.multiset.gcd

/-!
# Cycle Types

In this file we define the cycle type of a partition.

## Main definitions

- `σ.cycle_type` where `σ` is a permutation of a `fintype`
- `σ.partition` where `σ` is a permutation of a `fintype`

## Main results

- `sum_cycle_type` : The sum of `σ.cycle_type` equals `σ.support.card`
- `lcm_cycle_type` : The lcm of `σ.cycle_type` equals `order_of σ`
-/

namespace equiv.perm
open equiv list multiset

variables {α : Type*} [fintype α]

section cycle_type

lemma mem_list_cycles_iff {l : list (perm α)} (h1 : ∀ σ : perm α, σ ∈ l → σ.is_cycle)
 (h2 : l.pairwise disjoint) {σ : perm α} (h3 : σ.is_cycle) {a : α} (h4 : σ a ≠ a) :
 σ ∈ l ↔ ∀ k : ℕ, (σ ^ k) a = (l.prod ^ k) a :=
begin
  induction l with τ l ih,
  { exact ⟨false.elim, λ h, h4 (h 1)⟩ },
  { rw [mem_cons_iff, list.prod_cons,
        ih (λ σ hσ, h1 σ (list.mem_cons_of_mem τ hσ)) (pairwise_of_pairwise_cons h2)],
    have key := disjoint_prod_list_of_disjoint (pairwise_cons.mp h2).1,
    cases key a,
    { simp_rw [key.mul_comm, commute.mul_pow key.mul_comm.symm, mul_apply,
        pow_apply_eq_self_of_apply_eq_self h, or_iff_right_iff_imp],
      rintro rfl,
      exact (h4 h).elim },
    { simp_rw [commute.mul_pow key.mul_comm, mul_apply, pow_apply_eq_self_of_apply_eq_self h],
      rw [or_iff_left_of_imp (λ h : (∀ k : ℕ, (σ ^ k) a = a), (h4 (h 1)).elim)],
      split,
      { exact λ h k, by rw h },
      { intro h5,
        have hτa : τ a ≠ a := ne_of_eq_of_ne (h5 1).symm h4,
        ext b,
        by_cases hσb : σ b = b,
        { by_cases hτb : τ b = b,
          { rw [hσb, hτb] },
          { obtain ⟨n, rfl⟩ := ((h1 τ (list.mem_cons_self τ l))).exists_pow_eq hτa hτb,
            rw [←mul_apply τ, ←pow_succ, ←h5, ←h5, pow_succ, mul_apply] } },
        { obtain ⟨n, rfl⟩ := h3.exists_pow_eq h4 hσb,
          rw [←mul_apply, ←pow_succ, h5, h5, pow_succ, mul_apply] } } } },
end

lemma list_cycles_perm_list_cycles {l₁ l₂ : list (perm α)} (h₀ : l₁.prod = l₂.prod)
  (h₁l₁ : ∀ σ : perm α, σ ∈ l₁ → σ.is_cycle) (h₁l₂ : ∀ σ : perm α, σ ∈ l₂ → σ.is_cycle)
  (h₂l₁ : l₁.pairwise disjoint) (h₂l₂ : l₂.pairwise disjoint) :
  l₁ ~ l₂ :=
begin
  classical,
  have h₃l₁ : (1 : perm α) ∉ l₁ := λ h, (h₁l₁ 1 h).ne_one rfl,
  have h₃l₂ : (1 : perm α) ∉ l₂ := λ h, (h₁l₂ 1 h).ne_one rfl,
  refine (perm_ext (nodup_of_pairwise_disjoint h₃l₁ h₂l₁)
    (nodup_of_pairwise_disjoint h₃l₂ h₂l₂)).mpr (λ σ, _),
  by_cases hσ : σ.is_cycle,
  { obtain ⟨a, ha⟩ := not_forall.mp (mt ext hσ.ne_one),
    rw [mem_list_cycles_iff h₁l₁ h₂l₁ hσ ha, mem_list_cycles_iff h₁l₂ h₂l₂ hσ ha, h₀] },
  { exact iff_of_false (mt (h₁l₁ σ) hσ) (mt (h₁l₂ σ) hσ) },
end

variables [decidable_eq α]

/-- The cycle type of a permutation -/
def cycle_type (σ : perm α) : multiset ℕ :=
σ.trunc_cycle_factors.lift (λ l, l.1.map (finset.card ∘ support))
  (λ l₁ l₂, coe_eq_coe.mpr (perm.map _
  (list_cycles_perm_list_cycles (l₁.2.1.trans l₂.2.1.symm) l₁.2.2.1 l₂.2.2.1 l₁.2.2.2 l₂.2.2.2)))

lemma two_le_of_mem_cycle_type {σ : perm α} {n : ℕ} (h : n ∈ σ.cycle_type) : 2 ≤ n :=
begin
  rw [cycle_type, ←σ.trunc_cycle_factors.out_eq] at h,
  obtain ⟨τ, hτ, rfl⟩ := list.mem_map.mp h,
  exact (σ.trunc_cycle_factors.out.2.2.1 τ hτ).two_le_card_support,
end

lemma one_lt_of_mem_cycle_type {σ : perm α} {n : ℕ} (h : n ∈ σ.cycle_type) : 1 < n :=
two_le_of_mem_cycle_type h

lemma cycle_type_eq {σ : perm α} (l : list (perm α)) (h0 : l.prod = σ)
  (h1 : ∀ σ : perm α, σ ∈ l → σ.is_cycle) (h2 : l.pairwise disjoint) :
  σ.cycle_type = l.map (finset.card ∘ support) :=
by rw [cycle_type, trunc.eq σ.trunc_cycle_factors (trunc.mk ⟨l, h0, h1, h2⟩), trunc.lift_mk]

lemma cycle_type_one : (1 : perm α).cycle_type = 0 :=
cycle_type_eq [] rfl (λ _, false.elim) pairwise.nil

lemma cycle_type_eq_zero {σ : perm α} : σ.cycle_type = 0 ↔ σ = 1 :=
begin
  split,
  { intro h,
    let x := σ.trunc_cycle_factors.out,
    rw [cycle_type_eq x.1 x.2.1 x.2.2.1 x.2.2.2, coe_eq_zero, map_eq_nil] at h,
    exact x.2.1.symm.trans (congr_arg _ h) },
  { exact λ h, by rw [h, cycle_type_one] },
end

lemma card_cycle_type_eq_zero {σ : perm α} : σ.cycle_type.card = 0 ↔ σ = 1 :=
by rw [card_eq_zero, cycle_type_eq_zero]

lemma is_cycle.cycle_type {σ : perm α} (hσ : is_cycle σ) : σ.cycle_type = [σ.support.card] :=
cycle_type_eq [σ] (mul_one σ) (λ τ hτ, (congr_arg is_cycle (list.mem_singleton.mp hτ)).mpr hσ)
  (pairwise_singleton disjoint σ)

lemma card_cycle_type_eq_one {σ : perm α} : σ.cycle_type.card = 1 ↔ σ.is_cycle :=
begin
  split,
  { intro hσ,
    let x := σ.trunc_cycle_factors.out,
    rw [cycle_type_eq x.1 x.2.1 x.2.2.1 x.2.2.2, coe_card, length_map] at hσ,
    obtain ⟨τ, hτ⟩ := length_eq_one.mp hσ,
    rw [←x.2.1, hτ, list.prod_singleton],
    apply x.2.2.1,
    rw [hτ, list.mem_singleton] },
  { exact λ hσ, by rw [hσ.cycle_type, coe_card, length_singleton] },
end

lemma disjoint.cycle_type {σ τ : perm α} (h : disjoint σ τ) :
  (σ * τ).cycle_type = σ.cycle_type + τ.cycle_type :=
begin
  let x := σ.trunc_cycle_factors.out,
  let y := τ.trunc_cycle_factors.out,
  rw [cycle_type_eq x.1 x.2.1 x.2.2.1 x.2.2.2, cycle_type_eq y.1 y.2.1 y.2.2.1 y.2.2.2,
      cycle_type_eq (x.1 ++ y.1) _ _ _, map_append, ←coe_add],
  { rw [prod_append, x.2.1, y.2.1] },
  { exact λ f hf, (mem_append.mp hf).elim (x.2.2.1 f) (y.2.2.1 f) },
  { refine pairwise_append.mpr ⟨x.2.2.2, y.2.2.2, λ f hf g hg a, by_contra (λ H, _)⟩,
    rw not_or_distrib at H,
    exact ((congr_arg2 disjoint x.2.1 y.2.1).mpr h a).elim
      (ne_of_eq_of_ne ((mem_list_cycles_iff x.2.2.1 x.2.2.2 (x.2.2.1 f hf) H.1).1 hf 1).symm H.1)
      (ne_of_eq_of_ne ((mem_list_cycles_iff y.2.2.1 y.2.2.2 (y.2.2.1 g hg) H.2).1 hg 1).symm H.2) }
end

lemma cycle_type_inv (σ : perm α) : σ⁻¹.cycle_type = σ.cycle_type :=
cycle_induction_on (λ τ : perm α, τ⁻¹.cycle_type = τ.cycle_type) σ rfl
  (λ σ hσ, by rw [hσ.cycle_type, hσ.inv.cycle_type, support_inv])
  (λ σ τ hστ hσ hτ, by rw [mul_inv_rev, hστ.cycle_type, ←hσ, ←hτ, add_comm,
    disjoint.cycle_type (λ x, or.imp (λ h : τ x = x, inv_eq_iff_eq.mpr h.symm)
    (λ h : σ x = x, inv_eq_iff_eq.mpr h.symm) (hστ x).symm)])

lemma sum_cycle_type (σ : perm α) : σ.cycle_type.sum = σ.support.card :=
cycle_induction_on (λ τ : perm α, τ.cycle_type.sum = τ.support.card) σ
  (by rw [cycle_type_one, sum_zero, support_one, finset.card_empty])
  (λ σ hσ, by rw [hσ.cycle_type, coe_sum, list.sum_singleton])
  (λ σ τ hστ hσ hτ, by rw [hστ.cycle_type, sum_add, hσ, hτ, hστ.card_support_mul])

lemma sign_of_cycle_type (σ : perm α) :
  sign σ = (σ.cycle_type.map (λ n, -(-1 : units ℤ) ^ n)).prod :=
cycle_induction_on (λ τ : perm α, sign τ = (τ.cycle_type.map (λ n, -(-1 : units ℤ) ^ n)).prod) σ
  (by rw [sign_one, cycle_type_one, map_zero, prod_zero])
  (λ σ hσ, by rw [hσ.sign, hσ.cycle_type, coe_map, coe_prod,
    list.map_singleton, list.prod_singleton])
  (λ σ τ hστ hσ hτ, by rw [sign_mul, hσ, hτ, hστ.cycle_type, map_add, prod_add])

lemma lcm_cycle_type (σ : perm α) : σ.cycle_type.lcm = order_of σ :=
cycle_induction_on (λ τ : perm α, τ.cycle_type.lcm = order_of τ) σ
  (by rw [cycle_type_one, lcm_zero, order_of_one])
  (λ σ hσ, by rw [hσ.cycle_type, ←singleton_coe, lcm_singleton, order_of_is_cycle hσ,
    nat.normalize_eq])
  (λ σ τ hστ hσ hτ, by rw [hστ.cycle_type, lcm_add, nat.lcm_eq_lcm, hστ.order_of, hσ, hτ])

lemma dvd_of_mem_cycle_type {σ : perm α} {n : ℕ} (h : n ∈ σ.cycle_type) : n ∣ order_of σ :=
begin
  rw ← lcm_cycle_type,
  exact dvd_lcm h,
end

lemma cycle_type_prime_order {σ : perm α} (hσ : (order_of σ).prime) :
  ∃ n : ℕ, σ.cycle_type = repeat (order_of σ) n.succ :=
begin
  rw eq_repeat_of_mem (λ n hn, or_iff_not_imp_left.mp
    (hσ.2 n (dvd_of_mem_cycle_type hn)) (ne_of_gt (one_lt_of_mem_cycle_type hn))),
  use σ.cycle_type.card.pred,
  rw nat.succ_pred_eq_of_pos,
  rw [pos_iff_ne_zero, ne, card_cycle_type_eq_zero],
  rintro rfl,
  rw order_of_one at hσ,
  exact hσ.ne_one rfl,
end

lemma is_cycle_of_prime_order {σ : perm α} (h1 : (order_of σ).prime)
  (h2 : σ.support.card < 2 * (order_of σ)) : σ.is_cycle :=
begin
  obtain ⟨n, hn⟩ := cycle_type_prime_order h1,
  rw [←σ.sum_cycle_type, hn, multiset.sum_repeat, nsmul_eq_mul, nat.cast_id, mul_lt_mul_right
      (order_of_pos σ), nat.succ_lt_succ_iff, nat.lt_succ_iff, nat.le_zero_iff] at h2,
  rw [←card_cycle_type_eq_one, hn, card_repeat, h2],
end

lemma foo {σ : perm α} {m1 m2 : multiset ℕ} (h : σ.cycle_type = m1 + m2) :
  ∃ (τ π : perm α), σ = τ * π ∧ disjoint τ π ∧ τ.cycle_type = m1 ∧ π.cycle_type = m2 :=
begin
  sorry
end

theorem is_conj_of_cycle_type_eq {σ : perm α} :
  ∀ {τ : perm α}, cycle_type σ = cycle_type τ → is_conj σ τ :=
begin
  apply cycle_induction_on _ σ,
  { intros τ h,
    rw [cycle_type_one, eq_comm, cycle_type_eq_zero] at h,
    rw [h] },
  { intros σ hσ τ h,
    rw [hσ.cycle_type] at h,
    have hτ : τ.is_cycle,
    { rw [← card_cycle_type_eq_one, ← h, coe_card, length, length] },
    apply hσ.is_conj hτ,
    simp only [hτ.cycle_type, and_true, coe_eq_coe, eq_self_iff_true, singleton_perm] at h,
    exact h },
  { intros σ τ hd ihσ ihτ π h,
    rw hd.cycle_type at h,
    obtain ⟨σ', τ', rfl, hd', hσ', hτ'⟩ := foo h.symm,
    exact hd.is_conj_mul (ihσ hσ'.symm) (ihτ hτ'.symm) hd' }
end

end cycle_type

lemma is_cycle_of_prime_order' {σ : perm α} (h1 : (order_of σ).prime)
  (h2 : fintype.card α < 2 * (order_of σ)) : σ.is_cycle :=
begin
  classical,
  exact is_cycle_of_prime_order h1 (lt_of_le_of_lt σ.support.card_le_univ h2),
end

lemma is_cycle_of_prime_order'' {σ : perm α} (h1 : (fintype.card α).prime)
  (h2 : order_of σ = fintype.card α) : σ.is_cycle :=
is_cycle_of_prime_order' ((congr_arg nat.prime h2).mpr h1)
begin
  classical,
  rw [←one_mul (fintype.card α), ←h2, mul_lt_mul_right (order_of_pos σ)],
  exact one_lt_two,
end

section partition

variables [decidable_eq α]

/-- The partition corresponding to a permutation -/
def partition (σ : perm α) : partition (fintype.card α) :=
{ parts := σ.cycle_type + repeat 1 (fintype.card α - σ.support.card),
  parts_pos := λ n hn,
  begin
    cases mem_add.mp hn with hn hn,
    { exact zero_lt_one.trans (one_lt_of_mem_cycle_type hn) },
    { exact lt_of_lt_of_le zero_lt_one (ge_of_eq (multiset.eq_of_mem_repeat hn)) },
  end,
  parts_sum := by rw [sum_add, sum_cycle_type, multiset.sum_repeat, nsmul_eq_mul,
    nat.cast_id, mul_one, nat.add_sub_cancel' σ.support.card_le_univ] }

end partition

end equiv.perm
