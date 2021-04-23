/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import combinatorics.partition
import data.multiset.gcd
import group_theory.perm.cycles
import group_theory.sylow

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
    have key := disjoint_prod_right _ (pairwise_cons.mp h2).1,
    cases key.def a,
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
σ.trunc_cycle_factors.lift (λ l, l.1.map (λ (f : perm α), fintype.card f.support))
  (λ ⟨l₁, h₁l₁, h₂l₁, h₃l₁⟩ ⟨l₂, h₁l₂, h₂l₂, h₃l₂⟩, coe_eq_coe.mpr (perm.map _
  (list_cycles_perm_list_cycles (h₁l₁.trans h₁l₂.symm) h₂l₁ h₂l₂ h₃l₁ h₃l₂)))

lemma two_le_of_mem_cycle_type {σ : perm α} {n : ℕ} (h : n ∈ σ.cycle_type) : 2 ≤ n :=
begin
  rw [cycle_type, ←σ.trunc_cycle_factors.out_eq] at h,
  obtain ⟨τ, hτ, rfl⟩ := list.mem_map.mp h,
  have : τ.support.finite := set.finite.of_fintype _,
  rw ←this.card_to_finset,
  exact (σ.trunc_cycle_factors.out.2.2.1 τ hτ).two_le_card_support this
end

lemma one_lt_of_mem_cycle_type {σ : perm α} {n : ℕ} (h : n ∈ σ.cycle_type) : 1 < n :=
two_le_of_mem_cycle_type h

lemma cycle_type_eq {σ : perm α} (l : list (perm α)) (h0 : l.prod = σ)
  (h1 : ∀ σ : perm α, σ ∈ l → σ.is_cycle) (h2 : l.pairwise disjoint) :
  σ.cycle_type = l.map (λ (f : perm α), fintype.card f.support) :=
by rw [cycle_type, trunc.eq σ.trunc_cycle_factors (trunc.mk ⟨l, h0, h1, h2⟩), trunc.lift_mk]

lemma cycle_type_one : (1 : perm α).cycle_type = 0 :=
cycle_type_eq [] rfl (λ _, false.elim) pairwise.nil

lemma cycle_type_eq_zero {σ : perm α} : σ.cycle_type = 0 ↔ σ = 1 :=
begin
  split,
  { intro h,
    obtain ⟨l, h₁l, h₂l, h₃l⟩ := σ.trunc_cycle_factors.out,
    rw [cycle_type_eq l h₁l h₂l h₃l, coe_eq_zero, map_eq_nil] at h,
    exact h₁l.symm.trans (congr_arg _ h) },
  { exact λ h, by rw [h, cycle_type_one] },
end

lemma card_cycle_type_eq_zero {σ : perm α} : σ.cycle_type.card = 0 ↔ σ = 1 :=
by rw [card_eq_zero, cycle_type_eq_zero]

lemma is_cycle.cycle_type {σ : perm α} (hσ : is_cycle σ) :
  σ.cycle_type = [fintype.card σ.support] :=
cycle_type_eq [σ] (mul_one σ) (λ τ hτ, (congr_arg is_cycle (list.mem_singleton.mp hτ)).mpr hσ)
  (pairwise_singleton disjoint σ)

lemma card_cycle_type_eq_one {σ : perm α} : σ.cycle_type.card = 1 ↔ σ.is_cycle :=
begin
  split,
  { intro hσ,
    obtain ⟨l, h₁l, h₂l, h₃l⟩ := σ.trunc_cycle_factors.out,
    rw [cycle_type_eq l h₁l h₂l h₃l, coe_card, length_map] at hσ,
    obtain ⟨τ, hτ⟩ := length_eq_one.mp hσ,
    rw [←h₁l, hτ, list.prod_singleton],
    apply h₂l,
    rw [hτ, list.mem_singleton] },
  { exact λ hσ, by rw [hσ.cycle_type, coe_card, length_singleton] },
end

lemma disjoint.cycle_type {σ τ : perm α} (h : disjoint σ τ) :
  (σ * τ).cycle_type = σ.cycle_type + τ.cycle_type :=
begin
  obtain ⟨l₁, h₁l₁, h₂l₁, h₃l₁⟩ := σ.trunc_cycle_factors.out,
  obtain ⟨l₂, h₁l₂, h₂l₂, h₃l₂⟩ := τ.trunc_cycle_factors.out,
  rw [cycle_type_eq l₁ h₁l₁ h₂l₁ h₃l₁, cycle_type_eq l₂ h₁l₂ h₂l₂ h₃l₂,
      cycle_type_eq (l₁ ++ l₂) _ _ _, map_append, ←coe_add],
  { rw [prod_append, h₁l₁, h₁l₂] },
  { exact λ f hf, (mem_append.mp hf).elim (h₂l₁ f) (h₂l₂ f) },
  { refine pairwise_append.mpr ⟨h₃l₁, h₃l₂, λ f hf g hg a, by_contra (λ H, _)⟩,
    simp only [exists_prop, set.mem_empty_eq, and_true, set.mem_inter_eq, set.bot_eq_empty,
               ne.def, not_false_iff, perm.mem_support, not_forall, set.inf_eq_inter] at H,
    exact (((congr_arg2 disjoint h₁l₁ h₁l₂).mpr h).def a).elim
      (ne_of_eq_of_ne ((mem_list_cycles_iff h₂l₁ h₃l₁ (h₂l₁ f hf) H.1).1 hf 1).symm H.1)
      (ne_of_eq_of_ne ((mem_list_cycles_iff h₂l₂ h₃l₂ (h₂l₂ g hg) H.2).1 hg 1).symm H.2) }
end

lemma cycle_type_inv (σ : perm α) : σ⁻¹.cycle_type = σ.cycle_type :=
begin
  refine cycle_induction_on _ σ rfl _ _,
  { intros σ hσ,
    rw [hσ.cycle_type, hσ.inv.cycle_type],
    congr' 4,
    simp },
  { intros σ τ hστ hσ hτ,
    rw [mul_inv_rev, hστ.cycle_type, ←hσ, ←hτ, add_comm],
    exact hστ.symm.inv_left.inv_right.cycle_type }
end

lemma sum_cycle_type (σ : perm α) : σ.cycle_type.sum = (fintype.card σ.support) :=
begin
  refine cycle_induction_on _ σ _ _ _,
  { simp [cycle_type_one] },
  { intros σ hσ,
    simp [hσ.cycle_type] },
  { intros σ τ hστ hσ hτ,
    rw [hστ.cycle_type, sum_add, hσ, hτ],
    convert (hστ.card_support_mul (set.finite.of_fintype _)
      (set.finite.of_fintype _) (set.finite.of_fintype _)).symm;
    rw set.finite.card_to_finset }
end

lemma sign_of_cycle_type (σ : perm α) :
  sign σ = (σ.cycle_type.map (λ n, -(-1 : units ℤ) ^ n)).prod :=
cycle_induction_on (λ τ : perm α, sign τ = (τ.cycle_type.map (λ n, -(-1 : units ℤ) ^ n)).prod) σ
  (by rw [sign_one, cycle_type_one, map_zero, prod_zero])
  (λ σ hσ, by rw [hσ.sign (set.finite.of_fintype _), hσ.cycle_type, coe_map, coe_prod,
    list.map_singleton, list.prod_singleton, set.finite.card_to_finset])
  (λ σ τ hστ hσ hτ, by rw [sign_mul, hσ, hτ, hστ.cycle_type, map_add, prod_add])

lemma lcm_cycle_type (σ : perm α) : σ.cycle_type.lcm = order_of σ :=
cycle_induction_on (λ τ : perm α, τ.cycle_type.lcm = order_of τ) σ
  (by rw [cycle_type_one, lcm_zero, order_of_one])
  (λ σ hσ, by rw [hσ.cycle_type, ←singleton_coe, lcm_singleton,
    order_of_is_cycle hσ (set.finite.of_fintype _), set.finite.card_to_finset, nat.normalize_eq])
  (λ σ τ hστ hσ hτ, by rw [hστ.cycle_type, lcm_add, nat.lcm_eq_lcm, hστ.order_of, hσ, hτ])

lemma dvd_of_mem_cycle_type {σ : perm α} {n : ℕ} (h : n ∈ σ.cycle_type) : n ∣ order_of σ :=
begin
  rw ← lcm_cycle_type,
  exact dvd_lcm h,
end

lemma cycle_type_prime_order {σ : perm α} (hσ : (order_of σ).prime) :
  ∃ n : ℕ, σ.cycle_type = repeat (order_of σ) (n + 1) :=
begin
  rw eq_repeat_of_mem (λ n hn, or_iff_not_imp_left.mp
    (hσ.2 n (dvd_of_mem_cycle_type hn)) (ne_of_gt (one_lt_of_mem_cycle_type hn))),
  use σ.cycle_type.card - 1,
  rw nat.sub_add_cancel,
  rw [nat.succ_le_iff, pos_iff_ne_zero, ne, card_cycle_type_eq_zero],
  rintro rfl,
  rw order_of_one at hσ,
  exact hσ.ne_one rfl,
end

lemma is_cycle_of_prime_order {σ : perm α} (h1 : (order_of σ).prime)
  (h2 : fintype.card σ.support < 2 * (order_of σ)) : σ.is_cycle :=
begin
  obtain ⟨n, hn⟩ := cycle_type_prime_order h1,
  rw [←σ.sum_cycle_type, hn, multiset.sum_repeat, nsmul_eq_mul, nat.cast_id, mul_lt_mul_right
      (order_of_pos σ), nat.succ_lt_succ_iff, nat.lt_succ_iff, nat.le_zero_iff] at h2,
  rw [←card_cycle_type_eq_one, hn, card_repeat, h2],
end

end cycle_type

lemma is_cycle_of_prime_order' {σ : perm α} (h1 : (order_of σ).prime)
  (h2 : fintype.card α < 2 * (order_of σ)) : σ.is_cycle :=
begin
  classical,
  refine is_cycle_of_prime_order h1 (lt_of_le_of_lt _ h2),
  convert fintype.card_subtype_le _,
  exact support.decidable_pred
end

lemma is_cycle_of_prime_order'' {σ : perm α} (h1 : (fintype.card α).prime)
  (h2 : order_of σ = fintype.card α) : σ.is_cycle :=
is_cycle_of_prime_order' ((congr_arg nat.prime h2).mpr h1)
begin
  classical,
  rw [←one_mul (fintype.card α), ←h2, mul_lt_mul_right (order_of_pos σ)],
  exact one_lt_two,
end

lemma subgroup_eq_top_of_swap_mem [decidable_eq α] {H : subgroup (perm α)}
  [d : decidable_pred (∈ H)] {τ : perm α} (h0 : (fintype.card α).prime)
  (h1 : fintype.card α ∣ fintype.card H) (h2 : τ ∈ H) (h3 : is_swap τ) :
  H = ⊤ :=
begin
  haveI : fact (fintype.card α).prime := ⟨h0⟩,
  obtain ⟨σ, hσ⟩ := sylow.exists_prime_order_of_dvd_card (fintype.card α) h1,
  have hσ1 : order_of (σ : perm α) = fintype.card α := (order_of_subgroup σ).trans hσ,
  have hσ2 : is_cycle ↑σ := is_cycle_of_prime_order'' h0 hσ1,
  have hσ3 : (σ : perm α).support = ⊤,
  { have hs : (σ : perm α).support.finite := set.finite.of_fintype _,
    rw [set.top_eq_univ, ←finset.coe_univ, ←hs.coe_to_finset, finset.coe_inj],
    exact (finset.eq_univ_of_card (hs.to_finset) ((order_of_is_cycle hσ2 hs).symm.trans hσ1)) },
  have hσ4 : subgroup.closure {↑σ, τ} = ⊤ := closure_prime_cycle_swap h0 hσ2 hσ3 h3,
  rw [eq_top_iff, ←hσ4, subgroup.closure_le, set.insert_subset, set.singleton_subset_iff],
  exact ⟨subtype.mem σ, h2⟩,
end

section partition

variables [decidable_eq α]

/-- The partition corresponding to a permutation -/
def partition (σ : perm α) : partition (fintype.card α) :=
{ parts := σ.cycle_type + repeat 1 (fintype.card α - fintype.card σ.support),
  parts_pos := λ n hn,
  begin
    cases mem_add.mp hn with hn hn,
    { exact zero_lt_one.trans (one_lt_of_mem_cycle_type hn) },
    { exact lt_of_lt_of_le zero_lt_one (ge_of_eq (multiset.eq_of_mem_repeat hn)) },
  end,
  parts_sum := by { rw [sum_add, sum_cycle_type, multiset.sum_repeat, nsmul_eq_mul,
    nat.cast_id, mul_one, nat.add_sub_cancel'],
    convert fintype.card_subtype_le _,
    exact support.decidable_pred } }

end partition

end equiv.perm
