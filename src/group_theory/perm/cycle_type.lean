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

section cycle_of_disjoint

variables [decidable_eq α]

lemma cycle_of_mul_eq_cycle_of_left {σ τ : perm α} (hστ : disjoint σ τ) {a : α} (ha : τ a = a) :
  (σ * τ).cycle_of a = σ.cycle_of a :=
begin
  ext b,
  simp_rw [cycle_of_apply, same_cycle, commute.mul_gpow hστ.mul_comm, mul_apply,
    gpow_apply_eq_self_of_apply_eq_self ha],
  by_cases h : ∃ i : ℤ, (σ ^ i) a = b,
  { rw [if_pos, if_pos],
    { obtain ⟨i, rfl⟩ := h,
      rw [←mul_apply, ←mul_apply, mul_assoc],
      simp_rw show τ * σ ^ i = σ ^ i * τ, from commute.gpow_right hστ.mul_comm.symm i,
      rw [mul_apply, mul_apply, ha] },
    { exact h },
    { exact h} },
  { rw [if_neg, if_neg],
    { exact h },
    { exact h } },
end

lemma cycle_of_mul_eq_cycle_of_right {σ τ : perm α} (hστ : disjoint σ τ) {a : α} (ha : σ a = a) :
  (σ * τ).cycle_of a = τ.cycle_of a :=
by rw [hστ.mul_comm, cycle_of_mul_eq_cycle_of_left hστ.symm ha]

lemma cycle_of_mul_eq_iff {σ τ : perm α} (h : disjoint σ τ) {c : perm α} {a : α} (hc : c a ≠ a) :
  (σ * τ).cycle_of a = c ↔ (σ.cycle_of a = c ∨ τ.cycle_of a = c) :=
begin
  have hc' : c ≠ 1 := λ h, hc (ext_iff.mp h a),
  cases (h a) with ha ha,
  { rw [σ.cycle_of_eq_one_iff.mpr ha, or_iff_right_of_imp (λ h, false.elim (hc'.symm h)),
        cycle_of_mul_eq_cycle_of_right h ha] },
  { rw [τ.cycle_of_eq_one_iff.mpr ha, or_iff_left_of_imp (λ h, false.elim (hc'.symm h)),
        cycle_of_mul_eq_cycle_of_left h ha] },
end

lemma is_cycle.cycle_of_eq_iff {σ : perm α} {c : perm α} {a : α} (hc : c a ≠ a) (hσ : σ.is_cycle) :
  σ.cycle_of a = c ↔ c = σ :=
begin
  split,
  { rintro rfl,
    rw [hσ.cycle_of, ite_eq_right_iff],
    intro h,
    rw [hσ.cycle_of, if_pos h] at hc,
    exact (hc rfl).elim },
  { rintro rfl,
    rw [hσ.cycle_of, if_neg hc] },
end

lemma mem_list_cycles_iff_prod_cycle_of_eq {l : list (perm α)}
  (h1 : ∀ σ : perm α, σ ∈ l → σ.is_cycle)
  (h2 : l.pairwise disjoint) {c : perm α} {a : α} (hc : c a ≠ a) :
  c ∈ l ↔ l.prod.cycle_of a = c :=
begin
  induction l with σ l ih,
  { exact ⟨false.elim, λ h, hc (ext_iff.mp (h.symm.trans (cycle_of_one a)) a)⟩ },
  { have x := ih (λ τ hτ, h1 τ (mem_cons_of_mem σ hτ)) (pairwise_of_pairwise_cons h2),
    have y := cycle_of_mul_eq_iff (disjoint_prod_list_of_disjoint (pairwise_cons.mp h2).1) hc,
    have z := (h1 σ (l.mem_cons_self σ)).cycle_of_eq_iff hc,
    rw [mem_cons_iff, list.prod_cons, x, y, z] },
end

end cycle_of_disjoint

section cycle_type

lemma list_cycles_perm_list_cycles {l₁ l₂ : list (perm α)} (h₀ : l₁.prod = l₂.prod)
  (h₁l₁ : ∀ σ : perm α, σ ∈ l₁ → σ.is_cycle) (h₁l₂ : ∀ σ : perm α, σ ∈ l₂ → σ.is_cycle)
  (h₂l₁ : l₁.pairwise disjoint) (h₂l₂ : l₂.pairwise disjoint) :
  l₁ ~ l₂ :=
begin
  classical,
  have h₃l₁ : (1 : perm α) ∉ l₁ := λ h, (h₁l₁ 1 h).ne_one rfl,
  have h₃l₂ : (1 : perm α) ∉ l₂ := λ h, (h₁l₂ 1 h).ne_one rfl,
  refine (perm_ext (nodup_of_pairwise_disjoint h₃l₁ h₂l₁)
    (nodup_of_pairwise_disjoint h₃l₂ h₂l₂)).mpr (λ c, _),
  by_cases hc : c = 1,
  { rw hc,
    exact iff_of_false h₃l₁ h₃l₂ },
  { obtain ⟨a, hc⟩ := not_forall.mp (mt ext hc),
    rw [mem_list_cycles_iff_prod_cycle_of_eq h₁l₁ h₂l₁ hc,
        mem_list_cycles_iff_prod_cycle_of_eq h₁l₂ h₂l₂ hc, h₀] },
end

lemma disjoint.cycle_type_aux {l : list (perm α)} (h1 : l.pairwise disjoint) {a : α}
  (h2 : l.prod a = a) {σ : perm α} (h3 : σ ∈ l) : σ a = a :=
begin
  revert h1 h2 h3,
  induction l with τ l ih,
  { exact λ _ _, false.elim },
  { intros h1 h2 h3,
    rw [list.prod_cons,
        (disjoint_prod_list_of_disjoint (pairwise_cons.mp h1).1).mul_apply_eq_iff] at h2,
    cases ((l.mem_cons_iff σ τ).mp h3) with h4 h4,
    { rw [h4, h2.1] },
    { exact ih (pairwise_of_pairwise_cons h1) h2.2 h4 } },
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
  { refine pairwise_append.mpr ⟨x.2.2.2, y.2.2.2, λ f hf g hg, _⟩,
    rw [←x.2.1, ←y.2.1] at h,
    intro a,
    cases h a with ha ha,
    { exact or.inl (disjoint.cycle_type_aux x.2.2.2 ha hf) },
    { exact or.inr (disjoint.cycle_type_aux y.2.2.2 ha hg) } },
end

lemma sum_cycle_type (σ : perm α) : σ.cycle_type.sum = σ.support.card :=
begin
  apply cycle_induction_on (λ τ : perm α, τ.cycle_type.sum = τ.support.card),
  { rw [cycle_type_one, sum_zero, support_one, finset.card_empty] },
  { intros σ hσ,
    rw [hσ.cycle_type, coe_sum, list.sum_singleton] },
  { intros σ τ hστ hσ hτ,
    rw [hστ.cycle_type, sum_add, hστ.card_support_mul, hσ, hτ] },
end

lemma lcm_cycle_type (σ : perm α) : σ.cycle_type.lcm = order_of σ :=
cycle_induction_on
  (λ τ : perm α, τ.cycle_type.lcm = order_of τ) σ
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

/-!
### 3-cycles
-/

section is_three_cycle

variables [decidable_eq α] {σ : perm α}

/-- A three-cycle is a cycle of length 3. -/
def is_three_cycle (σ : perm α) : Prop := σ.cycle_type = {3}

lemma is_three_cycle.cycle_type (h : is_three_cycle σ) : σ.cycle_type = {3} := h

lemma is_three_cycle.card_support (h : is_three_cycle σ) : σ.support.card = 3 :=
by rw [←sum_cycle_type, h.cycle_type, singleton_eq_singleton, multiset.sum_cons, sum_zero]

lemma card_support_eq_three_iff : σ.support.card = 3 ↔ σ.is_three_cycle :=
begin
  refine ⟨λ h, _, is_three_cycle.card_support⟩,
  by_cases h0 : σ.cycle_type = 0,
  { rw [←sum_cycle_type, h0, sum_zero] at h,
    exact (ne_of_lt zero_lt_three h).elim },
  obtain ⟨n, hn⟩ := exists_mem_of_ne_zero h0,
  by_cases h1 : σ.cycle_type.erase n = 0,
  { rw [←sum_cycle_type, ←cons_erase hn, h1, multiset.sum_singleton] at h,
    rw [is_three_cycle, ←cons_erase hn, h1, h, singleton_eq_singleton] },
  obtain ⟨m, hm⟩ := exists_mem_of_ne_zero h1,
  rw [←sum_cycle_type, ←cons_erase hn, ←cons_erase hm, multiset.sum_cons, multiset.sum_cons] at h,
  linarith [two_le_of_mem_cycle_type hn, two_le_of_mem_cycle_type (mem_of_mem_erase hm)],
end

lemma is_three_cycle.is_cycle (h : is_three_cycle σ) : is_cycle σ :=
by rw [←card_cycle_type_eq_one, h.cycle_type, singleton_eq_singleton, card_singleton]

lemma is_three_cycle.sign (h : is_three_cycle σ) : sign σ = 1 :=
begin
  rw [sign_of_cycle_type, h.cycle_type],
  refl,
end

lemma is_three_cycle.inv {f : perm α} (h : is_three_cycle f) : is_three_cycle (f⁻¹) :=
by rwa [is_three_cycle, cycle_type_inv]

lemma is_three_cycle_swap_mul_swap_same {a b c : α} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
  is_three_cycle (swap a b * swap a c) :=
begin
  suffices h : support (swap a b * swap a c) = {a, b, c},
  { rw [←card_support_eq_three_iff, h],
    simp [ab, ac, bc] },
  apply le_antisymm ((support_mul_le _ _).trans (λ x, _)) (λ x hx, _),
  { simp [ab, ac, bc] },
  { simp only [finset.mem_insert, finset.mem_singleton] at hx,
    rw mem_support,
    simp only [perm.coe_mul, function.comp_app, ne.def],
    obtain rfl | rfl | rfl := hx,
    { rw [swap_apply_left, swap_apply_of_ne_of_ne ac.symm bc.symm],
      exact ac.symm },
    { rw [swap_apply_of_ne_of_ne ab.symm bc, swap_apply_right],
      exact ab },
    { rw [swap_apply_right, swap_apply_left],
      exact bc } }
end

open subgroup

lemma swap_mul_swap_same_mem_closure_three_cycles {a b c : α} (ab : a ≠ b) (ac : a ≠ c) :
  (swap a b * swap a c) ∈ closure {σ : perm α | is_three_cycle σ } :=
begin
  by_cases bc : b = c,
  { subst bc,
    simp [one_mem] },
  exact subset_closure (is_three_cycle_swap_mul_swap_same ab ac bc)
end

lemma is_swap.mul_mem_closure_three_cycles {σ τ : perm α}
  (hσ : is_swap σ) (hτ : is_swap τ) :
  σ * τ ∈ closure {σ : perm α | is_three_cycle σ } :=
begin
  obtain ⟨a, b, ab, rfl⟩ := hσ,
  obtain ⟨c, d, cd, rfl⟩ := hτ,
  by_cases ac : a = c,
  { subst ac,
    exact swap_mul_swap_same_mem_closure_three_cycles ab cd },
  have h' : swap a b * swap c d = swap a b * swap a c * (swap c a * swap c d),
  { simp [swap_comm c a, mul_assoc] },
  rw h',
  exact mul_mem _ (swap_mul_swap_same_mem_closure_three_cycles ab ac)
    (swap_mul_swap_same_mem_closure_three_cycles (ne.symm ac) cd),
end

@[simp]
theorem closure_three_cycles_eq_alternating :
  closure {σ : perm α | is_three_cycle σ} = alternating_subgroup α :=
closure_eq_of_le _ (λ σ hσ, mem_alternating_subgroup.2 hσ.sign) $ λ σ hσ, begin
  suffices hind : ∀ (n : ℕ) (l : list (perm α)) (hl : ∀ g, g ∈ l → is_swap g)
    (hn : l.length = 2 * n), l.prod ∈ closure {σ : perm α | is_three_cycle σ},
  { obtain ⟨l, rfl, hl⟩ := trunc_swap_factors σ,
    obtain ⟨n, hn⟩ := (prod_list_swap_mem_alternating_subgroup_iff_even_length hl).1 hσ,
    exact hind n l hl hn },
  intro n,
  induction n with n ih; intros l hl hn,
  { simp [list.length_eq_zero.1 hn, one_mem] },
  rw [nat.mul_succ] at hn,
  obtain ⟨a, l, rfl⟩ := l.exists_of_length_succ hn,
  rw [list.length_cons, nat.succ_inj'] at hn,
  obtain ⟨b, l, rfl⟩ := l.exists_of_length_succ hn,
  rw [list.prod_cons, list.prod_cons, ← mul_assoc],
  rw [list.length_cons, nat.succ_inj'] at hn,
  exact mul_mem _ (is_swap.mul_mem_closure_three_cycles (hl a (list.mem_cons_self a _))
    (hl b (list.mem_cons_of_mem a (l.mem_cons_self b))))
    (ih _ (λ g hg, hl g (list.mem_cons_of_mem _ (list.mem_cons_of_mem _ hg))) hn),
end

end is_three_cycle

end equiv.perm
