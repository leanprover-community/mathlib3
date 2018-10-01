/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.order_of_element data.nat.totient data.polynomial

universes u v
variables {α : Type u} {β : Type v} [field α]

open function finset polynomial nat

lemma order_of_pow {α : Type*} [group α] [fintype α] [decidable_eq α] (a : α) (n : ℕ) :
  order_of (a ^ n) = order_of a / gcd (order_of a) n :=
dvd_antisymm
(order_of_dvd_of_pow_eq_one
  (by rw [← pow_mul, ← nat.mul_div_assoc _ (gcd_dvd_left _ _), mul_comm,
    nat.mul_div_assoc _ (gcd_dvd_right _ _), pow_mul, pow_order_of_eq_one, _root_.one_pow]))
(have gcd_pos : 0 < gcd (order_of a) n, from gcd_pos_of_pos_left n (order_of_pos a),
  have hdvd : order_of a ∣ n * order_of (a ^ n),
    from order_of_dvd_of_pow_eq_one (by rw [pow_mul, pow_order_of_eq_one]),
  coprime.dvd_of_dvd_mul_right (coprime_div_gcd_div_gcd gcd_pos)
    (dvd_of_mul_dvd_mul_right gcd_pos
      (by rwa [nat.div_mul_cancel (gcd_dvd_left _ _), mul_assoc,
          nat.div_mul_cancel (gcd_dvd_right _ _), mul_comm])))

def units_equiv_ne_zero (α : Type*) [field α] : units α ≃ {a : α | a ≠ 0} :=
⟨λ a, ⟨a.1, units.ne_zero _⟩, λ a, units.mk0 _ a.2, λ ⟨_, _, _, _⟩, units.ext rfl, λ ⟨_, _⟩, rfl⟩

@[simp] lemma coe_units_equiv_ne_zero (a : units α) : ((units_equiv_ne_zero α a) : α) = a := rfl

namespace finite_field

variables [fintype α] [decidable_eq α]

instance : fintype (units α) :=
by haveI := set_fintype {a : α | a ≠ 0}; exact
fintype.of_equiv _ (units_equiv_ne_zero α).symm

lemma card_units : fintype.card (units α) = fintype.card α - 1 :=
begin
  rw [eq_comm, nat.sub_eq_iff_eq_add (fintype.card_pos_iff.2 ⟨(0 : α)⟩)],
  haveI := set_fintype {a : α | a ≠ 0},
  haveI := set_fintype (@set.univ α),
  rw [fintype.card_congr (units_equiv_ne_zero _),
    ← @set.card_insert _ _ {a : α | a ≠ 0} _ (not_not.2 (eq.refl (0 : α)))
    (set.fintype_insert _ _), fintype.card_congr (equiv.set.univ α).symm],
  congr; simp [set.ext_iff, classical.em]
end

lemma card_nth_roots_units {n : ℕ} (hn : 0 < n)
  (a : units α) : (univ.filter (λ b, b ^ n = a)).card = (nth_roots n (a : α)).card :=
card_congr (λ a _, a)
  (by simp [mem_nth_roots hn, (units.coe_pow _ _).symm, -units.coe_pow, units.ext_iff.symm])
  (by simp [units.ext_iff.symm])
  (λ b hb, have hb0 : b ≠ 0, from λ h,
    units.coe_ne_zero a $ by rwa [mem_nth_roots hn, h, _root_.zero_pow hn, eq_comm] at hb,
    ⟨units.mk0 _ hb0, by simp [units.ext_iff, (mem_nth_roots hn).1 hb]⟩)

lemma card_pow_eq_one_eq_order_of (a : units α) :
  (univ.filter (λ b : units α, b ^ order_of a = 1)).card = order_of a :=
le_antisymm
(by rw card_nth_roots_units (order_of_pos a) 1; exact card_nth_roots _ _)
(calc order_of a = @fintype.card (gpowers a) (id _) : order_eq_card_gpowers
  ... ≤ @fintype.card (↑(univ.filter (λ b : units α, b ^ order_of a = 1)) : set (units α))
  (set.fintype_of_finset _ (λ _, iff.rfl)) :
    @fintype.card_le_of_injective (gpowers a) (↑(univ.filter (λ b : units α, b ^ order_of a = 1)) : set (units α))
      (id _) (id _) (λ b, ⟨b.1, mem_filter.2 ⟨mem_univ _,
        let ⟨i, hi⟩ := b.2 in
        by rw [← hi, ← gpow_coe_nat, ← gpow_mul, mul_comm, gpow_mul, gpow_coe_nat,
          pow_order_of_eq_one, one_gpow]⟩⟩) (λ _ _ h, subtype.eq (subtype.mk.inj h))
  ... = (univ.filter (λ b : units α, b ^ order_of a = 1)).card : set.card_fintype_of_finset _ _)

local notation `φ` := totient

private lemma card_order_of_eq_totient_aux :
  ∀ {d : ℕ}, d ∣ fintype.card (units α) → 0 < (univ.filter (λ a : units α, order_of a = d)).card →
  (univ.filter (λ a : units α, order_of a = d)).card = φ d
| 0     := λ hd hd0, absurd hd0 (mt card_pos.1
  (by simp [finset.ext, nat.pos_iff_ne_zero.1 (order_of_pos _)]))
| (d+1) := λ hd hd0,
let ⟨a, ha⟩ := exists_mem_of_ne_empty (card_pos.1 hd0) in
have ha : order_of a = d.succ, from (mem_filter.1 ha).2,
have h : ((range d.succ).filter (∣ d.succ)).sum
    (λ m, (univ.filter (λ a : units α, order_of a = m)).card) =
    ((range d.succ).filter (∣ d.succ)).sum φ, from
  finset.sum_congr rfl
    (λ m hm, have hmd : m < d.succ, from mem_range.1 (mem_filter.1 hm).1,
      have hm : m ∣ d.succ, from (mem_filter.1 hm).2,
      card_order_of_eq_totient_aux (dvd.trans hm hd) (finset.card_pos.2
        (ne_empty_of_mem (show a ^ (d.succ / m) ∈ _,
          from mem_filter.2 ⟨mem_univ _,
          by rw [order_of_pow, ha, gcd_eq_right (div_dvd_of_dvd hm),
            nat.div_div_self hm (succ_pos _)]⟩)))),
have hinsert : insert d.succ ((range d.succ).filter (∣ d.succ))
    = (range d.succ.succ).filter (∣ d.succ),
  from (finset.ext.2 $ λ x, ⟨λ h, (mem_insert.1 h).elim (λ h, by simp [h])
    (by clear _let_match; simp; tauto), by clear _let_match; simp {contextual := tt}; tauto⟩),
have hinsert₁ : d.succ ∉ (range d.succ).filter (∣ d.succ),
  by simp [-range_succ, mem_range, zero_le_one, le_succ],
(add_right_inj (((range d.succ).filter (∣ d.succ)).sum
  (λ m, (univ.filter (λ a : units α, order_of a = m)).card))).1
  (calc _ = (insert d.succ (filter (∣ d.succ) (range d.succ))).sum
        (λ m, (univ.filter (λ (a : units α), order_of a = m)).card) :
    eq.symm (finset.sum_insert (by simp [-range_succ, mem_range, zero_le_one, le_succ]))
  ... = ((range d.succ.succ).filter (∣ d.succ)).sum (λ m,
      (univ.filter (λ a : units α, order_of a = m)).card) :
    sum_congr hinsert (λ _ _, rfl)
  ... = (univ.filter (λ a : units α, a ^ d.succ = 1)).card :
    sum_card_order_of_eq_card_pow_eq_one (succ_pos d)
  ... = ((range d.succ.succ).filter (∣ d.succ)).sum φ :
    ha ▸ (card_pow_eq_one_eq_order_of a).symm ▸ (sum_totient _).symm
  ... = _ : by rw [h, ← sum_insert hinsert₁];
      exact finset.sum_congr hinsert.symm (λ _ _, rfl))

lemma card_order_of_eq_totient {d : ℕ} (hd : d ∣ fintype.card (units α)) :
  (univ.filter (λ a : units α, order_of a = d)).card = φ d :=
by_contradiction $ λ h,
have h0 : (univ.filter (λ a : units α, order_of a = d)).card = 0 :=
  not_not.1 (mt nat.pos_iff_ne_zero.2 (mt (card_order_of_eq_totient_aux hd) h)),
let c := fintype.card (units α) in
have hc0 : 0 < c, from fintype.card_pos_iff.2 ⟨1⟩,
lt_irrefl c $
  calc c = (univ.filter (λ a : units α, a ^ c = 1)).card :
    congr_arg card $ by simp [finset.ext]
  ... = ((range c.succ).filter (∣ c)).sum
      (λ m, (univ.filter (λ a : units α, order_of a = m)).card) :
    (sum_card_order_of_eq_card_pow_eq_one hc0).symm
  ... = (((range c.succ).filter (∣ c)).erase d).sum
      (λ m, (univ.filter (λ a : units α, order_of a = m)).card) :
    eq.symm (sum_subset (erase_subset _ _) (λ m hm₁ hm₂,
      have m = d, by simp at *; cc,
      by simp [*, finset.ext] at *))
  ... ≤ (((range c.succ).filter (∣ c)).erase d).sum φ :
    sum_le_sum (λ m hm,
      have hmc : m ∣ c, by simp at hm; tauto,
      (imp_iff_not_or.1 (card_order_of_eq_totient_aux hmc)).elim
        (λ h, by simp [nat.le_zero_iff.1 (le_of_not_gt h), nat.zero_le])
        (by simp [le_refl] {contextual := tt}))
  ... < φ d + (((range c.succ).filter (∣ c)).erase d).sum φ :
    lt_add_of_pos_left _ (totient_pos (nat.pos_of_ne_zero
      (λ h, nat.pos_iff_ne_zero.1 hc0 (eq_zero_of_zero_dvd $ h ▸ hd))))
  ... = (insert d (((range c.succ).filter (∣ c)).erase d)).sum φ : eq.symm (sum_insert (by simp))
  ... = ((range c.succ).filter (∣ c)).sum φ : finset.sum_congr
      (finset.insert_erase (mem_filter.2 ⟨mem_range.2 (lt_succ_of_le (le_of_dvd hc0 hd)), hd⟩)) (λ _ _, rfl)
  ... = c : sum_totient _

instance {α : Type*} [fintype α] [field α] : is_cyclic (units α) :=
by haveI := classical.dec_eq α; exact
have ∃ x, x ∈ univ.filter (λ a : units α, order_of a = fintype.card (units α)),
from exists_mem_of_ne_empty (card_pos.1 $
  by rw [card_order_of_eq_totient (dvd_refl _)];
  exact totient_pos (fintype.card_pos_iff.2 ⟨1⟩)),
let ⟨x, hx⟩ := this in
is_cyclic_of_order_of_eq_card x (finset.mem_filter.1 hx).2

lemma prod_univ_units_id_eq_neg_one : univ.prod (λ x, x) = (-1 : units α) :=
have ((@univ (units α) _).erase (-1)).prod (λ x, x) = 1,
from prod_involution (λ x _, x⁻¹) (by simp)
  (λ a, by simp [units.inv_eq_self_iff] {contextual := tt})
  (λ a, by simp [@inv_eq_iff_inv_eq _ _ a, eq_comm] {contextual := tt})
  (by simp),
by rw [← insert_erase (mem_univ (-1 : units α)), prod_insert (not_mem_erase _ _),
    this, mul_one]

end finite_field