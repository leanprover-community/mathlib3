/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import algebra.big_operators.basic
import data.nat.prime
import data.zmod.basic
import ring_theory.multiplicity
import data.nat.periodic
import algebra.char_p.two
import number_theory.divisors

/-!
# Euler's totient function

This file defines [Euler's totient function](https://en.wikipedia.org/wiki/Euler's_totient_function)
`nat.totient n` which counts the number of naturals less than `n` that are coprime with `n`.
We prove the divisor sum formula, namely that `n` equals `φ` summed over the divisors of `n`. See
`sum_totient`. We also prove two lemmas to help compute totients, namely `totient_mul` and
`totient_prime_pow`.
-/

open finset
open_locale big_operators

namespace nat

/-- Euler's totient function. This counts the number of naturals strictly less than `n` which are
coprime with `n`. -/
def totient (n : ℕ) : ℕ := ((range n).filter n.coprime).card

localized "notation `φ` := nat.totient" in nat

@[simp] theorem totient_zero : φ 0 = 0 := rfl

@[simp] theorem totient_one : φ 1 = 1 :=
by simp [totient]

lemma totient_eq_card_coprime (n : ℕ) : φ n = ((range n).filter n.coprime).card := rfl

lemma totient_le (n : ℕ) : φ n ≤ n :=
((range n).card_filter_le _).trans_eq (card_range n)

lemma totient_lt (n : ℕ) (hn : 1 < n) : φ n < n :=
(card_lt_card (filter_ssubset.2 ⟨0, by simp [hn.ne', pos_of_gt hn]⟩)).trans_eq (card_range n)

lemma totient_pos : ∀ {n : ℕ}, 0 < n → 0 < φ n
| 0 := dec_trivial
| 1 := by simp [totient]
| (n+2) := λ h, card_pos.2 ⟨1, mem_filter.2 ⟨mem_range.2 dec_trivial, coprime_one_right _⟩⟩

lemma filter_coprime_Ico_eq_totient (a n : ℕ) :
  ((Ico n (n+a)).filter (coprime a)).card = totient a :=
begin
  rw [totient, filter_Ico_card_eq_of_periodic, count_eq_card_filter_range],
  exact periodic_coprime a,
end

lemma Ico_filter_coprime_le {a : ℕ} (k n : ℕ) (a_pos : 0 < a) :
  ((Ico k (k + n)).filter (coprime a)).card ≤ totient a * (n / a + 1) :=
begin
  conv_lhs { rw ←nat.mod_add_div n a },
  induction n / a with i ih,
  { rw ←filter_coprime_Ico_eq_totient a k,
    simp only [add_zero, mul_one, mul_zero, le_of_lt (mod_lt n a_pos)],
    mono,
    refine monotone_filter_left a.coprime _,
    simp only [finset.le_eq_subset],
    exact Ico_subset_Ico rfl.le (add_le_add_left (le_of_lt (mod_lt n a_pos)) k), },
  simp only [mul_succ],
  simp_rw ←add_assoc at ih ⊢,
  calc (filter a.coprime (Ico k (k + n % a + a * i + a))).card
      = (filter a.coprime (Ico k (k + n % a + a * i)
                            ∪ Ico (k + n % a + a * i) (k + n % a + a * i + a))).card :
        begin
          congr,
          rw Ico_union_Ico_eq_Ico,
          rw add_assoc,
          exact le_self_add,
          exact le_self_add,
        end
  ... ≤ (filter a.coprime (Ico k (k + n % a + a * i))).card + a.totient :
        begin
          rw [filter_union, ←filter_coprime_Ico_eq_totient a (k + n % a + a * i)],
          apply card_union_le,
        end
  ... ≤ a.totient * i + a.totient + a.totient : add_le_add_right ih (totient a),
end

open zmod

/-- Note this takes an explicit `fintype ((zmod n)ˣ)` argument to avoid trouble with instance
diamonds. -/
@[simp] lemma _root_.zmod.card_units_eq_totient (n : ℕ) [fact (0 < n)] [fintype ((zmod n)ˣ)] :
  fintype.card ((zmod n)ˣ) = φ n :=
calc fintype.card ((zmod n)ˣ) = fintype.card {x : zmod n // x.val.coprime n} :
  fintype.card_congr zmod.units_equiv_coprime
... = φ n :
begin
  apply finset.card_congr (λ (a : {x : zmod n // x.val.coprime n}) _, a.1.val),
  { intro a, simp [(a : zmod n).val_lt, a.prop.symm] {contextual := tt} },
  { intros _ _ _ _ h, rw subtype.ext_iff_val, apply val_injective, exact h, },
  { intros b hb,
    rw [finset.mem_filter, finset.mem_range] at hb,
    refine ⟨⟨b, _⟩, finset.mem_univ _, _⟩,
    { let u := unit_of_coprime b hb.2.symm,
      exact val_coe_unit_coprime u },
    { show zmod.val (b : zmod n) = b,
      rw [val_nat_cast, nat.mod_eq_of_lt hb.1], } }
end

lemma totient_even {n : ℕ} (hn : 2 < n) : even n.totient :=
begin
  haveI : fact (1 < n) := ⟨one_lt_two.trans hn⟩,
  suffices : 2 = order_of (-1 : (zmod n)ˣ),
  { rw [← zmod.card_units_eq_totient, even_iff_two_dvd, this], exact order_of_dvd_card_univ },
  rw [←order_of_units, units.coe_neg_one, order_of_neg_one, ring_char.eq (zmod n) n, if_neg hn.ne'],
end

lemma totient_mul {m n : ℕ} (h : m.coprime n) : φ (m * n) = φ m * φ n :=
if hmn0 : m * n = 0
  then by cases nat.mul_eq_zero.1 hmn0 with h h;
    simp only [totient_zero, mul_zero, zero_mul, h]
  else
  begin
    haveI : fact (0 < (m * n)) := ⟨nat.pos_of_ne_zero hmn0⟩,
    haveI : fact (0 < m) := ⟨nat.pos_of_ne_zero $ left_ne_zero_of_mul hmn0⟩,
    haveI : fact (0 < n) := ⟨nat.pos_of_ne_zero $ right_ne_zero_of_mul hmn0⟩,
    simp only [← zmod.card_units_eq_totient],
    rw [fintype.card_congr (units.map_equiv (zmod.chinese_remainder h).to_mul_equiv).to_equiv,
      fintype.card_congr (@mul_equiv.prod_units (zmod m) (zmod n) _ _).to_equiv,
      fintype.card_prod]
  end

/-- For `d ∣ n`, the totient of `n/d` equals the number of values `k < n` such that `gcd n k = d` -/
lemma totient_div_of_dvd {n d : ℕ} (hnd : d ∣ n) :
  φ (n/d) = (filter (λ (k : ℕ), n.gcd k = d) (range n)).card :=
begin
  rcases d.eq_zero_or_pos with rfl | hd0, { simp [zero_dvd_iff.1 hnd] },
  rcases hnd with ⟨x, rfl⟩,
  rw nat.mul_div_cancel_left x hd0,
  apply card_congr (λ k _, d * k),
  { simp only [mem_filter, mem_range, and_imp, coprime],
    refine λ a ha1 ha2, ⟨(mul_lt_mul_left hd0).2 ha1, _⟩,
    rw [gcd_mul_left, ha2, mul_one] },
  { simp [hd0.ne'] },
  { simp only [mem_filter, mem_range, exists_prop, and_imp],
    refine λ b hb1 hb2, _,
    have : d ∣ b, { rw ←hb2, apply gcd_dvd_right },
    rcases this with ⟨q, rfl⟩,
    refine ⟨q, ⟨⟨(mul_lt_mul_left hd0).1 hb1, _⟩, rfl⟩⟩,
    rwa [gcd_mul_left, mul_right_eq_self_iff hd0] at hb2 },
end

lemma sum_totient (n : ℕ) : n.divisors.sum φ = n :=
begin
  rcases n.eq_zero_or_pos with rfl | hn, { simp },
  rw ←sum_div_divisors n φ,
  have : n = ∑ (d : ℕ) in n.divisors, (filter (λ (k : ℕ), n.gcd k = d) (range n)).card,
  { nth_rewrite_lhs 0 ←card_range n,
    refine card_eq_sum_card_fiberwise (λ x hx, mem_divisors.2 ⟨_, hn.ne'⟩),
    apply gcd_dvd_left },
  nth_rewrite_rhs 0 this,
  exact sum_congr rfl (λ x hx, totient_div_of_dvd (dvd_of_mem_divisors hx)),
end

lemma sum_totient' (n : ℕ) : ∑ m in (range n.succ).filter (∣ n), φ m = n :=
begin
  convert sum_totient _ using 1,
  simp only [nat.divisors, sum_filter, range_eq_Ico],
  rw sum_eq_sum_Ico_succ_bot; simp
end

/-- When `p` is prime, then the totient of `p ^ (n + 1)` is `p ^ n * (p - 1)` -/
lemma totient_prime_pow_succ {p : ℕ} (hp : p.prime) (n : ℕ) :
  φ (p ^ (n + 1)) = p ^ n * (p - 1) :=
calc φ (p ^ (n + 1))
    = ((range (p ^ (n + 1))).filter (coprime (p ^ (n + 1)))).card :
  totient_eq_card_coprime _
... = (range (p ^ (n + 1)) \ ((range (p ^ n)).image (* p))).card :
  congr_arg card begin
    rw [sdiff_eq_filter],
    apply filter_congr,
    simp only [mem_range, mem_filter, coprime_pow_left_iff n.succ_pos,
      mem_image, not_exists, hp.coprime_iff_not_dvd],
    intros a ha,
    split,
    { rintros hap b _ rfl,
      exact hap (dvd_mul_left _ _) },
    { rintros h ⟨b, rfl⟩,
      rw [pow_succ] at ha,
      exact h b (lt_of_mul_lt_mul_left ha (zero_le _)) (mul_comm _ _) }
  end
... = _ :
have h1 : set.inj_on (* p) (range (p ^ n)),
  from λ x _ y _, (nat.mul_left_inj hp.pos).1,
have h2 : (range (p ^ n)).image (* p) ⊆ range (p ^ (n + 1)),
  from λ a, begin
    simp only [mem_image, mem_range, exists_imp_distrib],
    rintros b h rfl,
    rw [pow_succ'],
    exact (mul_lt_mul_right hp.pos).2 h
  end,
begin
  rw [card_sdiff h2, card_image_of_inj_on h1, card_range,
    card_range, ← one_mul (p ^ n), pow_succ, ← tsub_mul,
    one_mul, mul_comm]
end

/-- When `p` is prime, then the totient of `p ^ n` is `p ^ (n - 1) * (p - 1)` -/
lemma totient_prime_pow {p : ℕ} (hp : p.prime) {n : ℕ} (hn : 0 < n) :
  φ (p ^ n) = p ^ (n - 1) * (p - 1) :=
by rcases exists_eq_succ_of_ne_zero (pos_iff_ne_zero.1 hn) with ⟨m, rfl⟩;
  exact totient_prime_pow_succ hp _

lemma totient_prime {p : ℕ} (hp : p.prime) : φ p = p - 1 :=
by rw [← pow_one p, totient_prime_pow hp]; simp

lemma totient_mul_of_prime_of_dvd {p n : ℕ} (hp : p.prime) (h : p ∣ n) :
  (p * n).totient = p * n.totient :=
begin
  by_cases hzero : n = 0,
  { simp [hzero] },
  { have hfin := (multiplicity.finite_nat_iff.2 ⟨hp.ne_one, zero_lt_iff.2 hzero⟩),
    have h0 : 0 < (multiplicity p n).get hfin := multiplicity.pos_of_dvd hfin h,
    obtain ⟨m, hm, hndiv⟩ := multiplicity.exists_eq_pow_mul_and_not_dvd hfin,
    rw [hm, ← mul_assoc, ← pow_succ, nat.totient_mul (coprime_comm.mp (hp.coprime_pow_of_not_dvd
      hndiv)), nat.totient_mul (coprime_comm.mp (hp.coprime_pow_of_not_dvd hndiv)), ← mul_assoc],
    congr,
    rw [ ← succ_pred_eq_of_pos h0, totient_prime_pow_succ hp, totient_prime_pow_succ hp,
      succ_pred_eq_of_pos h0, ← mul_assoc p, ← pow_succ, ← succ_pred_eq_of_pos h0, nat.pred_succ] }
end

lemma totient_eq_iff_prime {p : ℕ} (hp : 0 < p) : p.totient = p - 1 ↔ p.prime :=
begin
  refine ⟨λ h, _, totient_prime⟩,
  replace hp : 1 < p,
  { apply lt_of_le_of_ne,
    { rwa succ_le_iff },
    { rintro rfl,
      rw [totient_one, tsub_self] at h,
      exact one_ne_zero h } },
  rw [totient_eq_card_coprime, range_eq_Ico, ←Ico_insert_succ_left hp.le, finset.filter_insert,
      if_neg (not_coprime_of_dvd_of_dvd hp (dvd_refl p) (dvd_zero p)), ←nat.card_Ico 1 p] at h,
  refine p.prime_of_coprime hp (λ n hn hnz, finset.filter_card_eq h n $ finset.mem_Ico.mpr ⟨_, hn⟩),
  rwa [succ_le_iff, pos_iff_ne_zero],
end

lemma card_units_zmod_lt_sub_one {p : ℕ} (hp : 1 < p) [fintype ((zmod p)ˣ)] :
  fintype.card ((zmod p)ˣ) ≤ p - 1 :=
begin
  haveI : fact (0 < p) := ⟨zero_lt_one.trans hp⟩,
  rw zmod.card_units_eq_totient p,
  exact nat.le_pred_of_lt (nat.totient_lt p hp),
end

lemma prime_iff_card_units (p : ℕ) [fintype ((zmod p)ˣ)] :
  p.prime ↔ fintype.card ((zmod p)ˣ) = p - 1 :=
begin
  by_cases hp : p = 0,
  { substI hp,
    simp only [zmod, not_prime_zero, false_iff, zero_tsub],
    -- the substI created an non-defeq but subsingleton instance diamond; resolve it
    suffices : fintype.card ℤˣ ≠ 0, { convert this },
    simp },
  haveI : fact (0 < p) := ⟨nat.pos_of_ne_zero hp⟩,
  rw [zmod.card_units_eq_totient, nat.totient_eq_iff_prime (fact.out (0 < p))],
end

@[simp] lemma totient_two : φ 2 = 1 :=
(totient_prime prime_two).trans rfl

lemma totient_eq_one_iff : ∀ {n : ℕ}, n.totient = 1 ↔ n = 1 ∨ n = 2
| 0 := by simp
| 1 := by simp
| 2 := by simp
| (n+3) :=
begin
  have : 3 ≤ n + 3 := le_add_self,
  simp only [succ_succ_ne_one, false_or],
  exact ⟨λ h, not_even_one.elim $ h ▸ totient_even this, by rintro ⟨⟩⟩,
end

/-! ### Euler's product formula for the totient function

We prove several different statements of this formula. -/

/-- Euler's product formula for the totient function. -/
theorem totient_eq_prod_factorization {n : ℕ} (hn : n ≠ 0) :
  φ n = n.factorization.prod (λ p k, p ^ (k - 1) * (p - 1)) :=
begin
  rw multiplicative_factorization φ @totient_mul totient_one hn,
  apply finsupp.prod_congr (λ p hp, _),
  have h := zero_lt_iff.mpr (finsupp.mem_support_iff.mp hp),
  rw [totient_prime_pow (prime_of_mem_factorization hp) h],
end

/-- Euler's product formula for the totient function. -/
theorem totient_mul_prod_factors (n : ℕ) :
  φ n * ∏ p in n.factors.to_finset, p = n * ∏ p in n.factors.to_finset, (p - 1) :=
begin
  by_cases hn : n = 0, { simp [hn] },
  rw totient_eq_prod_factorization hn,
  nth_rewrite 2 ←factorization_prod_pow_eq_self hn,
  simp only [←prod_factorization_eq_prod_factors, ←finsupp.prod_mul],
  refine finsupp.prod_congr (λ p hp, _),
  rw [finsupp.mem_support_iff, ← zero_lt_iff] at hp,
  rw [mul_comm, ←mul_assoc, ←pow_succ, nat.sub_add_cancel hp],
end

/-- Euler's product formula for the totient function. -/
theorem totient_eq_div_factors_mul (n : ℕ) :
  φ n = n / (∏ p in n.factors.to_finset, p) * (∏ p in n.factors.to_finset, (p - 1)) :=
begin
  rw [← mul_div_left n.totient, totient_mul_prod_factors, mul_comm,
      nat.mul_div_assoc _ (prod_prime_factors_dvd n), mul_comm],
  simpa [prod_factorization_eq_prod_factors] using prod_pos (λ p, pos_of_mem_factorization),
end

/-- Euler's product formula for the totient function. -/
theorem totient_eq_mul_prod_factors (n : ℕ) :
  (φ n : ℚ) = n * ∏ p in n.factors.to_finset, (1 - p⁻¹) :=
begin
  by_cases hn : n = 0, { simp [hn] },
  have hn' : (n : ℚ) ≠ 0, { simp [hn] },
  have hpQ : ∏ p in n.factors.to_finset, (p : ℚ) ≠ 0,
  { rw [←cast_prod, cast_ne_zero, ←zero_lt_iff, ←prod_factorization_eq_prod_factors],
    exact prod_pos (λ p hp, pos_of_mem_factorization hp) },
  simp only [totient_eq_div_factors_mul n, prod_prime_factors_dvd n, cast_mul, cast_prod,
      cast_div_char_zero, mul_comm_div, mul_right_inj' hn', div_eq_iff hpQ, ←prod_mul_distrib],
  refine prod_congr rfl (λ p hp, _),
  have hp := pos_of_mem_factors (list.mem_to_finset.mp hp),
  have hp' : (p : ℚ) ≠ 0 := cast_ne_zero.mpr hp.ne.symm,
  rw [sub_mul, one_mul, mul_comm, mul_inv_cancel hp', cast_pred hp],
end

end nat
