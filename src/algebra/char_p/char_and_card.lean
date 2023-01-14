/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import algebra.char_p.basic
import group_theory.perm.cycle.type

/-!
# Characteristic and cardinality

We prove some results relating characteristic and cardinality of finite rings

## Tags
characterstic, cardinality, ring
-/

/-- A prime `p` is a unit in a commutative ring `R` of nonzero characterstic iff it does not divide
the characteristic. -/
lemma is_unit_iff_not_dvd_char_of_ring_char_ne_zero (R : Type*) [comm_ring R] (p : ℕ) [fact p.prime]
  (hR : ring_char R ≠ 0) :
  is_unit (p : R) ↔ ¬ p ∣ ring_char R :=
begin
  have hch := char_p.cast_eq_zero R (ring_char R),
  have hp : p.prime := fact.out p.prime,
  split,
  { rintros h₁ ⟨q, hq⟩,
    rcases is_unit.exists_left_inv h₁ with ⟨a, ha⟩,
    have h₃ : ¬ ring_char R ∣ q :=
    begin
      rintro ⟨r, hr⟩,
      rw [hr, ← mul_assoc, mul_comm p, mul_assoc] at hq,
      nth_rewrite 0 ← mul_one (ring_char R) at hq,
      exact nat.prime.not_dvd_one hp ⟨r, mul_left_cancel₀ hR hq⟩,
    end,
    have h₄ := mt (char_p.int_cast_eq_zero_iff R (ring_char R) q).mp,
    apply_fun (coe : ℕ → R) at hq,
    apply_fun ((*) a) at hq,
    rw [nat.cast_mul, hch, mul_zero, ← mul_assoc, ha, one_mul] at hq,
    norm_cast at h₄,
    exact h₄ h₃ hq.symm, },
  { intro h,
    rcases (hp.coprime_iff_not_dvd.mpr h).is_coprime with ⟨a, b, hab⟩,
    apply_fun (coe : ℤ → R) at hab,
    push_cast at hab,
    rw [hch, mul_zero, add_zero, mul_comm] at hab,
    exact is_unit_of_mul_eq_one (p : R) a hab, },
end

/-- A prime `p` is a unit in a finite commutative ring `R`
iff it does not divide the characteristic. -/
lemma is_unit_iff_not_dvd_char (R : Type*) [comm_ring R] (p : ℕ) [fact p.prime] [finite R] :
  is_unit (p : R) ↔ ¬ p ∣ ring_char R :=
is_unit_iff_not_dvd_char_of_ring_char_ne_zero R p $ char_p.char_ne_zero_of_finite R (ring_char R)

/-- The prime divisors of the characteristic of a finite commutative ring are exactly
the prime divisors of its cardinality. -/
lemma prime_dvd_char_iff_dvd_card {R : Type*} [comm_ring R] [fintype R] (p : ℕ) [fact p.prime] :
  p ∣ ring_char R ↔ p ∣ fintype.card R :=
begin
  refine ⟨λ h, h.trans $ int.coe_nat_dvd.mp $ (char_p.int_cast_eq_zero_iff R (ring_char R)
    (fintype.card R)).mp $ by exact_mod_cast char_p.cast_card_eq_zero R, λ h, _⟩,
  by_contra h₀,
  rcases exists_prime_add_order_of_dvd_card p h with ⟨r, hr⟩,
  have hr₁ := add_order_of_nsmul_eq_zero r,
  rw [hr, nsmul_eq_mul] at hr₁,
  rcases is_unit.exists_left_inv ((is_unit_iff_not_dvd_char R p).mpr h₀) with ⟨u, hu⟩,
  apply_fun ((*) u) at hr₁,
  rw [mul_zero, ← mul_assoc, hu, one_mul] at hr₁,
  exact mt add_monoid.order_of_eq_one_iff.mpr
          (ne_of_eq_of_ne hr (nat.prime.ne_one (fact.out p.prime))) hr₁,
end

/-- A prime that does not divide the cardinality of a finite commutative ring `R`
is a unit in `R`. -/
lemma not_is_unit_prime_of_dvd_card {R : Type*} [comm_ring R] [fintype R] (p : ℕ) [fact p.prime]
 (hp : p ∣ fintype.card R) : ¬ is_unit (p : R) :=
mt (is_unit_iff_not_dvd_char R p).mp (not_not.mpr ((prime_dvd_char_iff_dvd_card p).mpr hp))
