/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import algebra.order.euclidean_absolute_value
import data.polynomial.field_division

/-!
# Absolute value on polynomials over a finite field.

Let `Fq` be a finite field of cardinality `q`, then the map sending a polynomial `p`
to `q ^ degree p` (where `q ^ degree 0 = 0`) is an absolute value.

## Main definitions

 * `polynomial.card_pow_degree` is an absolute value on `𝔽_q[t]`, the ring of
   polynomials over a finite field of cardinality `q`, mapping a polynomial `p`
   to `q ^ degree p` (where `q ^ degree 0 = 0`)

## Main results
 * `polynomial.card_pow_degree_is_euclidean`: `card_pow_degree` respects the
   Euclidean domain structure on the ring of polynomials

-/

namespace polynomial

variables {Fq : Type*} [field Fq] [fintype Fq]

open absolute_value

open_locale classical

/-- `card_pow_degree` is the absolute value on `𝔽_q[t]` sending `f` to `q ^ degree f`.

`card_pow_degree 0` is defined to be `0`. -/
noncomputable def card_pow_degree :
  absolute_value (polynomial Fq) ℤ :=
have card_pos : 0 < fintype.card Fq := fintype.card_pos_iff.mpr infer_instance,
have pow_pos : ∀ n, 0 < (fintype.card Fq : ℤ) ^ n := λ n, pow_pos (int.coe_nat_pos.mpr card_pos) n,
{ to_fun := λ p, if p = 0 then 0 else fintype.card Fq ^ p.nat_degree,
  nonneg' := λ p, by { split_ifs, { refl }, exact pow_nonneg (int.coe_zero_le _) _ },
  eq_zero' := λ p, ite_eq_left_iff.trans $ ⟨λ h, by { contrapose! h, exact ⟨h, (pow_pos _).ne'⟩ },
    absurd⟩,
  add_le' := λ p q, begin
    by_cases hp : p = 0, { simp [hp] },
    by_cases hq : q = 0, { simp [hq] },
    by_cases hpq : p + q = 0,
    { simp only [hpq, hp, hq, eq_self_iff_true, if_true, if_false],
      exact add_nonneg (pow_pos _).le (pow_pos _).le },
    simp only [hpq, hp, hq, if_false],
    refine le_trans (pow_le_pow (by linarith) (polynomial.nat_degree_add_le _ _)) _,
    refine le_trans (le_max_iff.mpr _)
      (max_le_add_of_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)),
    exact (max_choice p.nat_degree q.nat_degree).imp (λ h, by rw [h]) (λ h, by rw [h])
  end,
  map_mul' := λ p q, begin
    by_cases hp : p = 0, { simp [hp] },
    by_cases hq : q = 0, { simp [hq] },
    have hpq : p * q ≠ 0 := mul_ne_zero hp hq,
    simp only [hpq, hp, hq, eq_self_iff_true, if_true, if_false,
      polynomial.nat_degree_mul hp hq, pow_add],
  end }

lemma card_pow_degree_apply (p : polynomial Fq) :
  card_pow_degree p = if p = 0 then 0 else fintype.card Fq ^ nat_degree p := rfl

@[simp] lemma card_pow_degree_zero : card_pow_degree (0 : polynomial Fq) = 0 := if_pos rfl

@[simp] lemma card_pow_degree_nonzero (p : polynomial Fq) (hp : p ≠ 0) :
  card_pow_degree p = fintype.card Fq ^ p.nat_degree :=
if_neg hp

lemma card_pow_degree_is_euclidean :
  is_euclidean (card_pow_degree : absolute_value (polynomial Fq) ℤ) :=
have card_pos : 0 < fintype.card Fq := fintype.card_pos_iff.mpr infer_instance,
have pow_pos : ∀ n, 0 < (fintype.card Fq : ℤ) ^ n := λ n, pow_pos (int.coe_nat_pos.mpr card_pos) n,
{ map_lt_map_iff' := λ p q, begin
    simp only [euclidean_domain.r, card_pow_degree_apply],
    split_ifs with hp hq hq,
    { simp only [hp, hq, lt_self_iff_false] },
    { simp only [hp, hq, degree_zero, ne.def, bot_lt_iff_ne_bot,
        degree_eq_bot, pow_pos, not_false_iff] },
    { simp only [hp, hq, degree_zero, not_lt_bot, (pow_pos _).not_lt] },
    { rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq, with_bot.coe_lt_coe, pow_lt_pow_iff],
      exact_mod_cast @fintype.one_lt_card Fq _ _ },
  end }

end polynomial
