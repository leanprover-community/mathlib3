/-
Copyright (c) 2019 Casper Putz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Joey van Langen, Casper Putz
-/

import data.equiv.algebra
import data.polynomial
import data.zmod.basic
import algebra.char_p
import algebra.geom_sum
import linear_algebra.basis
import group_theory.order_of_element

/-!
# Finite fields

This file contains basic results about finite fields.
Throughout most of this file, K denotes a finite field with q elements.

## Main results

1. Every finite integral domain is a field (`field_of_integral_domain`).
2. The unit group of a finite field is a cyclic group of order q - 1.
   (`finite_field.is_cyclic` and `card_units`)
3. `sum_pow_units`: The sum of x^i, where x ranges over the units of K, is
   | q-1 if q-1 ∣ i
   | 0   otherwise
4. `finite_field.card`: The cardinality q is a power of the characteristic of K.
   See `card'` for a variant.
-/

variables {K : Type*} [discrete_field K] [fintype K]
variables {R : Type*} [integral_domain R] [decidable_eq R]
local notation `q` := fintype.card K

section

open function finset polynomial nat

variables (S : set (units R)) [is_subgroup S] [fintype S]

lemma card_nth_roots_subgroup_units {n : ℕ} (hn : 0 < n) (a : S) :
  (univ.filter (λ b : S, b ^ n = a)).card ≤ (nth_roots n ((a : units R) : R)).card :=
card_le_card_of_inj_on (λ a, ((a : units R) : R))
  (by simp [mem_nth_roots hn, (units.coe_pow _ _).symm, -units.coe_pow, units.ext_iff.symm, subtype.coe_ext])
  (by simp [units.ext_iff.symm, subtype.coe_ext.symm])

open_locale classical

/-- A finite subgroup of the units of an integral domain is cyclic. -/
instance subgroup_units_cyclic : is_cyclic S :=
is_cyclic_of_card_pow_eq_one_le
  (λ n hn, le_trans (card_nth_roots_subgroup_units S hn 1) (card_nth_roots _ _))

end

namespace finite_field
open function finset polynomial

/-- Every finite integral domain is a field. -/
def field_of_integral_domain [fintype R] : discrete_field R :=
{ has_decidable_eq := by apply_instance,
  inv := λ a, if h : a = 0 then 0
    else fintype.bij_inv (show function.bijective (* a),
      from fintype.injective_iff_bijective.1 $ λ _ _, (domain.mul_right_inj h).1) 1,
  inv_mul_cancel := λ a ha, show dite _ _ _ * a = _, by rw dif_neg ha;
    exact fintype.right_inverse_bij_inv (show function.bijective (* a), from _) 1,
  mul_inv_cancel :=  λ a ha, show a * dite _ _ _ = _, by rw [dif_neg ha, mul_comm];
    exact fintype.right_inverse_bij_inv (show function.bijective (* a), from _) 1,
  inv_zero := dif_pos rfl,
  ..show integral_domain R, by apply_instance }

/-- The units of a finite field are finite. -/
instance : fintype (units K) :=
by haveI := set_fintype {a : K | a ≠ 0}; exact
fintype.of_equiv _ (equiv.units_equiv_ne_zero K).symm

/-- A finite field of cardinality q has a unit group of cardinality q - 1. -/
lemma card_units : fintype.card (units K) = q - 1 :=
begin
  rw [eq_comm, nat.sub_eq_iff_eq_add (fintype.card_pos_iff.2 ⟨(0 : K)⟩)],
  haveI := set_fintype {a : K | a ≠ 0},
  haveI := set_fintype (@set.univ K),
  rw [fintype.card_congr (equiv.units_equiv_ne_zero _),
    ← @set.card_insert _ _ {a : K | a ≠ 0} _ (not_not.2 (eq.refl (0 : K)))
    (set.fintype_insert _ _), fintype.card_congr (equiv.set.univ K).symm],
  congr, ext, simp [classical.em]
end

/-- The units of a finite field form a cyclic group. -/
instance : is_cyclic (units K) :=
by haveI := set_fintype (@set.univ (units K)); exact
let ⟨g, hg⟩ := is_cyclic.exists_generator (@set.univ (units K)) in
⟨⟨g, λ x, let ⟨n, hn⟩ := hg ⟨x, trivial⟩ in ⟨n, by rw [← is_subgroup.coe_gpow, hn]; refl⟩⟩⟩

lemma prod_univ_units_id_eq_neg_one : univ.prod (λ x, x) = (-1 : units K) :=
have ((@univ (units K) _).erase (-1)).prod (λ x, x) = 1,
from prod_involution (λ x _, x⁻¹) (by simp)
  (λ a, by simp [units.inv_eq_self_iff] {contextual := tt})
  (λ a, by simp [@inv_eq_iff_inv_eq _ _ a, eq_comm] {contextual := tt})
  (by simp),
by rw [← insert_erase (mem_univ (-1 : units K)), prod_insert (not_mem_erase _ _),
    this, mul_one]

/-- In a finite field of cardinality q, one has a^(q-1) = 1 for all nonzero a. -/
lemma pow_card_sub_one_eq_one (a : K) (ha : a ≠ 0) : a ^ (q - 1) = 1 :=
calc a ^ (q - 1) = (units.mk0 a ha ^ (q - 1) : units K) : by rw [units.coe_pow, units.mk0_val]
             ... = 1 : by rw [← card_units, pow_card_eq_one]; refl

variable (K)

/-- The sum of x^i as x ranges over the units of a finite field of cardinality q
is equal to 0 unless (q-1) ∣ i, in which case the sum is q-1. -/
lemma sum_pow_units (i : ℕ) :
  univ.sum (λ (x : units K), (x^i : K)) = if (q - 1) ∣ i then q - 1 else 0 :=
begin
  have hq : 0 < q - 1,
  { rw [← card_units, fintype.card_pos_iff],
    exact ⟨1⟩ },
  cases is_cyclic.exists_generator (units K) with a ha,
  calc univ.sum (λ (x : units K), (x^i : K)) = (range (order_of a)).sum (λ k, ((a^k)^i : K)) :
  begin
    symmetry,
    refine sum_bij (λ i hi, a^i) (λ _ _, mem_univ _) (λ _ _, by rw units.coe_pow) _ _,
    { intros i j hi hj h, rw [mem_range] at hi hj,
      exact pow_injective_of_lt_order_of a hi hj h, },
    { intros x hx, specialize ha x,
      rwa [mem_gpowers_iff_mem_range_order_of, mem_image] at ha,
      rcases ha with ⟨i, hi, rfl⟩, exact ⟨i, hi, rfl⟩ }
  end
    ... = geom_series (a^i : K) (q-1) :
  begin
    rw [order_of_eq_card_of_forall_mem_gpowers ha, card_units],
    apply sum_congr rfl, intros k hk, rw [← pow_mul, mul_comm, pow_mul]
  end
    ... = if (q - 1) ∣ i then q - 1 else 0 :
  begin
    split_ifs with H H,
    { rcases H with ⟨d, rfl⟩,
      have aux : (λ (i:ℕ), ((a : K) ^ ((q - 1) * d)) ^ i) = λ i, 1,
      { funext i, rw [pow_mul, pow_card_sub_one_eq_one _ (units.ne_zero _), one_pow, one_pow], },
      rw [geom_series_def, aux, sum_const, card_range, add_monoid.smul_one,
        nat.cast_sub, nat.cast_one],
      exact le_trans hq (nat.pred_le _), },
    { have key := geom_sum_mul (a^i : K) (q-1),
      have hai : (a^i : K) ≠ 0, { rw ← units.coe_pow, apply units.ne_zero },
      rw [pow_card_sub_one_eq_one _ hai, sub_self] at key,
      replace key := eq_zero_or_eq_zero_of_mul_eq_zero key,
      rw classical.or_iff_not_imp_right at key, apply key, contrapose! H,
      rw [← card_units, ← order_of_eq_card_of_forall_mem_gpowers ha],
      apply order_of_dvd_of_pow_eq_one,
      rwa [units.ext_iff, units.coe_pow, units.coe_one, ← sub_eq_zero], }
  end
end

theorem card (p : ℕ) [char_p K p] : ∃ (n : ℕ+), nat.prime p ∧ q = p^(n : ℕ) :=
have hp : nat.prime p, from char_p.char_is_prime K p,
have V : vector_space (zmodp p hp) K, from {..zmod.to_module'},
let ⟨n, h⟩ := @vector_space.card_fintype _ _ _ _ V _ _ in
have hn : n > 0, from or.resolve_left (nat.eq_zero_or_pos n)
  (assume h0 : n = 0,
  have q = 1, by rw[←nat.pow_zero (fintype.card _), ←h0]; exact h,
  have (1 : K) = 0, from (fintype.card_le_one_iff.mp (le_of_eq this)) 1 0,
  absurd this one_ne_zero),
⟨⟨n, hn⟩, hp, fintype.card_fin p ▸ h⟩

theorem card' : ∃ (p : ℕ) (n : ℕ+), nat.prime p ∧ q = p^(n : ℕ) :=
let ⟨p, hc⟩ := char_p.exists K in ⟨p, @finite_field.card K _ _ p hc⟩

@[simp] lemma cast_card_eq_zero : (q : K) = 0 :=
begin
  rcases char_p.exists K with ⟨p, _char_p⟩, resetI,
  rcases card K p with ⟨n, hp, hn⟩,
  simp only [char_p.cast_eq_zero_iff K p, hn],
  conv { congr, rw [← nat.pow_one p] },
  exact nat.pow_dvd_pow _ n.2,
end

/-- The sum of x^i as x ranges over a finite field of cardinality q is equal to 0 if i < q-1. -/
lemma sum_pow_lt_card_sub_one (i : ℕ) (h : i < q - 1) :
  univ.sum (λ x, x^i) = (0:K) :=
begin
  have hq : 0 < q - 1,
  { rw [← card_units, fintype.card_pos_iff],
    exact ⟨1⟩ },
  by_cases hi : i = 0,
  { rcases char_p.exists K with ⟨p, _char_p⟩, resetI,
    rcases card K p with ⟨n, hp, hn⟩,
    simp only [hi, add_monoid.smul_one, sum_const, pow_zero, card_univ, cast_card_eq_zero], },
  rw [← sum_sdiff (subset_univ (finset.singleton (0:K))), sum_singleton,
    zero_pow (nat.pos_of_ne_zero hi), add_zero],
  have := sum_pow_units K i,
  have not_dvd_i : ¬q - 1 ∣ i,
  { rintro ⟨d, rfl⟩, apply hi, rw nat.mul_eq_zero, right, contrapose! h,
    conv { congr, rw ← mul_one (q-1), },
    rw mul_le_mul_left hq, exact nat.pos_of_ne_zero h },
  rw if_neg not_dvd_i at this,
  conv_rhs {rw ← this}, symmetry,
  refine sum_bij (λ x _, x) (λ _ _, by simp) (λ _ _, rfl) (λ _ _ _ _, units.ext_iff.mpr) _,
  { intros, refine ⟨units.mk0 b _, mem_univ _, rfl⟩,
    simpa only [true_and, mem_sdiff, mem_univ, mem_singleton] using H, },
end

end finite_field
