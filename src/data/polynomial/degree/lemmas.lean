/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.eval
import tactic.interval_cases

/-!
# Theory of degrees of polynomials

Some of the main results include
- `nat_degree_comp_le` : The degree of the composition is at most the product of degrees

-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

open finsupp finset

namespace polynomial
universes u v w
variables {R : Type u} {S : Type v} { ι : Type w} {a b : R} {m n : ℕ}

section semiring
variables [semiring R] {p q r : polynomial R}

section degree

lemma nat_degree_comp_le : nat_degree (p.comp q) ≤ nat_degree p * nat_degree q :=
if h0 : p.comp q = 0 then by rw [h0, nat_degree_zero]; exact nat.zero_le _
else with_bot.coe_le_coe.1 $
  calc ↑(nat_degree (p.comp q)) = degree (p.comp q) : (degree_eq_nat_degree h0).symm
  ... = _ : congr_arg degree comp_eq_sum_left
  ... ≤ _ : degree_sum_le _ _
  ... ≤ _ : sup_le (λ n hn,
    calc degree (C (coeff p n) * q ^ n)
        ≤ degree (C (coeff p n)) + degree (q ^ n) : degree_mul_le _ _
    ... ≤ nat_degree (C (coeff p n)) + n •ℕ (degree q) :
      add_le_add degree_le_nat_degree (degree_pow_le _ _)
    ... ≤ nat_degree (C (coeff p n)) + n •ℕ (nat_degree q) :
      add_le_add_left (nsmul_le_nsmul_of_le_right (@degree_le_nat_degree _ _ q) n) _
    ... = (n * nat_degree q : ℕ) :
     by rw [nat_degree_C, with_bot.coe_zero, zero_add, ← with_bot.coe_nsmul,
       nsmul_eq_mul]; simp
    ... ≤ (nat_degree p * nat_degree q : ℕ) : with_bot.coe_le_coe.2 $
      mul_le_mul_of_nonneg_right
        (le_nat_degree_of_ne_zero (finsupp.mem_support_iff.1 hn))
        (nat.zero_le _))

lemma degree_map_le [semiring S] (f : R →+* S) :
  degree (map f p) ≤ degree p :=
if h : map f p = 0 then by simp [h]
else begin
  rw [degree_eq_nat_degree h],
  refine le_degree_of_ne_zero (mt (congr_arg f) _),
  rw [← coeff_map f, is_semiring_hom.map_zero f],
  exact mt leading_coeff_eq_zero.1 h
end

lemma nat_degree_map_le [semiring S] (f : R →+* S) :
  (map f p).nat_degree ≤ p.nat_degree :=
begin
  by_cases hp : p = 0,
  { simp [hp] },
  { rw [← with_bot.coe_le_coe, ← degree_eq_nat_degree hp],
    by_cases hfp : map f p = 0,
    { simp [hfp, zero_le_degree_iff.mpr hp] },
    { simp [← degree_eq_nat_degree hfp, degree_map_le] } }
end

lemma degree_map_eq_of_leading_coeff_ne_zero [semiring S] (f : R →+* S)
  (hf : f (leading_coeff p) ≠ 0) : degree (p.map f) = degree p :=
le_antisymm (degree_map_le f) $
  have hp0 : p ≠ 0, from λ hp0, by simpa [hp0, is_semiring_hom.map_zero f] using hf,
  begin
    rw [degree_eq_nat_degree hp0],
    refine le_degree_of_ne_zero _,
    rw [coeff_map], exact hf
  end

lemma nat_degree_map_of_leading_coeff_ne_zero [semiring S] (f : R →+* S)
  (hf : f (leading_coeff p) ≠ 0) : nat_degree (p.map f) = nat_degree p :=
nat_degree_eq_of_degree_eq (degree_map_eq_of_leading_coeff_ne_zero f hf)

lemma leading_coeff_map_of_leading_coeff_ne_zero [semiring S] (f : R →+* S)
  (hf : f (leading_coeff p) ≠ 0) : leading_coeff (p.map f) = f (leading_coeff p) :=
begin
  unfold leading_coeff,
  rw [coeff_map, nat_degree_map_of_leading_coeff_ne_zero f hf],
end

lemma degree_pos_of_root {p : polynomial R} (hp : p ≠ 0) (h : is_root p a) : 0 < degree p :=
lt_of_not_ge $ λ hlt, begin
  have := eq_C_of_degree_le_zero hlt,
  rw [is_root, this, eval_C] at h,
  exact hp (finsupp.ext (λ n, show coeff p n = 0, from
    nat.cases_on n h (λ _, coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hlt
      (with_bot.coe_lt_coe.2 (nat.succ_pos _)))))),
end


variables [semiring S]

lemma nat_degree_pos_of_eval₂_root {p : polynomial R} (hp : p ≠ 0) (f : R →+* S)
  {z : S} (hz : eval₂ f z p = 0) (inj : ∀ (x : R), f x = 0 → x = 0) :
  0 < nat_degree p :=
lt_of_not_ge $ λ hlt, begin
  rw [eq_C_of_nat_degree_le_zero hlt, eval₂_C] at hz,
  refine hp (finsupp.ext (λ n, _)),
  cases n,
  { exact inj _ hz },
  { exact coeff_eq_zero_of_nat_degree_lt (lt_of_le_of_lt hlt (nat.succ_pos _)) }
end

lemma degree_pos_of_eval₂_root {p : polynomial R} (hp : p ≠ 0) (f : R →+* S)
  {z : S} (hz : eval₂ f z p = 0) (inj : ∀ (x : R), f x = 0 → x = 0) :
  0 < degree p :=
nat_degree_pos_iff_degree_pos.mp (nat_degree_pos_of_eval₂_root hp f hz inj)

section injective
open function
variables {f : R →+* S} (hf : injective f)
include hf

lemma degree_map_eq_of_injective (p : polynomial R) : degree (p.map f) = degree p :=
if h : p = 0 then by simp [h]
else degree_map_eq_of_leading_coeff_ne_zero _
  (by rw [← is_semiring_hom.map_zero f]; exact mt hf.eq_iff.1
    (mt leading_coeff_eq_zero.1 h))

lemma degree_map' (p : polynomial R) :
  degree (p.map f) = degree p :=
p.degree_map_eq_of_injective hf

lemma nat_degree_map' (p : polynomial R) :
  nat_degree (p.map f) = nat_degree p :=
nat_degree_eq_of_degree_eq (degree_map' hf p)

lemma leading_coeff_map' (p : polynomial R) :
  leading_coeff (p.map f) = f (leading_coeff p) :=
begin
  unfold leading_coeff,
  rw [coeff_map, nat_degree_map' hf p],
end

end injective

section
variable {f : polynomial R}

lemma monomial_nat_degree_leading_coeff_eq_self (h : f.support.card ≤ 1) :
  monomial f.nat_degree f.leading_coeff = f :=
begin
  interval_cases f.support.card with H,
  { have : f = 0 := finsupp.card_support_eq_zero.1 H,
    simp [this] },
  { obtain ⟨n, x, hx, rfl : f = monomial n x⟩ := finsupp.card_support_eq_one'.1 H,
    simp [hx] }
end

lemma C_mul_X_pow_eq_self (h : f.support.card ≤ 1) :
  C f.leading_coeff * X^f.nat_degree = f :=
by rw [C_mul_X_pow_eq_monomial, monomial_nat_degree_leading_coeff_eq_self h]

end

end degree
end semiring

end polynomial
