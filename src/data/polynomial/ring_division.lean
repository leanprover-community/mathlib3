
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/

import data.polynomial.basic
import data.polynomial.div
import data.polynomial.algebra_map

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $ R[X] $

-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

open finset

namespace polynomial
universes u v w z
variables {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section comm_ring
variables [comm_ring R] {p q : polynomial R}

variables [comm_ring S]

lemma nat_degree_pos_of_aeval_root [algebra R S] {p : polynomial R} (hp : p ≠ 0)
  {z : S} (hz : aeval z p = 0) (inj : ∀ (x : R), algebra_map R S x = 0 → x = 0) :
  0 < p.nat_degree :=
nat_degree_pos_of_eval₂_root hp (algebra_map R S) hz inj

lemma degree_pos_of_aeval_root [algebra R S] {p : polynomial R} (hp : p ≠ 0)
  {z : S} (hz : aeval z p = 0) (inj : ∀ (x : R), algebra_map R S x = 0 → x = 0) :
  0 < p.degree :=
nat_degree_pos_iff_degree_pos.mp (nat_degree_pos_of_aeval_root hp hz inj)

end comm_ring

section integral_domain
variables [integral_domain R] {p q : polynomial R}

instance : integral_domain (polynomial R) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b h, begin
    have : leading_coeff 0 = leading_coeff a * leading_coeff b := h ▸ leading_coeff_mul a b,
    rw [leading_coeff_zero, eq_comm] at this,
    erw [← leading_coeff_eq_zero, ← leading_coeff_eq_zero],
    exact eq_zero_or_eq_zero_of_mul_eq_zero this
  end,
  ..polynomial.nontrivial,
  ..polynomial.comm_ring }

lemma nat_degree_mul (hp : p ≠ 0) (hq : q ≠ 0) : nat_degree (p * q) =
  nat_degree p + nat_degree q :=
by rw [← with_bot.coe_eq_coe, ← degree_eq_nat_degree (mul_ne_zero hp hq),
    with_bot.coe_add, ← degree_eq_nat_degree hp,
    ← degree_eq_nat_degree hq, degree_mul]

@[simp] lemma nat_degree_pow (p : polynomial R) (n : ℕ) :
  nat_degree (p ^ n) = n * nat_degree p :=
if hp0 : p = 0
then if hn0 : n = 0 then by simp [hp0, hn0]
  else by rw [hp0, zero_pow (nat.pos_of_ne_zero hn0)]; simp
else nat_degree_pow'
  (by rw [← leading_coeff_pow, ne.def, leading_coeff_eq_zero]; exact pow_ne_zero _ hp0)

lemma root_mul : is_root (p * q) a ↔ is_root p a ∨ is_root q a :=
by simp_rw [is_root, eval_mul, mul_eq_zero]

lemma root_or_root_of_root_mul (h : is_root (p * q) a) : is_root p a ∨ is_root q a :=
root_mul.1 h

lemma degree_le_mul_left (p : polynomial R) (hq : q ≠ 0) : degree p ≤ degree (p * q) :=
if hp : p = 0 then by simp only [hp, zero_mul, le_refl]
else by rw [degree_mul, degree_eq_nat_degree hp,
    degree_eq_nat_degree hq];
  exact with_bot.coe_le_coe.2 (nat.le_add_right _ _)

theorem nat_degree_le_of_dvd {p q : polynomial R} (h1 : p ∣ q) (h2 : q ≠ 0) : p.nat_degree ≤ q.nat_degree :=
begin
  rcases h1 with ⟨q, rfl⟩, rw mul_ne_zero_iff at h2,
  rw [nat_degree_mul h2.1 h2.2], exact nat.le_add_right _ _
end

lemma exists_finset_roots : ∀ {p : polynomial R} (hp : p ≠ 0),
  ∃ s : finset R, (s.card : with_bot ℕ) ≤ degree p ∧ ∀ x, x ∈ s ↔ is_root p x
| p := λ hp, by haveI := classical.prop_decidable (∃ x, is_root p x); exact
if h : ∃ x, is_root p x
then
  let ⟨x, hx⟩ := h in
  have hpd : 0 < degree p := degree_pos_of_root hp hx,
  have hd0 : p /ₘ (X - C x) ≠ 0 :=
    λ h, by rw [← mul_div_by_monic_eq_iff_is_root.2 hx, h, mul_zero] at hp; exact hp rfl,
  have wf : degree (p /ₘ _) < degree p :=
    degree_div_by_monic_lt _ (monic_X_sub_C x) hp
    ((degree_X_sub_C x).symm ▸ dec_trivial),
  let ⟨t, htd, htr⟩ := @exists_finset_roots (p /ₘ (X - C x)) hd0 in
  have hdeg : degree (X - C x) ≤ degree p := begin
    rw [degree_X_sub_C, degree_eq_nat_degree hp],
    rw degree_eq_nat_degree hp at hpd,
    exact with_bot.coe_le_coe.2 (with_bot.coe_lt_coe.1 hpd)
  end,
  have hdiv0 : p /ₘ (X - C x) ≠ 0 := mt (div_by_monic_eq_zero_iff (monic_X_sub_C x)
    (ne_zero_of_monic (monic_X_sub_C x))).1 $ not_lt.2 hdeg,
  ⟨insert x t, calc (card (insert x t) : with_bot ℕ) ≤ card t + 1 :
    with_bot.coe_le_coe.2 $ finset.card_insert_le _ _
    ... ≤ degree p :
      by rw [← degree_add_div_by_monic (monic_X_sub_C x) hdeg,
          degree_X_sub_C, add_comm];
        exact add_le_add (le_refl (1 : with_bot ℕ)) htd,
  begin
    assume y,
    rw [mem_insert, htr, eq_comm, ← root_X_sub_C],
    conv {to_rhs, rw ← mul_div_by_monic_eq_iff_is_root.2 hx},
    exact ⟨λ h, or.cases_on h (root_mul_right_of_is_root _) (root_mul_left_of_is_root _),
      root_or_root_of_root_mul⟩
  end⟩
else
  ⟨∅, (degree_eq_nat_degree hp).symm ▸ with_bot.coe_le_coe.2 (nat.zero_le _),
    by simpa only [not_mem_empty, false_iff, not_exists] using h⟩
using_well_founded {dec_tac := tactic.assumption}

/-- `roots p` noncomputably gives a finset containing all the roots of `p` -/
noncomputable def roots (p : polynomial R) : finset R :=
if h : p = 0 then ∅ else classical.some (exists_finset_roots h)

lemma card_roots (hp0 : p ≠ 0) : ((roots p).card : with_bot ℕ) ≤ degree p :=
begin
  unfold roots,
  rw dif_neg hp0,
  exact (classical.some_spec (exists_finset_roots hp0)).1
end

lemma card_roots' {p : polynomial R} (hp0 : p ≠ 0) : p.roots.card ≤ nat_degree p :=
with_bot.coe_le_coe.1 (le_trans (card_roots hp0) (le_of_eq $ degree_eq_nat_degree hp0))

lemma card_roots_sub_C {p : polynomial R} {a : R} (hp0 : 0 < degree p) :
  ((p - C a).roots.card : with_bot ℕ) ≤ degree p :=
calc ((p - C a).roots.card : with_bot ℕ) ≤ degree (p - C a) :
  card_roots $ mt sub_eq_zero.1 $ λ h, not_le_of_gt hp0 $ h.symm ▸ degree_C_le
... = degree p : by rw [sub_eq_add_neg, ← C_neg]; exact degree_add_C hp0

lemma card_roots_sub_C' {p : polynomial R} {a : R} (hp0 : 0 < degree p) :
  (p - C a).roots.card ≤ nat_degree p :=
with_bot.coe_le_coe.1 (le_trans (card_roots_sub_C hp0) (le_of_eq $ degree_eq_nat_degree
  (λ h, by simp [*, lt_irrefl] at *)))

@[simp] lemma mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ is_root p a :=
by unfold roots; rw dif_neg hp; exact (classical.some_spec (exists_finset_roots hp)).2 _

lemma roots_mul (hpq : p * q ≠ 0) : (p * q).roots = p.roots ∪ q.roots :=
finset.ext $ λ r, by rw [mem_union, mem_roots hpq, mem_roots (mul_ne_zero_iff.1 hpq).1,
    mem_roots (mul_ne_zero_iff.1 hpq).2, root_mul]

@[simp] lemma mem_roots_sub_C {p : polynomial R} {a x : R} (hp0 : 0 < degree p) :
  x ∈ (p - C a).roots ↔ p.eval x = a :=
(mem_roots (show p - C a ≠ 0, from mt sub_eq_zero.1 $ λ h,
    not_le_of_gt hp0 $ h.symm ▸ degree_C_le)).trans
  (by rw [is_root.def, eval_sub, eval_C, sub_eq_zero])

@[simp] lemma roots_X_sub_C (r : R) : roots (X - C r) = {r} :=
finset.ext $ λ s, by rw [mem_roots (X_sub_C_ne_zero r), root_X_sub_C, mem_singleton, eq_comm]

lemma card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
  (roots ((X : polynomial R) ^ n - C a)).card ≤ n :=
with_bot.coe_le_coe.1 $
calc ((roots ((X : polynomial R) ^ n - C a)).card : with_bot ℕ)
      ≤ degree ((X : polynomial R) ^ n - C a) : card_roots (X_pow_sub_C_ne_zero hn a)
  ... = n : degree_X_pow_sub_C hn a


/-- `nth_roots n a` noncomputably returns the solutions to `x ^ n = a`-/
def nth_roots {R : Type*} [integral_domain R] (n : ℕ) (a : R) : finset R :=
roots ((X : polynomial R) ^ n - C a)

@[simp] lemma mem_nth_roots {R : Type*} [integral_domain R] {n : ℕ} (hn : 0 < n) {a x : R} :
  x ∈ nth_roots n a ↔ x ^ n = a :=
by rw [nth_roots, mem_roots (X_pow_sub_C_ne_zero hn a),
  is_root.def, eval_sub, eval_C, eval_pow, eval_X, sub_eq_zero_iff_eq]

lemma card_nth_roots {R : Type*} [integral_domain R] (n : ℕ) (a : R) :
  (nth_roots n a).card ≤ n :=
if hn : n = 0
then if h : (X : polynomial R) ^ n - C a = 0
  then by simp only [nat.zero_le, nth_roots, roots, h, dif_pos rfl, card_empty]
  else with_bot.coe_le_coe.1 (le_trans (card_roots h)
   (by rw [hn, pow_zero, ← C_1, ← @is_ring_hom.map_sub _ _ _ _ (@C R _)];
      exact degree_C_le))
else by rw [← with_bot.coe_le_coe, ← degree_X_pow_sub_C (nat.pos_of_ne_zero hn) a];
  exact card_roots (X_pow_sub_C_ne_zero (nat.pos_of_ne_zero hn) a)

lemma coeff_comp_degree_mul_degree (hqd0 : nat_degree q ≠ 0) :
  coeff (p.comp q) (nat_degree p * nat_degree q) =
  leading_coeff p * leading_coeff q ^ nat_degree p :=
if hp0 : p = 0 then by simp [hp0] else
calc coeff (p.comp q) (nat_degree p * nat_degree q)
  = p.sum (λ n a, coeff (C a * q ^ n) (nat_degree p * nat_degree q)) :
    by rw [comp, eval₂, coeff_sum]
... = coeff (C (leading_coeff p) * q ^ nat_degree p) (nat_degree p * nat_degree q) :
  finset.sum_eq_single _
  begin
    assume b hbs hbp,
    have hq0 : q ≠ 0, from λ hq0, hqd0 (by rw [hq0, nat_degree_zero]),
    have : coeff p b ≠ 0, rwa finsupp.mem_support_iff at hbs,
    refine coeff_eq_zero_of_degree_lt _,
    rw [degree_mul], erw degree_C this,
    rw [degree_pow, zero_add, degree_eq_nat_degree hq0,
      ← with_bot.coe_nsmul, nsmul_eq_mul, with_bot.coe_lt_coe, nat.cast_id],
    rw mul_lt_mul_right, apply lt_of_le_of_ne, assumption', swap, omega,
    exact le_nat_degree_of_ne_zero this,
  end
  begin
    intro h, contrapose! hp0,
    rw finsupp.mem_support_iff at h, push_neg at h,
    rwa ← leading_coeff_eq_zero,
  end
... = _ :
  have coeff (q ^ nat_degree p) (nat_degree p * nat_degree q) = leading_coeff (q ^ nat_degree p),
    by rw [leading_coeff, nat_degree_pow],
  by rw [coeff_C_mul, this, leading_coeff_pow]

lemma nat_degree_comp : nat_degree (p.comp q) = nat_degree p * nat_degree q :=
le_antisymm nat_degree_comp_le
  (if hp0 : p = 0 then by rw [hp0, zero_comp, nat_degree_zero, zero_mul]
  else if hqd0 : nat_degree q = 0
  then have degree q ≤ 0, by rw [← with_bot.coe_zero, ← hqd0]; exact degree_le_nat_degree,
    by rw [eq_C_of_degree_le_zero this]; simp
  else le_nat_degree_of_ne_zero $
    have hq0 : q ≠ 0, from λ hq0, hqd0 $ by rw [hq0, nat_degree_zero],
    calc coeff (p.comp q) (nat_degree p * nat_degree q)
        = leading_coeff p * leading_coeff q ^ nat_degree p :
      coeff_comp_degree_mul_degree hqd0
    ... ≠ 0 : mul_ne_zero (mt leading_coeff_eq_zero.1 hp0)
      (pow_ne_zero _ (mt leading_coeff_eq_zero.1 hq0)))

lemma leading_coeff_comp (hq : nat_degree q ≠ 0) : leading_coeff (p.comp q) =
  leading_coeff p * leading_coeff q ^ nat_degree p :=
by rw [← coeff_comp_degree_mul_degree hq, ← nat_degree_comp]; refl

lemma degree_eq_zero_of_is_unit (h : is_unit p) : degree p = 0 :=
let ⟨q, hq⟩ := is_unit_iff_dvd_one.1 h in
have hp0 : p ≠ 0, from λ hp0, by simpa [hp0] using hq,
have hq0 : q ≠ 0, from λ hp0, by simpa [hp0] using hq,
have nat_degree (1 : polynomial R) = nat_degree (p * q),
  from congr_arg _ hq,
by rw [nat_degree_one, nat_degree_mul hp0 hq0, eq_comm,
    _root_.add_eq_zero_iff, ← with_bot.coe_eq_coe,
    ← degree_eq_nat_degree hp0] at this;
  exact this.1

@[simp] lemma degree_coe_units (u : units (polynomial R)) :
  degree (u : polynomial R) = 0 :=
degree_eq_zero_of_is_unit ⟨u, rfl⟩

@[simp] lemma nat_degree_coe_units (u : units (polynomial R)) :
  nat_degree (u : polynomial R) = 0 :=
nat_degree_eq_of_degree_eq_some (degree_coe_units u)

theorem is_unit_iff {f : polynomial R} : is_unit f ↔ ∃ r : R, is_unit r ∧ C r = f :=
⟨λ hf, ⟨f.coeff 0,
  is_unit_C.1 $ eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf) ▸ hf,
  (eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf)).symm⟩,
λ ⟨r, hr, hrf⟩, hrf ▸ is_unit_C.2 hr⟩

lemma coeff_coe_units_zero_ne_zero (u : units (polynomial R)) :
  coeff (u : polynomial R) 0 ≠ 0 :=
begin
  conv in (0) {rw [← nat_degree_coe_units u]},
  rw [← leading_coeff, ne.def, leading_coeff_eq_zero],
  exact units.coe_ne_zero _
end

lemma degree_eq_degree_of_associated (h : associated p q) : degree p = degree q :=
let ⟨u, hu⟩ := h in by simp [hu.symm]

lemma degree_eq_one_of_irreducible_of_root (hi : irreducible p) {x : R} (hx : is_root p x) :
  degree p = 1 :=
let ⟨g, hg⟩ := dvd_iff_is_root.2 hx in
have is_unit (X - C x) ∨ is_unit g, from hi.2 _ _ hg,
this.elim
  (λ h, have h₁ : degree (X - C x) = 1, from degree_X_sub_C x,
    have h₂ : degree (X - C x) = 0, from degree_eq_zero_of_is_unit h,
    by rw h₁ at h₂; exact absurd h₂ dec_trivial)
  (λ hgu, by rw [hg, degree_mul, degree_X_sub_C, degree_eq_zero_of_is_unit hgu, add_zero])

theorem prime_X_sub_C {r : R} : prime (X - C r) :=
⟨X_sub_C_ne_zero r, not_is_unit_X_sub_C,
λ _ _, by { simp_rw [dvd_iff_is_root, is_root.def, eval_mul, mul_eq_zero], exact id }⟩

theorem prime_X : prime (X : polynomial R) :=
by simpa only [C_0, sub_zero] using (prime_X_sub_C : prime (X - C 0 : polynomial R))

lemma prime_of_degree_eq_one_of_monic (hp1 : degree p = 1)
  (hm : monic p) : prime p :=
have p = X - C (- p.coeff 0),
  by simpa [hm.leading_coeff] using eq_X_add_C_of_degree_eq_one hp1,
this.symm ▸ prime_X_sub_C

theorem irreducible_X_sub_C (r : R) : irreducible (X - C r) :=
irreducible_of_prime prime_X_sub_C

theorem irreducible_X : irreducible (X : polynomial R) :=
irreducible_of_prime prime_X

lemma irreducible_of_degree_eq_one_of_monic (hp1 : degree p = 1)
  (hm : monic p) : irreducible p :=
irreducible_of_prime (prime_of_degree_eq_one_of_monic hp1 hm)

end integral_domain


end polynomial

namespace is_integral_domain

variables {R : Type*} [comm_ring R]

/-- Lift evidence that `is_integral_domain R` to `is_integral_domain (polynomial R)`. -/
lemma polynomial (h : is_integral_domain R) : is_integral_domain (polynomial R) :=
@integral_domain.to_is_integral_domain _ (@polynomial.integral_domain _ (h.to_integral_domain _))

end is_integral_domain
