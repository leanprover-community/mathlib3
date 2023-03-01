/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker, Johan Commelin
-/
import algebra.char_zero.infinite
import data.polynomial.algebra_map
import data.polynomial.degree.lemmas
import data.polynomial.div
import ring_theory.localization.fraction_ring
import algebra.polynomial.big_operators

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $ R[X] $

## Main definitions

* `polynomial.roots p`: The multiset containing all the roots of `p`, including their
  multiplicities.
* `polynomial.root_set p E`: The set of distinct roots of `p` in an algebra `E`.

## Main statements

* `polynomial.C_leading_coeff_mul_prod_multiset_X_sub_C`: If a polynomial has as many roots as its
  degree, it can be written as the product of its leading coefficient with `∏ (X - a)` where `a`
  ranges through its roots.

-/

noncomputable theory
open_locale classical polynomial

open finset

namespace polynomial
universes u v w z
variables {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

section comm_ring
variables [comm_ring R] {p q : R[X]}

section
variables [semiring S]

lemma nat_degree_pos_of_aeval_root [algebra R S] {p : R[X]} (hp : p ≠ 0)
  {z : S} (hz : aeval z p = 0) (inj : ∀ (x : R), algebra_map R S x = 0 → x = 0) :
  0 < p.nat_degree :=
nat_degree_pos_of_eval₂_root hp (algebra_map R S) hz inj

lemma degree_pos_of_aeval_root [algebra R S] {p : R[X]} (hp : p ≠ 0)
  {z : S} (hz : aeval z p = 0) (inj : ∀ (x : R), algebra_map R S x = 0 → x = 0) :
  0 < p.degree :=
nat_degree_pos_iff_degree_pos.mp (nat_degree_pos_of_aeval_root hp hz inj)

lemma mod_by_monic_eq_of_dvd_sub (hq : q.monic) {p₁ p₂ : R[X]}
  (h : q ∣ (p₁ - p₂)) :
  p₁ %ₘ q = p₂ %ₘ q :=
begin
  nontriviality R,
  obtain ⟨f, sub_eq⟩ := h,
  refine (div_mod_by_monic_unique (p₂ /ₘ q + f) _ hq
    ⟨_, degree_mod_by_monic_lt _ hq⟩).2,
  rw [sub_eq_iff_eq_add.mp sub_eq, mul_add, ← add_assoc, mod_by_monic_add_div _ hq, add_comm]
end

lemma add_mod_by_monic (p₁ p₂ : R[X]) : (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q :=
begin
  by_cases hq : q.monic,
  { nontriviality R,
    exact (div_mod_by_monic_unique (p₁ /ₘ q + p₂ /ₘ q) _ hq
      ⟨by rw [mul_add, add_left_comm, add_assoc, mod_by_monic_add_div _ hq, ← add_assoc,
              add_comm (q * _), mod_by_monic_add_div _ hq],
        (degree_add_le _ _).trans_lt (max_lt (degree_mod_by_monic_lt _ hq)
          (degree_mod_by_monic_lt _ hq))⟩).2 },
  { simp_rw mod_by_monic_eq_of_not_monic _ hq }
end

lemma smul_mod_by_monic (c : R) (p : R[X]) : (c • p) %ₘ q = c • (p %ₘ q) :=
begin
  by_cases hq : q.monic,
  { nontriviality R,
    exact (div_mod_by_monic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
      ⟨by rw [mul_smul_comm, ← smul_add, mod_by_monic_add_div p hq],
      (degree_smul_le _ _).trans_lt (degree_mod_by_monic_lt _ hq)⟩).2 },
  { simp_rw mod_by_monic_eq_of_not_monic _ hq }
end

/--  `_ %ₘ q` as an `R`-linear map. -/
@[simps]
def mod_by_monic_hom (q : R[X]) : R[X] →ₗ[R] R[X] :=
{ to_fun := λ p, p %ₘ q,
  map_add' := add_mod_by_monic,
  map_smul' := smul_mod_by_monic }

end

section
variables [ring S]

lemma aeval_mod_by_monic_eq_self_of_root [algebra R S]
  {p q : R[X]} (hq : q.monic) {x : S} (hx : aeval x q = 0) :
  aeval x (p %ₘ q) = aeval x p :=
-- `eval₂_mod_by_monic_eq_self_of_root` doesn't work here as it needs commutativity
by rw [mod_by_monic_eq_sub_mul_div p hq, _root_.map_sub, _root_.map_mul, hx, zero_mul, sub_zero]

end

end comm_ring

section no_zero_divisors
variables [semiring R] [no_zero_divisors R] {p q : R[X]}

instance : no_zero_divisors R[X] :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b h, begin
    rw [← leading_coeff_eq_zero, ← leading_coeff_eq_zero],
    refine eq_zero_or_eq_zero_of_mul_eq_zero _,
    rw [← leading_coeff_zero, ← leading_coeff_mul, h],
  end }

lemma nat_degree_mul (hp : p ≠ 0) (hq : q ≠ 0) : nat_degree (p * q) =
  nat_degree p + nat_degree q :=
by rw [← with_bot.coe_eq_coe, ← degree_eq_nat_degree (mul_ne_zero hp hq),
    with_bot.coe_add, ← degree_eq_nat_degree hp,
    ← degree_eq_nat_degree hq, degree_mul]

lemma trailing_degree_mul : (p * q).trailing_degree = p.trailing_degree + q.trailing_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, trailing_degree_zero, top_add] },
  by_cases hq : q = 0,
  { rw [hq, mul_zero, trailing_degree_zero, add_top] },
  rw [trailing_degree_eq_nat_trailing_degree hp, trailing_degree_eq_nat_trailing_degree hq,
      trailing_degree_eq_nat_trailing_degree (mul_ne_zero hp hq),
      nat_trailing_degree_mul hp hq, with_top.coe_add],
end

@[simp] lemma nat_degree_pow (p : R[X]) (n : ℕ) :
  nat_degree (p ^ n) = n * nat_degree p :=
if hp0 : p = 0
then if hn0 : n = 0 then by simp [hp0, hn0]
  else by rw [hp0, zero_pow (nat.pos_of_ne_zero hn0)]; simp
else nat_degree_pow'
  (by rw [← leading_coeff_pow, ne.def, leading_coeff_eq_zero]; exact pow_ne_zero _ hp0)

lemma degree_le_mul_left (p : R[X]) (hq : q ≠ 0) : degree p ≤ degree (p * q) :=
if hp : p = 0 then by simp only [hp, zero_mul, le_refl]
else by rw [degree_mul, degree_eq_nat_degree hp,
    degree_eq_nat_degree hq];
  exact with_bot.coe_le_coe.2 (nat.le_add_right _ _)

theorem nat_degree_le_of_dvd {p q : R[X]} (h1 : p ∣ q) (h2 : q ≠ 0) :
  p.nat_degree ≤ q.nat_degree :=
begin
  rcases h1 with ⟨q, rfl⟩, rw mul_ne_zero_iff at h2,
  rw [nat_degree_mul h2.1 h2.2], exact nat.le_add_right _ _
end

lemma degree_le_of_dvd {p q : R[X]} (h1 : p ∣ q) (h2 : q ≠ 0) : degree p ≤ degree q :=
begin
  rcases h1 with ⟨q, rfl⟩, rw mul_ne_zero_iff at h2,
  exact degree_le_mul_left p h2.2,
end

lemma eq_zero_of_dvd_of_degree_lt {p q : R[X]} (h₁ : p ∣ q) (h₂ : degree q < degree p) :
  q = 0 :=
begin
  by_contradiction hc,
  exact (lt_iff_not_ge _ _ ).mp h₂ (degree_le_of_dvd h₁ hc),
end

lemma eq_zero_of_dvd_of_nat_degree_lt {p q : R[X]} (h₁ : p ∣ q) (h₂ : nat_degree q < nat_degree p) :
  q = 0 :=
begin
  by_contradiction hc,
  exact (lt_iff_not_ge _ _ ).mp h₂ (nat_degree_le_of_dvd h₁ hc),
end

theorem not_dvd_of_degree_lt {p q : R[X]} (h0 : q ≠ 0)
  (hl : q.degree < p.degree) : ¬ p ∣ q :=
begin
  by_contra hcontra,
  exact h0 (eq_zero_of_dvd_of_degree_lt hcontra hl),
end

theorem not_dvd_of_nat_degree_lt {p q : R[X]} (h0 : q ≠ 0)
  (hl : q.nat_degree < p.nat_degree) : ¬ p ∣ q :=
begin
  by_contra hcontra,
  exact h0 (eq_zero_of_dvd_of_nat_degree_lt hcontra hl),
end

/-- This lemma is useful for working with the `int_degree` of a rational function. -/
lemma nat_degree_sub_eq_of_prod_eq {p₁ p₂ q₁ q₂ : R[X]} (hp₁ : p₁ ≠ 0) (hq₁ : q₁ ≠ 0)
  (hp₂ : p₂ ≠ 0) (hq₂ : q₂ ≠ 0) (h_eq : p₁ * q₂ = p₂ * q₁) :
  (p₁.nat_degree : ℤ) - q₁.nat_degree = (p₂.nat_degree : ℤ) - q₂.nat_degree :=
begin
  rw sub_eq_sub_iff_add_eq_add,
  norm_cast,
  rw [← nat_degree_mul hp₁ hq₂, ← nat_degree_mul hp₂ hq₁, h_eq]
end

lemma nat_degree_eq_zero_of_is_unit (h : is_unit p) : nat_degree p = 0 :=
begin
  nontriviality R,
  obtain ⟨q, hq⟩ := h.exists_right_inv,
  have := nat_degree_mul (left_ne_zero_of_mul_eq_one hq) (right_ne_zero_of_mul_eq_one hq),
  rw [hq, nat_degree_one, eq_comm, add_eq_zero_iff] at this,
  exact this.1,
end

lemma degree_eq_zero_of_is_unit [nontrivial R] (h : is_unit p) : degree p = 0 :=
(nat_degree_eq_zero_iff_degree_le_zero.mp $ nat_degree_eq_zero_of_is_unit h).antisymm
  (zero_le_degree_iff.mpr h.ne_zero)

@[simp] lemma degree_coe_units [nontrivial R] (u : R[X]ˣ) : degree (u : R[X]) = 0 :=
degree_eq_zero_of_is_unit ⟨u, rfl⟩

theorem is_unit_iff : is_unit p ↔ ∃ r : R, is_unit r ∧ C r = p :=
⟨λ hp, ⟨p.coeff 0, let h := eq_C_of_nat_degree_eq_zero (nat_degree_eq_zero_of_is_unit hp) in
  ⟨is_unit_C.1 (h ▸ hp), h.symm⟩⟩, λ ⟨r, hr, hrp⟩, hrp ▸ is_unit_C.2 hr⟩

variables [char_zero R]

@[simp] lemma degree_bit0_eq (p : R[X]) : degree (bit0 p) = degree p :=
by rw [bit0_eq_two_mul, degree_mul, (by simp : (2 : R[X]) = C 2),
  @polynomial.degree_C R _ _ two_ne_zero, zero_add]

@[simp] lemma nat_degree_bit0_eq (p : R[X]) : nat_degree (bit0 p) = nat_degree p :=
nat_degree_eq_of_degree_eq $ degree_bit0_eq p

@[simp]
lemma nat_degree_bit1_eq (p : R[X]) : nat_degree (bit1 p) = nat_degree p :=
begin
  rw bit1,
  apply le_antisymm,
  convert nat_degree_add_le _ _,
  { simp, },
  by_cases h : p.nat_degree = 0,
  { simp [h], },
  apply le_nat_degree_of_ne_zero,
  intro hh,
  apply h,
  simp [*, coeff_one, if_neg (ne.symm h)] at *,
end

lemma degree_bit1_eq {p : R[X]} (hp : 0 < degree p) : degree (bit1 p) = degree p :=
begin
  rw [bit1, degree_add_eq_left_of_degree_lt, degree_bit0_eq],
  rwa [degree_one, degree_bit0_eq]
end

end no_zero_divisors

section no_zero_divisors
variables [comm_semiring R] [no_zero_divisors R] {p q : R[X]}

lemma irreducible_of_monic (hp : p.monic) (hp1 : p ≠ 1) :
  irreducible p ↔ ∀ f g : R[X], f.monic → g.monic → f * g = p → f = 1 ∨ g = 1 :=
begin
  refine ⟨λ h f g hf hg hp, (h.2 f g hp.symm).imp hf.eq_one_of_is_unit hg.eq_one_of_is_unit,
    λ h, ⟨hp1 ∘ hp.eq_one_of_is_unit, λ f g hfg, (h (g * C f.leading_coeff) (f * C g.leading_coeff)
      _ _ _).symm.imp (is_unit_of_mul_eq_one f _) (is_unit_of_mul_eq_one g _)⟩⟩,
  { rwa [monic, leading_coeff_mul, leading_coeff_C, ←leading_coeff_mul, mul_comm, ←hfg, ←monic] },
  { rwa [monic, leading_coeff_mul, leading_coeff_C, ←leading_coeff_mul, ←hfg, ←monic] },
  { rw [mul_mul_mul_comm, ←C_mul, ←leading_coeff_mul, ←hfg, hp.leading_coeff, C_1, mul_one,
        mul_comm, ←hfg] },
end

lemma monic.irreducible_iff_nat_degree (hp : p.monic) : irreducible p ↔
  p ≠ 1 ∧ ∀ f g : R[X], f.monic → g.monic → f * g = p → f.nat_degree = 0 ∨ g.nat_degree = 0 :=
begin
  by_cases hp1 : p = 1, { simp [hp1] },
  rw [irreducible_of_monic hp hp1, and_iff_right hp1],
  refine forall₄_congr (λ a b ha hb, _),
  rw [ha.nat_degree_eq_zero_iff_eq_one, hb.nat_degree_eq_zero_iff_eq_one],
end

lemma monic.irreducible_iff_nat_degree' (hp : p.monic) : irreducible p ↔ p ≠ 1 ∧
  ∀ f g : R[X], f.monic → g.monic → f * g = p → g.nat_degree ∉ Ioc 0 (p.nat_degree / 2) :=
begin
  simp_rw [hp.irreducible_iff_nat_degree, mem_Ioc, nat.le_div_iff_mul_le zero_lt_two, mul_two],
  apply and_congr_right',
  split; intros h f g hf hg he; subst he,
  { rw [hf.nat_degree_mul hg, add_le_add_iff_right],
    exact λ ha, (h f g hf hg rfl).elim (ha.1.trans_le ha.2).ne' ha.1.ne' },
  { simp_rw [hf.nat_degree_mul hg, pos_iff_ne_zero] at h,
    contrapose! h,
    obtain hl|hl := le_total f.nat_degree g.nat_degree,
    { exact ⟨g, f, hg, hf, mul_comm g f, h.1, add_le_add_left hl _⟩ },
    { exact ⟨f, g, hf, hg, rfl, h.2, add_le_add_right hl _⟩ } },
end

lemma monic.not_irreducible_iff_exists_add_mul_eq_coeff (hm : p.monic) (hnd : p.nat_degree = 2) :
  ¬ irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂ :=
begin
  casesI subsingleton_or_nontrivial R,
  { simpa only [nat_degree_of_subsingleton] using hnd },
  rw [hm.irreducible_iff_nat_degree', and_iff_right, hnd],
  push_neg, split,
  { rintros ⟨a, b, ha, hb, rfl, hdb|⟨⟨⟩⟩⟩,
    have hda := hnd, rw [ha.nat_degree_mul hb, hdb] at hda,
    use [a.coeff 0, b.coeff 0, mul_coeff_zero a b],
    simpa only [next_coeff, hnd, add_right_cancel hda, hdb] using ha.next_coeff_mul hb },
  { rintros ⟨c₁, c₂, hmul, hadd⟩,
    refine ⟨X + C c₁, X + C c₂, monic_X_add_C _, monic_X_add_C _, _, or.inl $ nat_degree_X_add_C _⟩,
    rw [p.as_sum_range_C_mul_X_pow, hnd, finset.sum_range_succ, finset.sum_range_succ,
      finset.sum_range_one, ← hnd, hm.coeff_nat_degree, hnd, hmul, hadd, C_mul, C_add, C_1],
    ring },
  { rintro rfl, simpa only [nat_degree_one] using hnd },
end

lemma root_mul : is_root (p * q) a ↔ is_root p a ∨ is_root q a :=
by simp_rw [is_root, eval_mul, mul_eq_zero]

lemma root_or_root_of_root_mul (h : is_root (p * q) a) : is_root p a ∨ is_root q a :=
root_mul.1 h

end no_zero_divisors

section ring
variables [ring R] [is_domain R] {p q : R[X]}

instance : is_domain R[X] :=
no_zero_divisors.to_is_domain _

end ring

section comm_ring
variable [comm_ring R]

/-- The multiplicity of `a` as root of a nonzero polynomial `p` is at least `n` iff
  `(X - a) ^ n` divides `p`. -/
lemma le_root_multiplicity_iff {p : R[X]} (p0 : p ≠ 0) {a : R} {n : ℕ} :
  n ≤ root_multiplicity a p ↔ (X - C a) ^ n ∣ p :=
begin
  simp_rw [root_multiplicity, dif_neg p0, nat.le_find_iff, not_not],
  refine ⟨λ h, _, λ h m hm, (pow_dvd_pow _ hm).trans h⟩,
  cases n, { rw pow_zero, apply one_dvd }, { exact h n n.lt_succ_self },
end

lemma root_multiplicity_le_iff {p : R[X]} (p0 : p ≠ 0) (a : R) (n : ℕ) :
  root_multiplicity a p ≤ n ↔ ¬ (X - C a) ^ (n + 1) ∣ p :=
by rw [← (le_root_multiplicity_iff p0).not, not_le, nat.lt_add_one_iff]

lemma pow_root_multiplicity_not_dvd {p : R[X]} (p0 : p ≠ 0) (a : R) :
  ¬ (X - C a) ^ (root_multiplicity a p + 1) ∣ p :=
by rw [← root_multiplicity_le_iff p0]

/-- The multiplicity of `p + q` is at least the minimum of the multiplicities. -/
lemma root_multiplicity_add {p q : R[X]} (a : R) (hzero : p + q ≠ 0) :
  min (root_multiplicity a p) (root_multiplicity a q) ≤ root_multiplicity a (p + q) :=
begin
  rw le_root_multiplicity_iff hzero,
  have hdivp : (X - C a) ^ root_multiplicity a p ∣ p := pow_root_multiplicity_dvd p a,
  have hdivq : (X - C a) ^ root_multiplicity a q ∣ q := pow_root_multiplicity_dvd q a,
  exact min_pow_dvd_add hdivp hdivq
end

variables [is_domain R] {p q : R[X]}

section roots

open multiset

theorem prime_X_sub_C (r : R) : prime (X - C r) :=
⟨X_sub_C_ne_zero r, not_is_unit_X_sub_C r,
 λ _ _, by { simp_rw [dvd_iff_is_root, is_root.def, eval_mul, mul_eq_zero], exact id }⟩

theorem prime_X : prime (X : R[X]) :=
by { convert (prime_X_sub_C (0 : R)), simp }

lemma monic.prime_of_degree_eq_one (hp1 : degree p = 1) (hm : monic p) :
  prime p :=
have p = X - C (- p.coeff 0),
  by simpa [hm.leading_coeff] using eq_X_add_C_of_degree_eq_one hp1,
this.symm ▸ prime_X_sub_C _

theorem irreducible_X_sub_C (r : R) : irreducible (X - C r) :=
(prime_X_sub_C r).irreducible

theorem irreducible_X : irreducible (X : R[X]) :=
prime.irreducible prime_X

lemma monic.irreducible_of_degree_eq_one (hp1 : degree p = 1) (hm : monic p) :
  irreducible p :=
(hm.prime_of_degree_eq_one hp1).irreducible

theorem eq_of_monic_of_associated (hp : p.monic) (hq : q.monic) (hpq : associated p q) : p = q :=
begin
  obtain ⟨u, hu⟩ := hpq,
  unfold monic at hp hq,
  rw eq_C_of_degree_le_zero (degree_coe_units _).le at hu,
  rw [← hu, leading_coeff_mul, hp, one_mul, leading_coeff_C] at hq,
  rwa [hq, C_1, mul_one] at hu,
  all_goals { apply_instance },
end

lemma root_multiplicity_mul {p q : R[X]} {x : R} (hpq : p * q ≠ 0) :
  root_multiplicity x (p * q) = root_multiplicity x p + root_multiplicity x q :=
begin
  have hp : p ≠ 0 := left_ne_zero_of_mul hpq,
  have hq : q ≠ 0 := right_ne_zero_of_mul hpq,
  rw [root_multiplicity_eq_multiplicity (p * q), dif_neg hpq,
      root_multiplicity_eq_multiplicity p, dif_neg hp,
      root_multiplicity_eq_multiplicity q, dif_neg hq,
      multiplicity.mul' (prime_X_sub_C x)],
end

lemma root_multiplicity_X_sub_C_self {x : R} :
  root_multiplicity x (X - C x) = 1 :=
by rw [root_multiplicity_eq_multiplicity, dif_neg (X_sub_C_ne_zero x),
       multiplicity.get_multiplicity_self]

lemma root_multiplicity_X_sub_C {x y : R} :
  root_multiplicity x (X - C y) = if x = y then 1 else 0 :=
begin
  split_ifs with hxy,
  { rw hxy,
    exact root_multiplicity_X_sub_C_self },
  exact root_multiplicity_eq_zero (mt root_X_sub_C.mp (ne.symm hxy))
end

/-- The multiplicity of `a` as root of `(X - a) ^ n` is `n`. -/
lemma root_multiplicity_X_sub_C_pow (a : R) (n : ℕ) : root_multiplicity a ((X - C a) ^ n) = n :=
begin
  induction n with n hn,
  { refine root_multiplicity_eq_zero _,
    simp only [eval_one, is_root.def, not_false_iff, one_ne_zero, pow_zero] },
  have hzero := pow_ne_zero n.succ (X_sub_C_ne_zero a),
  rw pow_succ (X - C a) n at hzero ⊢,
  simp only [root_multiplicity_mul hzero, root_multiplicity_X_sub_C_self, hn, nat.one_add]
end

lemma exists_multiset_roots : ∀ {p : R[X]} (hp : p ≠ 0),
  ∃ s : multiset R, (s.card : with_bot ℕ) ≤ degree p ∧ ∀ a, s.count a = root_multiplicity a p
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
  let ⟨t, htd, htr⟩ := @exists_multiset_roots (p /ₘ (X - C x)) hd0 in
  have hdeg : degree (X - C x) ≤ degree p := begin
    rw [degree_X_sub_C, degree_eq_nat_degree hp],
    rw degree_eq_nat_degree hp at hpd,
    exact with_bot.coe_le_coe.2 (with_bot.coe_lt_coe.1 hpd)
  end,
  have hdiv0 : p /ₘ (X - C x) ≠ 0 := mt (div_by_monic_eq_zero_iff (monic_X_sub_C x)).1 $
    not_lt.2 hdeg,
  ⟨x ::ₘ t, calc (card (x ::ₘ t) : with_bot ℕ) = t.card + 1 :
      by exact_mod_cast card_cons _ _
    ... ≤ degree p :
      by rw [← degree_add_div_by_monic (monic_X_sub_C x) hdeg,
          degree_X_sub_C, add_comm];
        exact add_le_add (le_refl (1 : with_bot ℕ)) htd,
  begin
    assume a,
    conv_rhs { rw ← mul_div_by_monic_eq_iff_is_root.mpr hx },
    rw [root_multiplicity_mul (mul_ne_zero (X_sub_C_ne_zero x) hdiv0),
        root_multiplicity_X_sub_C, ← htr a],
    split_ifs with ha,
    { rw [ha, count_cons_self, nat.succ_eq_add_one, add_comm] },
    { rw [count_cons_of_ne ha, zero_add] },
  end⟩
else
  ⟨0, (degree_eq_nat_degree hp).symm ▸ with_bot.coe_le_coe.2 (nat.zero_le _),
    by { intro a, rw [count_zero, root_multiplicity_eq_zero (not_exists.mp h a)] }⟩
using_well_founded {dec_tac := tactic.assumption}

/-- `roots p` noncomputably gives a multiset containing all the roots of `p`,
including their multiplicities. -/
noncomputable def roots (p : R[X]) : multiset R :=
if h : p = 0 then ∅ else classical.some (exists_multiset_roots h)

@[simp] lemma roots_zero : (0 : R[X]).roots = 0 :=
dif_pos rfl

lemma card_roots (hp0 : p ≠ 0) : ((roots p).card : with_bot ℕ) ≤ degree p :=
begin
  unfold roots,
  rw dif_neg hp0,
  exact (classical.some_spec (exists_multiset_roots hp0)).1
end

lemma card_roots' (p : R[X]) : p.roots.card ≤ nat_degree p :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0], },
  exact with_bot.coe_le_coe.1 (le_trans (card_roots hp0) (le_of_eq $ degree_eq_nat_degree hp0))
end

lemma card_roots_sub_C {p : R[X]} {a : R} (hp0 : 0 < degree p) :
  ((p - C a).roots.card : with_bot ℕ) ≤ degree p :=
calc ((p - C a).roots.card : with_bot ℕ) ≤ degree (p - C a) :
  card_roots $ mt sub_eq_zero.1 $ λ h, not_le_of_gt hp0 $ h.symm ▸ degree_C_le
... = degree p : by rw [sub_eq_add_neg, ← C_neg]; exact degree_add_C hp0

lemma card_roots_sub_C' {p : R[X]} {a : R} (hp0 : 0 < degree p) :
  (p - C a).roots.card ≤ nat_degree p :=
with_bot.coe_le_coe.1 (le_trans (card_roots_sub_C hp0) (le_of_eq $ degree_eq_nat_degree
  (λ h, by simp [*, lt_irrefl] at *)))

@[simp] lemma count_roots (p : R[X]) : p.roots.count a = root_multiplicity a p :=
begin
  by_cases hp : p = 0,
  { simp [hp], },
  rw [roots, dif_neg hp],
  exact (classical.some_spec (exists_multiset_roots hp)).2 a
end

@[simp] lemma mem_roots' : a ∈ p.roots ↔ p ≠ 0 ∧ is_root p a :=
by rw [← count_pos, count_roots p, root_multiplicity_pos']

lemma mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ is_root p a := mem_roots'.trans $ and_iff_right hp

lemma ne_zero_of_mem_roots (h : a ∈ p.roots) : p ≠ 0 := (mem_roots'.1 h).1

lemma is_root_of_mem_roots (h : a ∈ p.roots) : is_root p a := (mem_roots'.1 h).2

theorem card_le_degree_of_subset_roots {p : R[X]} {Z : finset R} (h : Z.val ⊆ p.roots) :
  Z.card ≤ p.nat_degree :=
(multiset.card_le_of_le (finset.val_le_iff_val_subset.2 h)).trans (polynomial.card_roots' p)

lemma finite_set_of_is_root {p : R[X]} (hp : p ≠ 0) : set.finite {x | is_root p x} :=
by simpa only [← finset.set_of_mem, mem_to_finset, mem_roots hp]
  using p.roots.to_finset.finite_to_set

lemma eq_zero_of_infinite_is_root (p : R[X]) (h : set.infinite {x | is_root p x}) : p = 0 :=
not_imp_comm.mp finite_set_of_is_root h

lemma exists_max_root [linear_order R] (p : R[X]) (hp : p ≠ 0) :
  ∃ x₀, ∀ x, p.is_root x → x ≤ x₀ :=
set.exists_upper_bound_image _ _ $ finite_set_of_is_root hp

lemma exists_min_root [linear_order R] (p : R[X]) (hp : p ≠ 0) :
  ∃ x₀, ∀ x, p.is_root x → x₀ ≤ x :=
set.exists_lower_bound_image _ _ $ finite_set_of_is_root hp

lemma eq_of_infinite_eval_eq (p q : R[X]) (h : set.infinite {x | eval x p = eval x q}) : p = q :=
begin
  rw [← sub_eq_zero],
  apply eq_zero_of_infinite_is_root,
  simpa only [is_root, eval_sub, sub_eq_zero]
end

lemma roots_mul {p q : R[X]} (hpq : p * q ≠ 0) : (p * q).roots = p.roots + q.roots :=
multiset.ext.mpr $ λ r,
  by rw [count_add, count_roots, count_roots,
         count_roots, root_multiplicity_mul hpq]

lemma roots.le_of_dvd (h : q ≠ 0) : p ∣ q → roots p ≤ roots q :=
begin
  rintro ⟨k, rfl⟩,
  exact multiset.le_iff_exists_add.mpr ⟨k.roots, roots_mul h⟩
end

lemma mem_roots_sub_C' {p : R[X]} {a x : R} :
  x ∈ (p - C a).roots ↔ p ≠ C a ∧ p.eval x = a :=
by rw [mem_roots', is_root.def, sub_ne_zero, eval_sub, sub_eq_zero, eval_C]

lemma mem_roots_sub_C {p : R[X]} {a x : R} (hp0 : 0 < degree p) :
  x ∈ (p - C a).roots ↔ p.eval x = a :=
mem_roots_sub_C'.trans $ and_iff_right $ λ hp, hp0.not_le $ hp.symm ▸ degree_C_le

@[simp] lemma roots_X_sub_C (r : R) : roots (X - C r) = {r} :=
begin
  ext s,
  rw [count_roots, root_multiplicity_X_sub_C, count_singleton],
end

@[simp] lemma roots_X : roots (X : R[X]) = {0} := by rw [← roots_X_sub_C, C_0, sub_zero]

@[simp] lemma roots_C (x : R) : (C x).roots = 0 :=
if H : x = 0 then by rw [H, C_0, roots_zero] else multiset.ext.mpr $ λ r,
by rw [count_roots, count_zero, root_multiplicity_eq_zero (not_is_root_C _ _ H)]

@[simp] lemma roots_one : (1 : R[X]).roots = ∅ :=
roots_C 1

@[simp] lemma roots_C_mul (p : R[X]) (ha : a ≠ 0) : (C a * p).roots = p.roots :=
by by_cases hp : p = 0; simp only [roots_mul, *, ne.def, mul_eq_zero, C_eq_zero, or_self,
  not_false_iff, roots_C, zero_add, mul_zero]

@[simp] lemma roots_smul_nonzero (p : R[X]) (ha : a ≠ 0) : (a • p).roots = p.roots :=
by rw [smul_eq_C_mul, roots_C_mul _ ha]

lemma roots_list_prod (L : list R[X]) :
  ((0 : R[X]) ∉ L) → L.prod.roots = (L : multiset R[X]).bind roots :=
list.rec_on L (λ _, roots_one) $ λ hd tl ih H,
begin
  rw [list.mem_cons_iff, not_or_distrib] at H,
  rw [list.prod_cons, roots_mul (mul_ne_zero (ne.symm H.1) $ list.prod_ne_zero H.2),
      ← multiset.cons_coe, multiset.cons_bind, ih H.2]
end

lemma roots_multiset_prod (m : multiset R[X]) :
  (0 : R[X]) ∉ m → m.prod.roots = m.bind roots :=
by { rcases m with ⟨L⟩, simpa only [multiset.coe_prod, quot_mk_to_coe''] using roots_list_prod L }

lemma roots_prod {ι : Type*} (f : ι → R[X]) (s : finset ι) :
  s.prod f ≠ 0 → (s.prod f).roots = s.val.bind (λ i, roots (f i)) :=
begin
  rcases s with ⟨m, hm⟩,
  simpa [multiset.prod_eq_zero_iff, bind_map] using roots_multiset_prod (m.map f)
end

@[simp] lemma roots_pow (p : R[X]) (n : ℕ) : (p ^ n).roots = n • p.roots :=
begin
  induction n with n ihn,
  { rw [pow_zero, roots_one, zero_smul, empty_eq_zero] },
  { rcases eq_or_ne p 0 with rfl | hp,
    { rw [zero_pow n.succ_pos, roots_zero, smul_zero] },
    { rw [pow_succ', roots_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ihn, nat.succ_eq_add_one,
        add_smul, one_smul] } }
end

lemma roots_X_pow (n : ℕ) : (X ^ n : R[X]).roots = n • {0} := by rw [roots_pow, roots_X]

lemma roots_C_mul_X_pow (ha : a ≠ 0) (n : ℕ) : (C a * X ^ n).roots = n • {0} :=
by rw [roots_C_mul _ ha, roots_X_pow]

@[simp] lemma roots_monomial (ha : a ≠ 0) (n : ℕ) : (monomial n a).roots = n • {0} :=
by rw [← C_mul_X_pow_eq_monomial, roots_C_mul_X_pow ha]

lemma roots_prod_X_sub_C (s : finset R) :
  (s.prod (λ a, X - C a)).roots = s.val :=
(roots_prod (λ a, X - C a) s (prod_ne_zero_iff.mpr (λ a _, X_sub_C_ne_zero a))).trans
  (by simp_rw [roots_X_sub_C, multiset.bind_singleton, multiset.map_id'])

@[simp] lemma roots_multiset_prod_X_sub_C (s : multiset R) :
  (s.map (λ a, X - C a)).prod.roots = s :=
begin
  rw [roots_multiset_prod, multiset.bind_map],
  { simp_rw [roots_X_sub_C, multiset.bind_singleton, multiset.map_id'] },
  { rw [multiset.mem_map], rintro ⟨a, -, h⟩, exact X_sub_C_ne_zero a h },
end

@[simp] lemma nat_degree_multiset_prod_X_sub_C_eq_card (s : multiset R):
  (s.map (λ a, X - C a)).prod.nat_degree = s.card :=
begin
  rw [nat_degree_multiset_prod_of_monic, multiset.map_map],
  { simp only [(∘), nat_degree_X_sub_C, multiset.map_const, multiset.sum_replicate, smul_eq_mul,
      mul_one] },
  { exact multiset.forall_mem_map_iff.2 (λ a _, monic_X_sub_C a) },
end

lemma card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
  (roots ((X : R[X]) ^ n - C a)).card ≤ n :=
with_bot.coe_le_coe.1 $
calc ((roots ((X : R[X]) ^ n - C a)).card : with_bot ℕ)
      ≤ degree ((X : R[X]) ^ n - C a) : card_roots (X_pow_sub_C_ne_zero hn a)
  ... = n : degree_X_pow_sub_C hn a

section nth_roots

/-- `nth_roots n a` noncomputably returns the solutions to `x ^ n = a`-/
def nth_roots (n : ℕ) (a : R) : multiset R :=
roots ((X : R[X]) ^ n - C a)

@[simp] lemma mem_nth_roots {n : ℕ} (hn : 0 < n) {a x : R} :
  x ∈ nth_roots n a ↔ x ^ n = a :=
by rw [nth_roots, mem_roots (X_pow_sub_C_ne_zero hn a),
  is_root.def, eval_sub, eval_C, eval_pow, eval_X, sub_eq_zero]

@[simp] lemma nth_roots_zero (r : R) : nth_roots 0 r = 0 :=
by simp only [empty_eq_zero, pow_zero, nth_roots, ← C_1, ← C_sub, roots_C]

lemma card_nth_roots (n : ℕ) (a : R) :
  (nth_roots n a).card ≤ n :=
if hn : n = 0
then if h : (X : R[X]) ^ n - C a = 0
  then by simp only [nat.zero_le, nth_roots, roots, h, dif_pos rfl, empty_eq_zero, card_zero]
  else with_bot.coe_le_coe.1 (le_trans (card_roots h)
   (by { rw [hn, pow_zero, ← C_1, ← ring_hom.map_sub ],
         exact degree_C_le }))
else by rw [← with_bot.coe_le_coe, ← degree_X_pow_sub_C (nat.pos_of_ne_zero hn) a];
  exact card_roots (X_pow_sub_C_ne_zero (nat.pos_of_ne_zero hn) a)

@[simp]
lemma nth_roots_two_eq_zero_iff {r : R} : nth_roots 2 r = 0 ↔ ¬ is_square r :=
by simp_rw [is_square_iff_exists_sq, eq_zero_iff_forall_not_mem,
            mem_nth_roots (by norm_num : 0 < 2), ← not_exists, eq_comm]

/-- The multiset `nth_roots ↑n (1 : R)` as a finset. -/
def nth_roots_finset (n : ℕ) (R : Type*) [comm_ring R] [is_domain R] : finset R :=
multiset.to_finset (nth_roots n (1 : R))

@[simp] lemma mem_nth_roots_finset {n : ℕ} (h : 0 < n) {x : R} :
  x ∈ nth_roots_finset n R ↔ x ^ (n : ℕ) = 1 :=
by rw [nth_roots_finset, mem_to_finset, mem_nth_roots h]

@[simp] lemma nth_roots_finset_zero : nth_roots_finset 0 R = ∅ := by simp [nth_roots_finset]

end nth_roots

lemma monic.comp (hp : p.monic) (hq : q.monic) (h : q.nat_degree ≠ 0) : (p.comp q).monic :=
by rw [monic.def, leading_coeff_comp h, monic.def.1 hp, monic.def.1 hq, one_pow, one_mul]

lemma monic.comp_X_add_C (hp : p.monic) (r : R) : (p.comp (X + C r)).monic :=
begin
  refine hp.comp (monic_X_add_C _) (λ ha, _),
  rw [nat_degree_X_add_C] at ha,
  exact one_ne_zero ha
end

lemma monic.comp_X_sub_C (hp : p.monic) (r : R) : (p.comp (X - C r)).monic :=
by simpa using hp.comp_X_add_C (-r)

lemma units_coeff_zero_smul (c : R[X]ˣ) (p : R[X]) :
  (c : R[X]).coeff 0 • p = c * p :=
by rw [←polynomial.C_mul', ←polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]

@[simp] lemma nat_degree_coe_units (u : R[X]ˣ) :
  nat_degree (u : R[X]) = 0 :=
nat_degree_eq_of_degree_eq_some (degree_coe_units u)

lemma comp_eq_zero_iff :
  p.comp q = 0 ↔ p = 0 ∨ (p.eval (q.coeff 0) = 0 ∧ q = C (q.coeff 0)) :=
begin
  split,
  { intro h,
    have key : p.nat_degree = 0 ∨ q.nat_degree = 0,
    { rw [←mul_eq_zero, ←nat_degree_comp, h, nat_degree_zero] },
    replace key := or.imp eq_C_of_nat_degree_eq_zero eq_C_of_nat_degree_eq_zero key,
    cases key,
    { rw [key, C_comp] at h,
      exact or.inl (key.trans h) },
    { rw [key, comp_C, C_eq_zero] at h,
      exact or.inr ⟨h, key⟩ }, },
  { exact λ h, or.rec (λ h, by rw [h, zero_comp]) (λ h, by rw [h.2, comp_C, h.1, C_0]) h },
end

lemma zero_of_eval_zero [infinite R] (p : R[X]) (h : ∀ x, p.eval x = 0) : p = 0 :=
by classical; by_contradiction hp; exact
fintype.false ⟨p.roots.to_finset, λ x, multiset.mem_to_finset.mpr ((mem_roots hp).mpr (h _))⟩

lemma funext [infinite R] {p q : R[X]} (ext : ∀ r : R, p.eval r = q.eval r) : p = q :=
begin
  rw ← sub_eq_zero,
  apply zero_of_eval_zero,
  intro x,
  rw [eval_sub, sub_eq_zero, ext],
end

variables [comm_ring T]

/-- The set of distinct roots of `p` in `E`.

If you have a non-separable polynomial, use `polynomial.roots` for the multiset
where multiple roots have the appropriate multiplicity. -/
def root_set (p : T[X]) (S) [comm_ring S] [is_domain S] [algebra T S] : set S :=
(p.map (algebra_map T S)).roots.to_finset

lemma root_set_def (p : T[X]) (S) [comm_ring S] [is_domain S] [algebra T S] :
  p.root_set S = (p.map (algebra_map T S)).roots.to_finset :=
rfl

@[simp] lemma root_set_C [comm_ring S] [is_domain S] [algebra T S] (a : T) :
  (C a).root_set S = ∅ :=
by rw [root_set_def, map_C, roots_C, multiset.to_finset_zero, finset.coe_empty]

@[simp] lemma root_set_zero (S) [comm_ring S] [is_domain S] [algebra T S] :
  (0 : T[X]).root_set S = ∅ :=
by rw [← C_0, root_set_C]

instance root_set_fintype (p : T[X])
  (S : Type*) [comm_ring S] [is_domain S] [algebra T S] : fintype (p.root_set S) :=
finset_coe.fintype _

lemma root_set_finite (p : T[X])
  (S : Type*) [comm_ring S] [is_domain S] [algebra T S] : (p.root_set S).finite :=
set.to_finite _

/-- The set of roots of all polynomials of bounded degree and having coefficients in a finite set
is finite. -/
lemma bUnion_roots_finite {R S : Type*} [semiring R] [comm_ring S] [is_domain S]
  (m : R →+* S) (d : ℕ) {U : set R} (h : U.finite) :
  (⋃ (f : R[X]) (hf : f.nat_degree ≤ d ∧ ∀ i, (f.coeff i) ∈ U),
    ((f.map m).roots.to_finset : set S)).finite :=
set.finite.bUnion begin
  -- We prove that the set of polynomials under consideration is finite because its
  -- image by the injective map `π` is finite
  let π : R[X] → fin (d+1) → R := λ f i, f.coeff i,
  refine ((set.finite.pi $ λ e, h).subset $ _).of_finite_image (_ : set.inj_on π _),
  { exact set.image_subset_iff.2 (λ f hf i _, hf.2 i) },
  { refine λ x hx y hy hxy, (ext_iff_nat_degree_le hx.1 hy.1).2 (λ i hi, _),
    exact id congr_fun hxy ⟨i, nat.lt_succ_of_le hi⟩ },
end $ λ i hi, finset.finite_to_set _

theorem mem_root_set' {p : T[X]} {S : Type*} [comm_ring S] [is_domain S] [algebra T S] {a : S} :
  a ∈ p.root_set S ↔ p.map (algebra_map T S) ≠ 0 ∧ aeval a p = 0 :=
by rw [root_set, finset.mem_coe, mem_to_finset, mem_roots', is_root.def, ← eval₂_eq_eval_map,
  aeval_def]

theorem mem_root_set {p : T[X]} {S : Type*} [comm_ring S] [is_domain S] [algebra T S]
  [no_zero_smul_divisors T S] {a : S} : a ∈ p.root_set S ↔ p ≠ 0 ∧ aeval a p = 0 :=
by rw [mem_root_set', (map_injective _
  (no_zero_smul_divisors.algebra_map_injective T S)).ne_iff' (polynomial.map_zero _)]

theorem mem_root_set_of_ne {p : T[X]} {S : Type*} [comm_ring S] [is_domain S] [algebra T S]
  [no_zero_smul_divisors T S] (hp : p ≠ 0) {a : S} : a ∈ p.root_set S ↔ aeval a p = 0 :=
mem_root_set.trans $ and_iff_right hp

lemma root_set_maps_to' {p : T[X]} {S S'} [comm_ring S] [is_domain S] [algebra T S]
  [comm_ring S'] [is_domain S'] [algebra T S']
  (hp : p.map (algebra_map T S') = 0 → p.map (algebra_map T S) = 0)
  (f : S →ₐ[T] S') : (p.root_set S).maps_to f (p.root_set S') :=
λ x hx, begin
  rw [mem_root_set'] at hx ⊢,
  rw [aeval_alg_hom, alg_hom.comp_apply, hx.2, _root_.map_zero],
  exact ⟨mt hp hx.1, rfl⟩
end

lemma ne_zero_of_mem_root_set {p : T[X]} [comm_ring S] [is_domain S] [algebra T S] {a : S}
  (h : a ∈ p.root_set S) : p ≠ 0 :=
λ hf, by rwa [hf, root_set_zero] at h

lemma aeval_eq_zero_of_mem_root_set {p : T[X]} [comm_ring S] [is_domain S] [algebra T S]
  {a : S} (hx : a ∈ p.root_set S) : aeval a p = 0 :=
(mem_root_set'.1 hx).2

lemma root_set_maps_to {p : T[X]} {S S'} [comm_ring S] [is_domain S] [algebra T S]
  [comm_ring S'] [is_domain S'] [algebra T S'] [no_zero_smul_divisors T S'] (f : S →ₐ[T] S') :
  (p.root_set S).maps_to f (p.root_set S') :=
begin
  refine root_set_maps_to' (λ h₀, _) f,
  obtain rfl : p = 0 := map_injective _
    (no_zero_smul_divisors.algebra_map_injective T S') (by rwa [polynomial.map_zero]),
  exact polynomial.map_zero _
end

end roots

lemma coeff_coe_units_zero_ne_zero (u : R[X]ˣ) :
  coeff (u : R[X]) 0 ≠ 0 :=
begin
  conv in (0) { rw [← nat_degree_coe_units u] },
  rw [← leading_coeff, ne.def, leading_coeff_eq_zero],
  exact units.ne_zero _
end

lemma degree_eq_degree_of_associated (h : associated p q) : degree p = degree q :=
let ⟨u, hu⟩ := h in by simp [hu.symm]

lemma degree_eq_one_of_irreducible_of_root (hi : irreducible p) {x : R} (hx : is_root p x) :
  degree p = 1 :=
let ⟨g, hg⟩ := dvd_iff_is_root.2 hx in
have is_unit (X - C x) ∨ is_unit g, from hi.is_unit_or_is_unit hg,
this.elim
  (λ h, have h₁ : degree (X - C x) = 1, from degree_X_sub_C x,
    have h₂ : degree (X - C x) = 0, from degree_eq_zero_of_is_unit h,
    by rw h₁ at h₂; exact absurd h₂ dec_trivial)
  (λ hgu, by rw [hg, degree_mul, degree_X_sub_C, degree_eq_zero_of_is_unit hgu, add_zero])

/-- Division by a monic polynomial doesn't change the leading coefficient. -/
lemma leading_coeff_div_by_monic_of_monic {R : Type u} [comm_ring R]
  {p q : R[X]} (hmonic : q.monic) (hdegree : q.degree ≤ p.degree) :
  (p /ₘ q).leading_coeff = p.leading_coeff :=
begin
  nontriviality,
  have h : q.leading_coeff * (p /ₘ q).leading_coeff ≠ 0,
  { simpa [div_by_monic_eq_zero_iff hmonic, hmonic.leading_coeff, nat.with_bot.one_le_iff_zero_lt]
      using hdegree },
  nth_rewrite_rhs 0 ←mod_by_monic_add_div p hmonic,
  rw [leading_coeff_add_of_degree_lt, leading_coeff_monic_mul hmonic],
  rw [degree_mul' h, degree_add_div_by_monic hmonic hdegree],
  exact (degree_mod_by_monic_lt p hmonic).trans_le hdegree
end

lemma leading_coeff_div_by_monic_X_sub_C (p : R[X]) (hp : degree p ≠ 0) (a : R) :
  leading_coeff (p /ₘ (X - C a)) = leading_coeff p :=
begin
  nontriviality,
  cases hp.lt_or_lt with hd hd,
  { rw [degree_eq_bot.mp $ (nat.with_bot.lt_zero_iff _).mp hd, zero_div_by_monic] },
  refine leading_coeff_div_by_monic_of_monic (monic_X_sub_C a) _,
  rwa [degree_X_sub_C, nat.with_bot.one_le_iff_zero_lt]
end

lemma eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le {R} [comm_ring R]
  {p q : R[X]} (hp : p.monic) (hdiv : p ∣ q)
  (hdeg : q.nat_degree ≤ p.nat_degree) : q = C q.leading_coeff * p :=
begin
  obtain ⟨r, hr⟩ := hdiv,
  obtain (rfl|hq) := eq_or_ne q 0, {simp},
  have rzero : r ≠ 0 := λ h, by simpa [h, hq] using hr,
  rw [hr, nat_degree_mul'] at hdeg, swap,
  { rw [hp.leading_coeff, one_mul, leading_coeff_ne_zero], exact rzero },
  rw [mul_comm, @eq_C_of_nat_degree_eq_zero _ _ r] at hr,
  { convert hr, convert leading_coeff_C _ using 1, rw [hr, leading_coeff_mul_monic hp] },
  { exact (add_right_inj _).1 (le_antisymm hdeg $ nat.le.intro rfl) },
end

lemma eq_of_monic_of_dvd_of_nat_degree_le {R} [comm_ring R]
  {p q : R[X]} (hp : p.monic) (hq : q.monic) (hdiv : p ∣ q)
  (hdeg : q.nat_degree ≤ p.nat_degree) : q = p :=
begin
  convert eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le hp hdiv hdeg,
  rw [hq.leading_coeff, C_1, one_mul],
end

lemma is_coprime_X_sub_C_of_is_unit_sub {R} [comm_ring R] {a b : R}
  (h : is_unit (a - b)) : is_coprime (X - C a) (X - C b) :=
⟨-C h.unit⁻¹.val, C h.unit⁻¹.val, by { rw [neg_mul_comm, ← left_distrib, neg_add_eq_sub,
  sub_sub_sub_cancel_left, ← C_sub, ← C_mul], convert C_1, exact h.coe_inv_mul }⟩

theorem pairwise_coprime_X_sub_C {K} [field K] {I : Type v} {s : I → K}
  (H : function.injective s) : pairwise (is_coprime on (λ i : I, X - C (s i))) :=
λ i j hij, is_coprime_X_sub_C_of_is_unit_sub (sub_ne_zero_of_ne $ H.ne hij).is_unit

lemma monic_prod_multiset_X_sub_C : monic (p.roots.map (λ a, X - C a)).prod :=
monic_multiset_prod_of_monic _ _ (λ a _, monic_X_sub_C a)

lemma prod_multiset_root_eq_finset_root :
  (p.roots.map (λ a, X - C a)).prod =
  p.roots.to_finset.prod (λ a, (X - C a) ^ root_multiplicity a p) :=
by simp only [count_roots, finset.prod_multiset_map_count]

/-- The product `∏ (X - a)` for `a` inside the multiset `p.roots` divides `p`. -/
lemma prod_multiset_X_sub_C_dvd (p : R[X]) : (p.roots.map (λ a, X - C a)).prod ∣ p :=
begin
  rw ← map_dvd_map _ (is_fraction_ring.injective R $ fraction_ring R) monic_prod_multiset_X_sub_C,
  rw [prod_multiset_root_eq_finset_root, polynomial.map_prod],
  refine finset.prod_dvd_of_coprime (λ a _ b _ h, _) (λ a _, _),
  { simp_rw [polynomial.map_pow, polynomial.map_sub, map_C, map_X],
    exact (pairwise_coprime_X_sub_C (is_fraction_ring.injective R $ fraction_ring R) h).pow },
  { exact polynomial.map_dvd _ (pow_root_multiplicity_dvd p a) },
end

/-- A Galois connection. -/
lemma _root_.multiset.prod_X_sub_C_dvd_iff_le_roots {p : R[X]} (hp : p ≠ 0) (s : multiset R) :
  (s.map (λ a, X - C a)).prod ∣ p ↔ s ≤ p.roots :=
⟨λ h, multiset.le_iff_count.2 $ λ r, begin
  rw [count_roots, le_root_multiplicity_iff hp, ← multiset.prod_replicate,
    ← multiset.map_replicate (λ a, X - C a), ← multiset.filter_eq],
  exact (multiset.prod_dvd_prod_of_le $ multiset.map_le_map $ s.filter_le _).trans h,
end, λ h, (multiset.prod_dvd_prod_of_le $ multiset.map_le_map h).trans p.prod_multiset_X_sub_C_dvd⟩

lemma exists_prod_multiset_X_sub_C_mul (p : R[X]) : ∃ q,
  (p.roots.map (λ a, X - C a)).prod * q = p ∧
  p.roots.card + q.nat_degree = p.nat_degree ∧
  q.roots = 0 :=
begin
  obtain ⟨q, he⟩ := p.prod_multiset_X_sub_C_dvd,
  use [q, he.symm],
  obtain (rfl|hq) := eq_or_ne q 0,
  { rw mul_zero at he, subst he, simp },
  split,
  { conv_rhs { rw he },
    rw [monic_prod_multiset_X_sub_C.nat_degree_mul' hq, nat_degree_multiset_prod_X_sub_C_eq_card] },
  { replace he := congr_arg roots he.symm,
    rw [roots_mul, roots_multiset_prod_X_sub_C] at he,
    exacts [add_right_eq_self.1 he, mul_ne_zero monic_prod_multiset_X_sub_C.ne_zero hq] },
end

/-- A polynomial `p` that has as many roots as its degree
can be written `p = p.leading_coeff * ∏(X - a)`, for `a` in `p.roots`. -/
lemma C_leading_coeff_mul_prod_multiset_X_sub_C (hroots : p.roots.card = p.nat_degree) :
  C p.leading_coeff * (p.roots.map (λ a, X - C a)).prod = p :=
(eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le monic_prod_multiset_X_sub_C
  p.prod_multiset_X_sub_C_dvd ((nat_degree_multiset_prod_X_sub_C_eq_card _).trans hroots).ge).symm

/-- A monic polynomial `p` that has as many roots as its degree
can be written `p = ∏(X - a)`, for `a` in `p.roots`. -/
lemma prod_multiset_X_sub_C_of_monic_of_roots_card_eq
  (hp : p.monic) (hroots : p.roots.card = p.nat_degree) :
  (p.roots.map (λ a, X - C a)).prod = p :=
by { convert C_leading_coeff_mul_prod_multiset_X_sub_C hroots, rw [hp.leading_coeff, C_1, one_mul] }

end comm_ring

section
variables {A B : Type*} [comm_ring A] [comm_ring B]

lemma le_root_multiplicity_map {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0) (a : A) :
  root_multiplicity a p ≤ root_multiplicity (f a) (p.map f) :=
begin
  rw [le_root_multiplicity_iff hmap],
  refine trans _ ((map_ring_hom f).map_dvd (pow_root_multiplicity_dvd p a)),
  rw [map_pow, map_sub, coe_map_ring_hom, map_X, map_C],
end

lemma eq_root_multiplicity_map {p : A[X]} {f : A →+* B} (hf : function.injective f)
  (a : A) : root_multiplicity a p = root_multiplicity (f a) (p.map f) :=
begin
  by_cases hp0 : p = 0, { simp only [hp0, root_multiplicity_zero, polynomial.map_zero], },
  apply le_antisymm (le_root_multiplicity_map ((polynomial.map_ne_zero_iff hf).mpr hp0) a),
  rw [le_root_multiplicity_iff hp0, ← map_dvd_map f hf ((monic_X_sub_C a).pow _),
    polynomial.map_pow, polynomial.map_sub, map_X, map_C],
  apply pow_root_multiplicity_dvd,
end

lemma count_map_roots [is_domain A] {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0) (b : B) :
  (p.roots.map f).count b ≤ root_multiplicity b (p.map f) :=
begin
  rw [le_root_multiplicity_iff hmap, ← multiset.prod_replicate,
    ← multiset.map_replicate (λ a, X - C a)],
  rw ← multiset.filter_eq,
  refine (multiset.prod_dvd_prod_of_le $ multiset.map_le_map $ multiset.filter_le _ _).trans _,
  convert polynomial.map_dvd _ p.prod_multiset_X_sub_C_dvd,
  simp only [polynomial.map_multiset_prod, multiset.map_map],
  congr, ext1,
  simp only [function.comp_app, polynomial.map_sub, map_X, map_C],
end

lemma count_map_roots_of_injective [is_domain A] (p : A[X]) {f : A →+* B}
  (hf : function.injective f) (b : B) :
  (p.roots.map f).count b ≤ root_multiplicity b (p.map f) :=
begin
  by_cases hp0 : p = 0,
  { simp only [hp0, roots_zero, multiset.map_zero,
      multiset.count_zero, polynomial.map_zero, root_multiplicity_zero] },
  { exact count_map_roots ((polynomial.map_ne_zero_iff hf).mpr hp0) b },
end

lemma map_roots_le [is_domain A] [is_domain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0) :
  p.roots.map f ≤ (p.map f).roots :=
multiset.le_iff_count.2 $ λ b, by { rw count_roots, apply count_map_roots h }

lemma map_roots_le_of_injective [is_domain A] [is_domain B] (p : A[X])
  {f : A →+* B} (hf : function.injective f) :
  p.roots.map f ≤ (p.map f).roots :=
begin
  by_cases hp0 : p = 0, { simp only [hp0, roots_zero, multiset.map_zero, polynomial.map_zero], },
  exact map_roots_le ((polynomial.map_ne_zero_iff hf).mpr hp0),
end

lemma card_roots_le_map [is_domain A] [is_domain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0) :
  p.roots.card ≤ (p.map f).roots.card :=
by { rw ← p.roots.card_map f, exact multiset.card_le_of_le (map_roots_le h) }

lemma card_roots_le_map_of_injective [is_domain A] [is_domain B] {p : A[X]} {f : A →+* B}
  (hf : function.injective f) : p.roots.card ≤ (p.map f).roots.card :=
begin
  by_cases hp0 : p = 0, { simp only [hp0, roots_zero, polynomial.map_zero, multiset.card_zero], },
  exact card_roots_le_map ((polynomial.map_ne_zero_iff hf).mpr hp0),
end

lemma roots_map_of_injective_of_card_eq_nat_degree [is_domain A] [is_domain B] {p : A[X]}
  {f : A →+* B} (hf : function.injective f) (hroots : p.roots.card = p.nat_degree) :
  p.roots.map f = (p.map f).roots :=
begin
  apply multiset.eq_of_le_of_card_le (map_roots_le_of_injective p hf),
  simpa only [multiset.card_map, hroots] using (card_roots' _).trans (nat_degree_map_le f p),
end

end

section

variables [semiring R] [comm_ring S] [is_domain S] (φ : R →+* S)

lemma is_unit_of_is_unit_leading_coeff_of_is_unit_map
  {f : R[X]} (hf : is_unit f.leading_coeff) (H : is_unit (map φ f)) :
  is_unit f :=
begin
  have dz := degree_eq_zero_of_is_unit H,
  rw degree_map_eq_of_leading_coeff_ne_zero at dz,
  { rw eq_C_of_degree_eq_zero dz,
    refine is_unit.map C _,
    convert hf,
    rw (degree_eq_iff_nat_degree_eq _).1 dz,
    rintro rfl,
    simpa using H, },
  { intro h,
    have u : is_unit (φ f.leading_coeff) := is_unit.map φ hf,
    rw h at u,
    simpa using u, }
end

end

section
variables [comm_ring R] [is_domain R] [comm_ring S] [is_domain S] (φ : R →+* S)
/--
A polynomial over an integral domain `R` is irreducible if it is monic and
  irreducible after mapping into an integral domain `S`.

A special case of this lemma is that a polynomial over `ℤ` is irreducible if
  it is monic and irreducible over `ℤ/pℤ` for some prime `p`.
-/
lemma monic.irreducible_of_irreducible_map (f : R[X])
  (h_mon : monic f) (h_irr : irreducible (map φ f)) :
  irreducible f :=
begin
  refine ⟨h_irr.not_unit ∘ is_unit.map (map_ring_hom φ), λ a b h, _⟩,
  dsimp [monic] at h_mon,
  have q := (leading_coeff_mul a b).symm,
  rw [←h, h_mon] at q,
  refine (h_irr.is_unit_or_is_unit $ (congr_arg (map φ) h).trans (polynomial.map_mul φ)).imp _ _;
    apply is_unit_of_is_unit_leading_coeff_of_is_unit_map;
    apply is_unit_of_mul_eq_one,
  { exact q }, { rw mul_comm, exact q },
end

end

end polynomial
