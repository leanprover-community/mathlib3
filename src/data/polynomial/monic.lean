/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.reverse
import algebra.regular.smul

/-!
# Theory of monic polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We give several tools for proving that polynomials are monic, e.g.
`monic.mul`, `monic.map`, `monic.pow`.
-/

noncomputable theory

open finset
open_locale big_operators classical polynomial

namespace polynomial
universes u v y
variables {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

section semiring
variables [semiring R] {p q r : R[X]}

lemma monic_zero_iff_subsingleton : monic (0 : R[X]) ↔ subsingleton R :=
subsingleton_iff_zero_eq_one

lemma not_monic_zero_iff : ¬ monic (0 : R[X]) ↔ (0 : R) ≠ 1 :=
(monic_zero_iff_subsingleton.trans subsingleton_iff_zero_eq_one.symm).not

lemma monic_zero_iff_subsingleton' :
  monic (0 : R[X]) ↔ (∀ f g : R[X], f = g) ∧ (∀ a b : R, a = b) :=
polynomial.monic_zero_iff_subsingleton.trans ⟨by { introI, simp },
  λ h, subsingleton_iff.mpr h.2⟩

lemma monic.as_sum (hp : p.monic) :
  p = X^(p.nat_degree) + (∑ i in range p.nat_degree, C (p.coeff i) * X^i) :=
begin
  conv_lhs { rw [p.as_sum_range_C_mul_X_pow, sum_range_succ_comm] },
  suffices : C (p.coeff p.nat_degree) = 1,
  { rw [this, one_mul] },
  exact congr_arg C hp
end

lemma ne_zero_of_ne_zero_of_monic (hp : p ≠ 0) (hq : monic q) : q ≠ 0 :=
begin
  rintro rfl,
  rw [monic.def, leading_coeff_zero] at hq,
  rw [← mul_one p, ← C_1, ← hq, C_0, mul_zero] at hp,
  exact hp rfl
end

lemma monic.map [semiring S] (f : R →+* S) (hp : monic p) : monic (p.map f) :=
begin
  nontriviality,
  have : f (leading_coeff p) ≠ 0,
  { rw [show _ = _, from hp, f.map_one],
    exact one_ne_zero, },
  rw [monic, leading_coeff, coeff_map],
  suffices : p.coeff (map f p).nat_degree = 1,
  { simp [this], },
  rwa nat_degree_eq_of_degree_eq (degree_map_eq_of_leading_coeff_ne_zero f this),
end

lemma monic_C_mul_of_mul_leading_coeff_eq_one {b : R} (hp : b * p.leading_coeff = 1) :
  monic (C b * p) :=
by { nontriviality, rw [monic, leading_coeff_mul' _]; simp [leading_coeff_C b, hp] }

lemma monic_mul_C_of_leading_coeff_mul_eq_one {b : R} (hp : p.leading_coeff * b = 1) :
  monic (p * C b) :=
by { nontriviality, rw [monic, leading_coeff_mul' _]; simp [leading_coeff_C b, hp] }

theorem monic_of_degree_le (n : ℕ) (H1 : degree p ≤ n) (H2 : coeff p n = 1) : monic p :=
decidable.by_cases
  (assume H : degree p < n, eq_of_zero_eq_one
    (H2 ▸ (coeff_eq_zero_of_degree_lt H).symm) _ _)
  (assume H : ¬degree p < n,
    by rwa [monic, leading_coeff, nat_degree, (lt_or_eq_of_le H1).resolve_left H])

theorem monic_X_pow_add {n : ℕ} (H : degree p ≤ n) : monic (X ^ (n+1) + p) :=
have H1 : degree p < n+1, from lt_of_le_of_lt H (with_bot.coe_lt_coe.2 (nat.lt_succ_self n)),
monic_of_degree_le (n+1)
  (le_trans (degree_add_le _ _) (max_le (degree_X_pow_le _) (le_of_lt H1)))
  (by rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H1, add_zero])

theorem monic_X_add_C (x : R) : monic (X + C x) :=
pow_one (X : R[X]) ▸ monic_X_pow_add degree_C_le

lemma monic.mul (hp : monic p) (hq : monic q) : monic (p * q) :=
if h0 : (0 : R) = 1 then by haveI := subsingleton_of_zero_eq_one h0;
  exact subsingleton.elim _ _
else
  have leading_coeff p * leading_coeff q ≠ 0, by simp [monic.def.1 hp, monic.def.1 hq, ne.symm h0],
  by rw [monic.def, leading_coeff_mul' this, monic.def.1 hp, monic.def.1 hq, one_mul]

lemma monic.pow (hp : monic p) : ∀ (n : ℕ), monic (p ^ n)
| 0     := monic_one
| (n+1) := by { rw pow_succ, exact hp.mul (monic.pow n) }

lemma monic.add_of_left (hp : monic p) (hpq : degree q < degree p) :
  monic (p + q) :=
by rwa [monic, add_comm, leading_coeff_add_of_degree_lt hpq]

lemma monic.add_of_right (hq : monic q) (hpq : degree p < degree q) :
  monic (p + q) :=
by rwa [monic, leading_coeff_add_of_degree_lt hpq]

lemma monic.of_mul_monic_left (hp : p.monic) (hpq : (p * q).monic) : q.monic :=
begin
  contrapose! hpq,
  rw monic.def at hpq ⊢,
  rwa leading_coeff_monic_mul hp,
end

lemma monic.of_mul_monic_right (hq : q.monic) (hpq : (p * q).monic) : p.monic :=
begin
  contrapose! hpq,
  rw monic.def at hpq ⊢,
  rwa leading_coeff_mul_monic hq,
end

namespace monic

@[simp]
lemma nat_degree_eq_zero_iff_eq_one (hp : p.monic) :
  p.nat_degree = 0 ↔ p = 1 :=
begin
  split; intro h,
  swap, { rw h, exact nat_degree_one },
  have : p = C (p.coeff 0),
  { rw ← polynomial.degree_le_zero_iff,
    rwa polynomial.nat_degree_eq_zero_iff_degree_le_zero at h },
  rw this, convert C_1, rw ← h, apply hp,
end

@[simp]
lemma degree_le_zero_iff_eq_one (hp : p.monic) :
  p.degree ≤ 0 ↔ p = 1 :=
by rw [←hp.nat_degree_eq_zero_iff_eq_one, nat_degree_eq_zero_iff_degree_le_zero]

lemma nat_degree_mul (hp : p.monic) (hq : q.monic) :
  (p * q).nat_degree = p.nat_degree + q.nat_degree :=
begin
  nontriviality R,
  apply nat_degree_mul',
  simp [hp.leading_coeff, hq.leading_coeff]
end

lemma degree_mul_comm (hp : p.monic) (q : R[X]) :
  (p * q).degree = (q * p).degree :=
begin
  by_cases h : q = 0,
  { simp [h] },
  rw [degree_mul', hp.degree_mul],
  { exact add_comm _ _ },
  { rwa [hp.leading_coeff, one_mul, leading_coeff_ne_zero] }
end

lemma nat_degree_mul' (hp : p.monic) (hq : q ≠ 0) :
  (p * q).nat_degree = p.nat_degree + q.nat_degree :=
begin
  rw [nat_degree_mul', add_comm],
  simpa [hp.leading_coeff, leading_coeff_ne_zero]
end

lemma nat_degree_mul_comm (hp : p.monic) (q : R[X]) :
  (p * q).nat_degree = (q * p).nat_degree :=
begin
  by_cases h : q = 0,
  { simp [h] },
  rw [hp.nat_degree_mul' h, polynomial.nat_degree_mul', add_comm],
  simpa [hp.leading_coeff, leading_coeff_ne_zero]
end

lemma not_dvd_of_nat_degree_lt (hp : monic p)
  (h0 : q ≠ 0) (hl : nat_degree q < nat_degree p) : ¬ p ∣ q :=
begin
  rintro ⟨r, rfl⟩,
  rw [hp.nat_degree_mul' $ right_ne_zero_of_mul h0] at hl,
  exact hl.not_le (nat.le_add_right _ _)
end

lemma not_dvd_of_degree_lt (hp : monic p)
  (h0 : q ≠ 0) (hl : degree q < degree p) : ¬ p ∣ q :=
monic.not_dvd_of_nat_degree_lt hp h0 $ nat_degree_lt_nat_degree h0 hl

lemma next_coeff_mul (hp : monic p) (hq : monic q) :
  next_coeff (p * q) = next_coeff p + next_coeff q :=
begin
  nontriviality,
  simp only [← coeff_one_reverse],
  rw reverse_mul;
    simp [coeff_mul, nat.antidiagonal, hp.leading_coeff, hq.leading_coeff, add_comm]
end

lemma eq_one_of_map_eq_one {S : Type*} [semiring S] [nontrivial S]
  (f : R →+* S) (hp : p.monic) (map_eq : p.map f = 1) : p = 1 :=
begin
  nontriviality R,
  have hdeg : p.degree = 0,
  { rw [← degree_map_eq_of_leading_coeff_ne_zero f _, map_eq, degree_one],
    { rw [hp.leading_coeff, f.map_one],
      exact one_ne_zero } },
  have hndeg : p.nat_degree = 0 :=
    with_bot.coe_eq_coe.mp ((degree_eq_nat_degree hp.ne_zero).symm.trans hdeg),
  convert eq_C_of_degree_eq_zero hdeg,
  rw [← hndeg, ← polynomial.leading_coeff, hp.leading_coeff, C.map_one]
end

lemma nat_degree_pow (hp : p.monic) (n : ℕ) :
  (p ^ n).nat_degree = n * p.nat_degree :=
begin
  induction n with n hn,
  { simp },
  { rw [pow_succ, hp.nat_degree_mul (hp.pow n), hn],
    ring }
end

end monic

@[simp] lemma nat_degree_pow_X_add_C [nontrivial R] (n : ℕ) (r : R) :
  ((X + C r) ^ n).nat_degree = n :=
by rw [(monic_X_add_C r).nat_degree_pow, nat_degree_X_add_C, mul_one]

lemma monic.eq_one_of_is_unit (hm : monic p) (hpu : is_unit p) : p = 1 :=
begin
  nontriviality R,
  obtain ⟨q, h⟩ := hpu.exists_right_inv,
  have := hm.nat_degree_mul' (right_ne_zero_of_mul_eq_one h),
  rw [h, nat_degree_one, eq_comm, add_eq_zero_iff] at this,
  exact hm.nat_degree_eq_zero_iff_eq_one.mp this.1,
end

lemma monic.is_unit_iff (hm : p.monic) : is_unit p ↔ p = 1 :=
⟨hm.eq_one_of_is_unit, λ h, h.symm ▸ is_unit_one⟩

end semiring

section comm_semiring
variables [comm_semiring R] {p : R[X]}

lemma monic_multiset_prod_of_monic (t : multiset ι) (f : ι → R[X])
  (ht : ∀ i ∈ t, monic (f i)) :
  monic (t.map f).prod :=
begin
  revert ht,
  refine t.induction_on _ _, { simp },
  intros a t ih ht,
  rw [multiset.map_cons, multiset.prod_cons],
  exact (ht _ (multiset.mem_cons_self _ _)).mul (ih (λ _ hi, ht _ (multiset.mem_cons_of_mem hi)))
end

lemma monic_prod_of_monic (s : finset ι) (f : ι → R[X]) (hs : ∀ i ∈ s, monic (f i)) :
  monic (∏ i in s, f i) :=
monic_multiset_prod_of_monic s.1 f hs

lemma monic.next_coeff_multiset_prod (t : multiset ι) (f : ι → R[X])
  (h : ∀ i ∈ t, monic (f i)) :
  next_coeff (t.map f).prod = (t.map (λ i, next_coeff (f i))).sum :=
begin
  revert h,
  refine multiset.induction_on t _ (λ a t ih ht, _),
  { simp only [multiset.not_mem_zero, forall_prop_of_true, forall_prop_of_false, multiset.map_zero,
               multiset.prod_zero, multiset.sum_zero, not_false_iff, forall_true_iff],
    rw ← C_1, rw next_coeff_C_eq_zero },
  { rw [multiset.map_cons, multiset.prod_cons, multiset.map_cons, multiset.sum_cons,
        monic.next_coeff_mul, ih],
    exacts [λ i hi, ht i (multiset.mem_cons_of_mem hi), ht a (multiset.mem_cons_self _ _),
            monic_multiset_prod_of_monic _ _ (λ b bs, ht _ (multiset.mem_cons_of_mem bs))] }
end

lemma monic.next_coeff_prod (s : finset ι) (f : ι → R[X]) (h : ∀ i ∈ s, monic (f i)) :
  next_coeff (∏ i in s, f i) = ∑ i in s, next_coeff (f i) :=
monic.next_coeff_multiset_prod s.1 f h

end comm_semiring

section semiring
variables [semiring R]

@[simp]
lemma monic.nat_degree_map [semiring S] [nontrivial S] {P : R[X]} (hmo : P.monic)
  (f : R →+* S) : (P.map f).nat_degree = P.nat_degree :=
begin
  refine le_antisymm (nat_degree_map_le _ _) (le_nat_degree_of_ne_zero _),
  rw [coeff_map, monic.coeff_nat_degree hmo, ring_hom.map_one],
  exact one_ne_zero
end

@[simp]
lemma monic.degree_map [semiring S] [nontrivial S] {P : R[X]} (hmo : P.monic)
  (f : R →+* S) : (P.map f).degree = P.degree :=
begin
  by_cases hP : P = 0,
  { simp [hP] },
  { refine le_antisymm (degree_map_le _ _) _,
    rw [degree_eq_nat_degree hP],
    refine le_degree_of_ne_zero _,
    rw [coeff_map, monic.coeff_nat_degree hmo, ring_hom.map_one],
    exact one_ne_zero }
end

section injective
open function
variables [semiring S] {f : R →+* S} (hf : injective f)
include hf

lemma degree_map_eq_of_injective (p : R[X]) : degree (p.map f) = degree p :=
if h : p = 0 then by simp [h]
else degree_map_eq_of_leading_coeff_ne_zero _
  (by rw [← f.map_zero]; exact mt hf.eq_iff.1
    (mt leading_coeff_eq_zero.1 h))

lemma nat_degree_map_eq_of_injective (p : R[X]) :
  nat_degree (p.map f) = nat_degree p :=
nat_degree_eq_of_degree_eq (degree_map_eq_of_injective hf p)

lemma leading_coeff_map' (p : R[X]) :
  leading_coeff (p.map f) = f (leading_coeff p) :=
begin
  unfold leading_coeff,
  rw [coeff_map, nat_degree_map_eq_of_injective hf p],
end

lemma next_coeff_map (p : R[X]) :
  (p.map f).next_coeff = f p.next_coeff :=
begin
  unfold next_coeff,
  rw nat_degree_map_eq_of_injective hf,
  split_ifs; simp
end

lemma leading_coeff_of_injective (p : R[X]) :
  leading_coeff (p.map f) = f (leading_coeff p) :=
begin
  delta leading_coeff,
  rw [coeff_map f, nat_degree_map_eq_of_injective hf p]
end

lemma monic_of_injective {p : R[X]} (hp : (p.map f).monic) : p.monic :=
begin
  apply hf,
  rw [← leading_coeff_of_injective hf, hp.leading_coeff, f.map_one]
end

theorem _root_.function.injective.monic_map_iff {p : R[X]} : p.monic ↔ (p.map f).monic :=
⟨monic.map _, polynomial.monic_of_injective hf⟩

end injective

end semiring

section ring
variables [ring R] {p : R[X]}

theorem monic_X_sub_C (x : R) : monic (X - C x) :=
by simpa only [sub_eq_add_neg, C_neg] using monic_X_add_C (-x)

theorem monic_X_pow_sub {n : ℕ} (H : degree p ≤ n) : monic (X ^ (n+1) - p) :=
by simpa [sub_eq_add_neg] using monic_X_pow_add (show degree (-p) ≤ n, by rwa ←degree_neg p at H)

/-- `X ^ n - a` is monic. -/
lemma monic_X_pow_sub_C {R : Type u} [ring R] (a : R) {n : ℕ} (h : n ≠ 0) : (X ^ n - C a).monic :=
begin
  obtain ⟨k, hk⟩ := nat.exists_eq_succ_of_ne_zero h,
  convert monic_X_pow_sub _,
  exact le_trans degree_C_le nat.with_bot.coe_nonneg,
end

lemma not_is_unit_X_pow_sub_one (R : Type*) [comm_ring R] [nontrivial R] (n : ℕ) :
  ¬ is_unit (X ^ n - 1 : R[X]) :=
begin
  intro h,
  rcases eq_or_ne n 0 with rfl | hn,
  { simpa using h },
  apply hn,
  rw [←@nat_degree_one R, ←(monic_X_pow_sub_C _ hn).eq_one_of_is_unit h, nat_degree_X_pow_sub_C],
end

lemma monic.sub_of_left {p q : R[X]} (hp : monic p) (hpq : degree q < degree p) :
  monic (p - q) :=
by { rw sub_eq_add_neg, apply hp.add_of_left, rwa degree_neg }

lemma monic.sub_of_right {p q : R[X]}
  (hq : q.leading_coeff = -1) (hpq : degree p < degree q) : monic (p - q) :=
have (-q).coeff (-q).nat_degree = 1 :=
by rw [nat_degree_neg, coeff_neg, show q.coeff q.nat_degree = -1, from hq, neg_neg],
by { rw sub_eq_add_neg, apply monic.add_of_right this, rwa degree_neg }

end ring

section nonzero_semiring
variables [semiring R] [nontrivial R] {p q : R[X]}

@[simp] lemma not_monic_zero : ¬monic (0 : R[X]) :=
not_monic_zero_iff.mp zero_ne_one

end nonzero_semiring

section not_zero_divisor

-- TODO: using gh-8537, rephrase lemmas that involve commutation around `*` using the op-ring

variables [semiring R] {p : R[X]}

lemma monic.mul_left_ne_zero (hp : monic p) {q : R[X]} (hq : q ≠ 0) :
  q * p ≠ 0 :=
begin
  by_cases h : p = 1,
  { simpa [h] },
  rw [ne.def, ←degree_eq_bot, hp.degree_mul, with_bot.add_eq_bot, not_or_distrib, degree_eq_bot],
  refine ⟨hq, _⟩,
  rw [←hp.degree_le_zero_iff_eq_one, not_le] at h,
  refine (lt_trans _ h).ne',
  simp
end

lemma monic.mul_right_ne_zero (hp : monic p) {q : R[X]} (hq : q ≠ 0) :
  p * q ≠ 0 :=
begin
  by_cases h : p = 1,
  { simpa [h] },
  rw [ne.def, ←degree_eq_bot, hp.degree_mul_comm, hp.degree_mul, with_bot.add_eq_bot,
      not_or_distrib, degree_eq_bot],
  refine ⟨hq, _⟩,
  rw [←hp.degree_le_zero_iff_eq_one, not_le] at h,
  refine (lt_trans _ h).ne',
  simp
end

lemma monic.mul_nat_degree_lt_iff (h : monic p) {q : R[X]} :
  (p * q).nat_degree < p.nat_degree ↔ p ≠ 1 ∧ q = 0 :=
begin
  by_cases hq : q = 0,
  { suffices : 0 < p.nat_degree ↔ p.nat_degree ≠ 0,
    { simpa [hq, ←h.nat_degree_eq_zero_iff_eq_one] },
    exact ⟨λ h, h.ne', λ h, lt_of_le_of_ne (nat.zero_le _) h.symm ⟩ },
  { simp [h.nat_degree_mul', hq] }
end

lemma monic.mul_right_eq_zero_iff (h : monic p) {q : R[X]} :
  p * q = 0 ↔ q = 0 :=
begin
  by_cases hq : q = 0;
  simp [h.mul_right_ne_zero, hq]
end

lemma monic.mul_left_eq_zero_iff (h : monic p) {q : R[X]} :
  q * p = 0 ↔ q = 0 :=
begin
  by_cases hq : q = 0;
  simp [h.mul_left_ne_zero, hq]
end

lemma monic.is_regular {R : Type*} [ring R] {p : R[X]} (hp : monic p) : is_regular p :=
begin
  split,
  { intros q r h,
    rw [←sub_eq_zero, ←hp.mul_right_eq_zero_iff, mul_sub, h, sub_self] },
  { intros q r h,
    simp only at h,
    rw [←sub_eq_zero, ←hp.mul_left_eq_zero_iff, sub_mul, h, sub_self] }
end

lemma degree_smul_of_smul_regular {S : Type*} [monoid S] [distrib_mul_action S R]
  {k : S} (p : R[X]) (h : is_smul_regular R k) :
  (k • p).degree = p.degree :=
begin
  refine le_antisymm _ _,
  { rw degree_le_iff_coeff_zero,
    intros m hm,
    rw degree_lt_iff_coeff_zero at hm,
    simp [hm m le_rfl] },
  { rw degree_le_iff_coeff_zero,
    intros m hm,
    rw degree_lt_iff_coeff_zero at hm,
    refine h _,
    simpa using hm m le_rfl },
end

lemma nat_degree_smul_of_smul_regular {S : Type*} [monoid S] [distrib_mul_action S R]
  {k : S} (p : R[X]) (h : is_smul_regular R k) :
  (k • p).nat_degree = p.nat_degree :=
begin
  by_cases hp : p = 0,
  { simp [hp] },
  rw [←with_bot.coe_eq_coe, ←degree_eq_nat_degree hp, ←degree_eq_nat_degree,
      degree_smul_of_smul_regular p h],
  contrapose! hp,
  rw ←smul_zero k at hp,
  exact h.polynomial hp
end

lemma leading_coeff_smul_of_smul_regular {S : Type*} [monoid S] [distrib_mul_action S R]
  {k : S} (p : R[X]) (h : is_smul_regular R k) :
  (k • p).leading_coeff = k • p.leading_coeff :=
by rw [leading_coeff, leading_coeff, coeff_smul, nat_degree_smul_of_smul_regular p h]

lemma monic_of_is_unit_leading_coeff_inv_smul (h : is_unit p.leading_coeff) :
  monic (h.unit⁻¹ • p) :=
begin
  rw [monic.def, leading_coeff_smul_of_smul_regular _ (is_smul_regular_of_group _), units.smul_def],
  obtain ⟨k, hk⟩ := h,
  simp only [←hk, smul_eq_mul, ←units.coe_mul, units.coe_eq_one, inv_mul_eq_iff_eq_mul],
  simp [units.ext_iff, is_unit.unit_spec]
end

lemma is_unit_leading_coeff_mul_right_eq_zero_iff (h : is_unit p.leading_coeff) {q : R[X]} :
  p * q = 0 ↔ q = 0 :=
begin
  split,
  { intro hp,
    rw ←smul_eq_zero_iff_eq (h.unit)⁻¹ at hp,
    have : (h.unit)⁻¹ • (p * q) = ((h.unit)⁻¹ • p) * q,
    { ext,
      simp only [units.smul_def, coeff_smul, coeff_mul, smul_eq_mul, mul_sum],
      refine sum_congr rfl (λ x hx, _),
      rw ←mul_assoc },
    rwa [this, monic.mul_right_eq_zero_iff] at hp,
    exact monic_of_is_unit_leading_coeff_inv_smul _ },
  { rintro rfl,
    simp }
end

lemma is_unit_leading_coeff_mul_left_eq_zero_iff (h : is_unit p.leading_coeff) {q : R[X]} :
  q * p = 0 ↔ q = 0 :=
begin
  split,
  { intro hp,
    replace hp := congr_arg (* C ↑(h.unit)⁻¹) hp,
    simp only [zero_mul] at hp,
    rwa [mul_assoc, monic.mul_left_eq_zero_iff] at hp,
    refine monic_mul_C_of_leading_coeff_mul_eq_one _,
    simp [units.mul_inv_eq_iff_eq_mul, is_unit.unit_spec] },
  { rintro rfl,
    rw zero_mul }
end

end not_zero_divisor

end polynomial
