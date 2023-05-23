/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.big_operators.fin
import data.polynomial.degree.definitions

/-!
# Erase the leading term of a univariate polynomial

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Definition

* `erase_lead f`: the polynomial `f - leading term of f`

`erase_lead` serves as reduction step in an induction, shaving off one monomial from a polynomial.
The definition is set up so that it does not mention subtraction in the definition,
and thus works for polynomials over semirings as well as rings.
-/

noncomputable theory
open_locale classical polynomial

open polynomial finset

namespace polynomial

variables {R : Type*} [semiring R] {f : R[X]}

/-- `erase_lead f` for a polynomial `f` is the polynomial obtained by
subtracting from `f` the leading term of `f`. -/
def erase_lead (f : R[X]) : R[X] :=
polynomial.erase f.nat_degree f

section erase_lead

lemma erase_lead_support (f : R[X]) :
  f.erase_lead.support = f.support.erase f.nat_degree :=
by simp only [erase_lead, support_erase]

lemma erase_lead_coeff (i : ℕ) :
  f.erase_lead.coeff i = if i = f.nat_degree then 0 else f.coeff i :=
by simp only [erase_lead, coeff_erase]

@[simp] lemma erase_lead_coeff_nat_degree : f.erase_lead.coeff f.nat_degree = 0 :=
by simp [erase_lead_coeff]

lemma erase_lead_coeff_of_ne (i : ℕ) (hi : i ≠ f.nat_degree) :
  f.erase_lead.coeff i = f.coeff i :=
by simp [erase_lead_coeff, hi]

@[simp] lemma erase_lead_zero : erase_lead (0 : R[X]) = 0 :=
by simp only [erase_lead, erase_zero]

@[simp] lemma erase_lead_add_monomial_nat_degree_leading_coeff (f : R[X]) :
  f.erase_lead + monomial f.nat_degree f.leading_coeff = f :=
(add_comm _ _).trans (f.monomial_add_erase _)

@[simp] lemma erase_lead_add_C_mul_X_pow (f : R[X]) :
  f.erase_lead + (C f.leading_coeff) * X ^ f.nat_degree = f :=
by rw [C_mul_X_pow_eq_monomial, erase_lead_add_monomial_nat_degree_leading_coeff]

@[simp] lemma self_sub_monomial_nat_degree_leading_coeff {R : Type*} [ring R] (f : R[X]) :
  f - monomial f.nat_degree f.leading_coeff = f.erase_lead :=
(eq_sub_iff_add_eq.mpr (erase_lead_add_monomial_nat_degree_leading_coeff f)).symm

@[simp] lemma self_sub_C_mul_X_pow {R : Type*} [ring R] (f : R[X]) :
  f - (C f.leading_coeff) * X ^ f.nat_degree = f.erase_lead :=
by rw [C_mul_X_pow_eq_monomial, self_sub_monomial_nat_degree_leading_coeff]

lemma erase_lead_ne_zero (f0 : 2 ≤ f.support.card) : erase_lead f ≠ 0 :=
begin
  rw [ne, ← card_support_eq_zero, erase_lead_support],
  exact (zero_lt_one.trans_le $ (tsub_le_tsub_right f0 1).trans
    finset.pred_card_le_card_erase).ne.symm
end

lemma lt_nat_degree_of_mem_erase_lead_support {a : ℕ} (h : a ∈ (erase_lead f).support) :
  a < f.nat_degree :=
begin
  rw [erase_lead_support, mem_erase] at h,
  exact (le_nat_degree_of_mem_supp a h.2).lt_of_ne h.1,
end

lemma ne_nat_degree_of_mem_erase_lead_support {a : ℕ} (h : a ∈ (erase_lead f).support) :
  a ≠ f.nat_degree :=
(lt_nat_degree_of_mem_erase_lead_support h).ne

lemma nat_degree_not_mem_erase_lead_support : f.nat_degree ∉ (erase_lead f).support :=
λ h, ne_nat_degree_of_mem_erase_lead_support h rfl

lemma erase_lead_support_card_lt (h : f ≠ 0) : (erase_lead f).support.card < f.support.card :=
begin
  rw erase_lead_support,
  exact card_lt_card (erase_ssubset $ nat_degree_mem_support_of_nonzero h)
end

lemma erase_lead_card_support {c : ℕ} (fc : f.support.card = c) :
  f.erase_lead.support.card = c - 1 :=
begin
  by_cases f0 : f = 0,
  { rw [← fc, f0, erase_lead_zero, support_zero, card_empty] },
  { rw [erase_lead_support, card_erase_of_mem (nat_degree_mem_support_of_nonzero f0), fc] }
end

lemma erase_lead_card_support' {c : ℕ} (fc : f.support.card = c + 1) :
  f.erase_lead.support.card = c :=
erase_lead_card_support fc

@[simp] lemma erase_lead_monomial (i : ℕ) (r : R) :
  erase_lead (monomial i r) = 0 :=
begin
  by_cases hr : r = 0,
  { subst r, simp only [monomial_zero_right, erase_lead_zero] },
  { rw [erase_lead, nat_degree_monomial, if_neg hr, erase_monomial] }
end

@[simp] lemma erase_lead_C (r : R) : erase_lead (C r) = 0 :=
erase_lead_monomial _ _

@[simp] lemma erase_lead_X : erase_lead (X : R[X]) = 0 :=
erase_lead_monomial _ _

@[simp] lemma erase_lead_X_pow (n : ℕ) : erase_lead (X ^ n : R[X]) = 0 :=
by rw [X_pow_eq_monomial, erase_lead_monomial]

@[simp] lemma erase_lead_C_mul_X_pow (r : R) (n : ℕ) : erase_lead (C r * X ^ n) = 0 :=
by rw [C_mul_X_pow_eq_monomial, erase_lead_monomial]

lemma erase_lead_add_of_nat_degree_lt_left {p q : R[X]} (pq : q.nat_degree < p.nat_degree) :
  (p + q).erase_lead = p.erase_lead + q :=
begin
  ext n,
  by_cases nd : n = p.nat_degree,
  { rw [nd, erase_lead_coeff, if_pos (nat_degree_add_eq_left_of_nat_degree_lt pq).symm],
    simpa using (coeff_eq_zero_of_nat_degree_lt pq).symm },
  { rw [erase_lead_coeff, coeff_add, coeff_add, erase_lead_coeff, if_neg, if_neg nd],
    rintro rfl,
    exact nd (nat_degree_add_eq_left_of_nat_degree_lt pq) }
end

lemma erase_lead_add_of_nat_degree_lt_right {p q : R[X]} (pq : p.nat_degree < q.nat_degree) :
  (p + q).erase_lead = p + q.erase_lead :=
begin
  ext n,
  by_cases nd : n = q.nat_degree,
  { rw [nd, erase_lead_coeff, if_pos (nat_degree_add_eq_right_of_nat_degree_lt pq).symm],
    simpa using (coeff_eq_zero_of_nat_degree_lt pq).symm },
  { rw [erase_lead_coeff, coeff_add, coeff_add, erase_lead_coeff, if_neg, if_neg nd],
    rintro rfl,
    exact nd (nat_degree_add_eq_right_of_nat_degree_lt pq) }
end

lemma erase_lead_degree_le : (erase_lead f).degree ≤ f.degree := f.degree_erase_le _

lemma erase_lead_nat_degree_le_aux : (erase_lead f).nat_degree ≤ f.nat_degree :=
nat_degree_le_nat_degree erase_lead_degree_le

lemma erase_lead_nat_degree_lt (f0 : 2 ≤ f.support.card) :
  (erase_lead f).nat_degree < f.nat_degree :=
lt_of_le_of_ne erase_lead_nat_degree_le_aux $ ne_nat_degree_of_mem_erase_lead_support $
  nat_degree_mem_support_of_nonzero $ erase_lead_ne_zero f0

lemma erase_lead_nat_degree_lt_or_erase_lead_eq_zero (f : R[X]) :
  (erase_lead f).nat_degree < f.nat_degree ∨ f.erase_lead = 0 :=
begin
  by_cases h : f.support.card ≤ 1,
  { right,
    rw ← C_mul_X_pow_eq_self h,
    simp },
  { left,
    apply erase_lead_nat_degree_lt (lt_of_not_ge h) }
end

lemma erase_lead_nat_degree_le (f : R[X]) : (erase_lead f).nat_degree ≤ f.nat_degree - 1 :=
begin
  rcases f.erase_lead_nat_degree_lt_or_erase_lead_eq_zero with h | h,
  { exact nat.le_pred_of_lt h },
  { simp only [h, nat_degree_zero, zero_le] }
end

end erase_lead

/-- An induction lemma for polynomials. It takes a natural number `N` as a parameter, that is
required to be at least as big as the `nat_degree` of the polynomial.  This is useful to prove
results where you want to change each term in a polynomial to something else depending on the
`nat_degree` of the polynomial itself and not on the specific `nat_degree` of each term. -/
lemma induction_with_nat_degree_le (P : R[X] → Prop) (N : ℕ)
  (P_0 : P 0)
  (P_C_mul_pow : ∀ n : ℕ, ∀ r : R, r ≠ 0 → n ≤ N → P (C r * X ^ n))
  (P_C_add : ∀ f g : R[X], f.nat_degree < g.nat_degree →
    g.nat_degree ≤ N → P f → P g → P (f + g)) :
  ∀ f : R[X], f.nat_degree ≤ N → P f :=
begin
  intros f df,
  generalize' hd : card f.support = c,
  revert f,
  induction c with c hc,
  { assume f df f0,
    convert P_0,
    simpa only [support_eq_empty, card_eq_zero] using f0 },
  { intros f df f0,
    rw [← erase_lead_add_C_mul_X_pow f],
    cases c,
    { convert P_C_mul_pow f.nat_degree f.leading_coeff _ df,
      { convert zero_add _,
        rw [← card_support_eq_zero, erase_lead_card_support f0] },
      { rw [leading_coeff_ne_zero, ne.def, ← card_support_eq_zero, f0],
        exact zero_ne_one.symm } },
    refine P_C_add f.erase_lead _ _ _ _ _,
    { refine (erase_lead_nat_degree_lt _).trans_le (le_of_eq _),
      { exact (nat.succ_le_succ (nat.succ_le_succ (nat.zero_le _))).trans f0.ge },
      { rw [nat_degree_C_mul_X_pow _ _ (leading_coeff_ne_zero.mpr _)],
        rintro rfl,
        simpa using f0 } },
    { exact (nat_degree_C_mul_X_pow_le f.leading_coeff f.nat_degree).trans df },
    { exact hc _ (erase_lead_nat_degree_le_aux.trans df) (erase_lead_card_support f0) },
    { refine P_C_mul_pow _ _ _ df,
      rw [ne.def, leading_coeff_eq_zero, ← card_support_eq_zero, f0],
      exact nat.succ_ne_zero _ } }
end

/-- Let `φ : R[x] → S[x]` be an additive map, `k : ℕ` a bound, and `fu : ℕ → ℕ` a
"sufficiently monotone" map.  Assume also that
* `φ` maps to `0` all monomials of degree less than `k`,
* `φ` maps each monomial `m` in `R[x]` to a polynomial `φ m` of degree `fu (deg m)`.
Then, `φ` maps each polynomial `p` in `R[x]` to a polynomial of degree `fu (deg p)`. -/
lemma mono_map_nat_degree_eq {S F : Type*} [semiring S]
  [add_monoid_hom_class F R[X] S[X]] {φ : F}
  {p : R[X]} (k : ℕ)
  (fu : ℕ → ℕ) (fu0 : ∀ {n}, n ≤ k → fu n = 0) (fc : ∀ {n m}, k ≤ n → n < m → fu n < fu m)
  (φ_k : ∀ {f : R[X]}, f.nat_degree < k → φ f = 0)
  (φ_mon_nat : ∀ n c, c ≠ 0 → (φ (monomial n c)).nat_degree = fu n) :
  (φ p).nat_degree = fu p.nat_degree :=
begin
  refine induction_with_nat_degree_le (λ p, _ = fu _) p.nat_degree (by simp [fu0]) _ _ _ rfl.le,
  { intros n r r0 np,
    rw [nat_degree_C_mul_X_pow _ _ r0, C_mul_X_pow_eq_monomial, φ_mon_nat _ _ r0] },
  { intros f g fg gp fk gk,
    rw [nat_degree_add_eq_right_of_nat_degree_lt fg, _root_.map_add],
    by_cases FG : k ≤ f.nat_degree,
    { rw [nat_degree_add_eq_right_of_nat_degree_lt, gk],
      rw [fk, gk],
      exact fc FG fg },
    { cases k,
      { exact (FG (nat.zero_le _)).elim },
      { rwa [φ_k (not_le.mp FG), zero_add] } } }
end

lemma map_nat_degree_eq_sub {S F : Type*} [semiring S]
  [add_monoid_hom_class F R[X] S[X]] {φ : F}
  {p : R[X]} {k : ℕ}
  (φ_k : ∀ f : R[X], f.nat_degree < k → φ f = 0)
  (φ_mon : ∀ n c, c ≠ 0 → (φ (monomial n c)).nat_degree = n - k) :
  (φ p).nat_degree = p.nat_degree - k :=
mono_map_nat_degree_eq k (λ j, j - k) (by simp) (λ m n h, (tsub_lt_tsub_iff_right h).mpr) φ_k φ_mon

lemma map_nat_degree_eq_nat_degree {S F : Type*} [semiring S]
  [add_monoid_hom_class F R[X] S[X]] {φ : F} (p)
  (φ_mon_nat : ∀ n c, c ≠ 0 → (φ (monomial n c)).nat_degree = n) :
  (φ p).nat_degree = p.nat_degree :=
(map_nat_degree_eq_sub (λ f h, (nat.not_lt_zero _ h).elim) (by simpa)).trans p.nat_degree.sub_zero

open_locale big_operators

lemma card_support_eq' {n : ℕ} (k : fin n → ℕ) (x : fin n → R) (hk : function.injective k)
  (hx : ∀ i, x i ≠ 0) :  (∑ i, C (x i) * X ^ k i).support.card = n :=
begin
  suffices : (∑ i, C (x i) * X ^ k i).support = image k univ,
  { rw [this, univ.card_image_of_injective hk, card_fin] },
  simp_rw [finset.ext_iff, mem_support_iff, finset_sum_coeff, coeff_C_mul_X_pow,
    mem_image, mem_univ, exists_true_left],
  refine λ i, ⟨λ h, _, _⟩,
  { obtain ⟨j, hj, h⟩ := exists_ne_zero_of_sum_ne_zero h,
    exact ⟨j, (ite_ne_right_iff.mp h).1.symm⟩ },
  { rintros ⟨j, rfl⟩,
    rw [sum_eq_single_of_mem j (mem_univ j), if_pos rfl],
    { exact hx j },
    { exact λ m hm hmj, if_neg (λ h, hmj.symm (hk h)) } },
end

lemma card_support_eq {n : ℕ} : f.support.card = n ↔ ∃ (k : fin n → ℕ) (x : fin n → R)
  (hk : strict_mono k) (hx : ∀ i, x i ≠ 0), f = ∑ i, C (x i) * X ^ k i :=
begin
  refine ⟨_, λ ⟨k, x, hk, hx, hf⟩, hf.symm ▸ card_support_eq' k x hk.injective hx⟩,
  induction n with n hn generalizing f,
  { exact λ hf, ⟨0, 0, is_empty_elim, is_empty_elim, card_support_eq_zero.mp hf⟩ },
  { intro h,
    obtain ⟨k, x, hk, hx, hf⟩ := hn (erase_lead_card_support' h),
    have H : ¬ ∃ k : fin n, k.cast_succ = fin.last n,
    { rintros ⟨i, hi⟩,
      exact (i.cast_succ_lt_last).ne hi },
    refine ⟨function.extend fin.cast_succ k (λ _, f.nat_degree),
      function.extend fin.cast_succ x (λ _, f.leading_coeff), _, _, _⟩,
    { intros i j hij,
      have hi : i ∈ set.range (fin.cast_succ : fin n ↪o fin (n + 1)),
      { rw [fin.range_cast_succ, set.mem_def],
        exact lt_of_lt_of_le hij (nat.lt_succ_iff.mp j.2) },
      obtain ⟨i, rfl⟩ := hi,
      rw fin.cast_succ.injective.extend_apply,
      by_cases hj : ∃ j₀, fin.cast_succ j₀ = j,
      { obtain ⟨j, rfl⟩ := hj,
        rwa [fin.cast_succ.injective.extend_apply, hk.lt_iff_lt,
          ←fin.cast_succ_lt_cast_succ_iff] },
      { rw [function.extend_apply' _ _ _ hj],
        apply lt_nat_degree_of_mem_erase_lead_support,
        rw [mem_support_iff, hf, finset_sum_coeff],
        rw [sum_eq_single, coeff_C_mul, coeff_X_pow_self, mul_one],
        { exact hx i },
        { intros j hj hji,
          rw [coeff_C_mul, coeff_X_pow, if_neg (hk.injective.ne hji.symm), mul_zero] },
        { exact λ hi, (hi (mem_univ i)).elim } } },
    { intro i,
      by_cases hi : ∃ i₀, fin.cast_succ i₀ = i,
      { obtain ⟨i, rfl⟩ := hi,
        rw fin.cast_succ.injective.extend_apply,
        exact hx i },
      { rw [function.extend_apply' _ _ _ hi, ne, leading_coeff_eq_zero,
          ←card_support_eq_zero, h],
        exact n.succ_ne_zero } },
    { rw fin.sum_univ_cast_succ,
      simp only [fin.cast_succ.injective.extend_apply],
      rw [←hf, function.extend_apply', function.extend_apply', erase_lead_add_C_mul_X_pow],
      all_goals { exact H } } },
end

lemma card_support_eq_one : f.support.card = 1 ↔ ∃ (k : ℕ) (x : R) (hx : x ≠ 0), f = C x * X ^ k :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h,
    exact ⟨k 0, x 0, hx 0, fin.sum_univ_one _⟩ },
  { rintros ⟨k, x, hx, rfl⟩,
    rw [support_C_mul_X_pow k hx, card_singleton] },
end

lemma card_support_eq_two : f.support.card = 2 ↔ ∃ (k m : ℕ) (hkm : k < m)
  (x y : R) (hx : x ≠ 0) (hy : y ≠ 0), f = C x * X ^ k + C y * X ^ m :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h,
    refine ⟨k 0, k 1, hk (by exact nat.zero_lt_one), x 0, x 1, hx 0, hx 1, _⟩,
    rw [fin.sum_univ_cast_succ, fin.sum_univ_one],
    refl },
  { rintros ⟨k, m, hkm, x, y, hx, hy, rfl⟩,
    exact card_support_binomial hkm.ne hx hy },
end

lemma card_support_eq_three : f.support.card = 3 ↔
  ∃ (k m n : ℕ) (hkm : k < m) (hmn : m < n) (x y z : R) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0),
    f = C x * X ^ k + C y * X ^ m + C z * X ^ n :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h,
    refine ⟨k 0, k 1, k 2, hk (by exact nat.zero_lt_one), hk (by exact nat.lt_succ_self 1),
      x 0, x 1, x 2, hx 0, hx 1, hx 2, _⟩,
    rw [fin.sum_univ_cast_succ, fin.sum_univ_cast_succ, fin.sum_univ_one],
    refl },
  { rintros ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩,
    exact card_support_trinomial hkm hmn hx hy hz },
end

end polynomial
