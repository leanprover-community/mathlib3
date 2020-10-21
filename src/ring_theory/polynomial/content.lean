/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson
-/
import data.finset.gcd
import data.polynomial
import data.polynomial.erase_lead

/-!
# Gauss's Lemma, and GCD structures on polynomials

Gauss's Lemma is one of a few results pertaining to `gcd`s and irreducibility in polynomials over
GCD domains.

## Main Definitions
Let `p : polynomial R`.
 - `p.content` is the `gcd` of the coefficients of `p`.
 - `p.is_primitive` indicates that `p.content = 1`.

## Main Results
 - If `p q : polynomial R`, then `(p * q).content = p.content * q.content`.

-/

variables {R : Type*} [integral_domain R]

namespace polynomial
section gcd_monoid
variable [gcd_monoid R]

/-- `p.content` is the `gcd` of the coefficients of `p`. -/
def content (p : polynomial R) : R := (p.support).gcd p.coeff

lemma content_dvd_coeff {p : polynomial R} (n : ℕ) : p.content ∣ p.coeff n :=
begin
  by_cases h : n ∈ p.support,
  { apply finset.gcd_dvd h },
  rw [mem_support_iff_coeff_ne_zero, not_not] at h,
  rw h,
  apply dvd_zero,
end

@[simp] lemma content_C {r : R} : (C r).content = normalize r :=
begin
  rw content,
  by_cases h0 : r = 0,
  { simp [h0] },
  have h : (C r).support = {0} := finsupp.support_single_ne_zero h0,
  simp [h],
end

@[simp] lemma content_zero : content (0 : polynomial R) = 0 :=
by rw [← C_0, content_C, normalize_zero]

@[simp] lemma content_one : content (1 : polynomial R) = 1 :=
by rw [← C_1, content_C, normalize_one]

lemma content_X_mul {p : polynomial R} : content (X * p) = content p :=
begin
  rw [content, content, finset.gcd_def, finset.gcd_def],
  refine congr rfl _,
  have h : (X * p).support = p.support.map ⟨nat.succ, nat.succ_injective⟩,
  { ext a,
    simp only [exists_prop, finset.mem_map, function.embedding.coe_fn_mk, ne.def,
      mem_support_iff_coeff_ne_zero],
    cases a,
    { simp [coeff_X_mul_zero, nat.succ_ne_zero] },
    rw [mul_comm, coeff_mul_X],
    split,
    { intro h,
      use a,
      simp [h] },
    { rintros ⟨b, ⟨h1, h2⟩⟩,
      rw ← nat.succ_injective h2,
      apply h1 } },
  rw h,
  simp only [finset.map_val, function.comp_app, function.embedding.coe_fn_mk, multiset.map_map],
  refine congr (congr rfl _) rfl,
  ext a,
  rw mul_comm,
  simp [coeff_mul_X],
end

@[simp] lemma content_X_pow {k : ℕ} : content ((X : polynomial R) ^ k) = 1 :=
begin
  induction k with k hi,
  { simp },
  rw [pow_succ, content_X_mul, hi]
end

@[simp] lemma content_X : content (X : polynomial R) = 1 :=
by { rw [← mul_one X, content_X_mul, content_one] }

lemma content_C_mul (r : R) (p : polynomial R) : (C r * p).content = normalize r * p.content :=
begin
  by_cases h0 : r = 0, { simp [h0] },
  rw content, rw content, rw ← finset.gcd_mul_left,
  refine congr (congr rfl _) _; ext; simp [h0, mem_support_iff_coeff_ne_zero]
end

@[simp] lemma content_monomial {r : R} {k : ℕ} : content (monomial k r) = normalize r :=
by { rw [single_eq_C_mul_X, content_C_mul, content_X_pow, mul_one] }

lemma content_eq_zero_iff {p : polynomial R} : content p = 0 ↔ p = 0 :=
begin
  rw [content, finset.gcd_eq_zero_iff],
  split; intro h,
  { ext n,
    by_cases h0 : n ∈ p.support,
    { rw [h n h0, coeff_zero], },
    { rw mem_support_iff_coeff_ne_zero at h0,
      push_neg at h0,
      simp [h0] } },
  { intros x h0,
    simp [h] }
end

@[simp] lemma normalize_content {p : polynomial R} : normalize p.content = p.content :=
finset.normalize_gcd

lemma content_eq_gcd_range_of_lt (p : polynomial R) (n : ℕ) (h : p.nat_degree < n) :
  p.content = (finset.range n).gcd p.coeff :=
begin
  apply dvd_antisymm_of_normalize_eq normalize_content finset.normalize_gcd,
  { rw finset.dvd_gcd_iff,
    intros i hi,
    apply content_dvd_coeff _ },
  { apply finset.gcd_mono,
    intro i,
    simp only [nat.lt_succ_iff, mem_support_iff_coeff_ne_zero, ne.def, finset.mem_range],
    contrapose!,
    intro h1,
    apply coeff_eq_zero_of_nat_degree_lt (lt_of_lt_of_le h h1), }
end

lemma content_eq_gcd_range_succ (p : polynomial R) :
  p.content = (finset.range p.nat_degree.succ).gcd p.coeff :=
content_eq_gcd_range_of_lt _ _ (nat.lt_succ_self _)

lemma content_eq_gcd_leading_coeff_content_erase_lead (p : polynomial R) :
  p.content = gcd_monoid.gcd p.leading_coeff (erase_lead p).content :=
begin
  by_cases h : p = 0,
  { simp [h] },
  rw [← leading_coeff_eq_zero, leading_coeff, ← ne.def, ← mem_support_iff_coeff_ne_zero] at h,
  rw [content, ← finset.insert_erase h, finset.gcd_insert, leading_coeff, content,
    erase_lead_support],
  refine congr rfl (finset.gcd_congr rfl (λ i hi, _)),
  rw finset.mem_erase at hi,
  rw [erase_lead_coeff, if_neg hi.1],
end

lemma dvd_content_iff_C_dvd {p : polynomial R} {r : R} : r ∣ p.content ↔ C r ∣ p :=
begin
  rw C_dvd_iff_dvd_coeff,
  split,
  { intros h i,
    apply dvd_trans h (content_dvd_coeff _) },
  { intro h,
    rw [content, finset.dvd_gcd_iff],
    intros i hi,
    apply h i }
end

lemma C_content_dvd (p : polynomial R) : C p.content ∣ p :=
dvd_content_iff_C_dvd.1 (dvd_refl _)

/-- A polynomial over a GCD domain is primitive when the `gcd` of its coefficients is 1 -/
def is_primitive (p : polynomial R) : Prop := p.content = 1

@[simp]
lemma is_primitive_one : is_primitive (1 : polynomial R) :=
by rw [is_primitive, ← C_1, content_C, normalize_one]

lemma is_primitive.ne_zero {p : polynomial R} (hp : p.is_primitive) : p ≠ 0 :=
begin
  rintro rfl,
  rw [is_primitive, content_zero] at hp,
  apply zero_ne_one hp,
end

lemma is_primitive.content_eq_one {p : polynomial R} (hp : p.is_primitive) : p.content = 1 := hp

lemma is_primitive_iff_is_unit_of_C_dvd {p : polynomial R} :
  p.is_primitive ↔ ∀ (r : R), C r ∣ p → is_unit r :=
begin
  rw [is_primitive],
  split,
  { intros h r hdvd,
    rw [← dvd_content_iff_C_dvd, h] at hdvd,
    apply is_unit_of_dvd_one _ hdvd },
  { intro h,
    rw [← normalize_content, normalize_eq_one],
    apply h _ (C_content_dvd _) }
end

lemma eq_C_mul_primitive (p : polynomial R) :
  ∃ (r : R) (q : polynomial R), p = C r * q ∧ q.is_primitive ∧ p.nat_degree = q.nat_degree :=
begin
  by_cases h0 : p = 0,
  { use [0, 1],
    simp [h0] },
  rcases C_content_dvd p with ⟨q, h⟩,
  use [p.content, q],
  refine ⟨h, _, _⟩,
  { have h1 := content_C_mul p.content q,
    rw [← h, normalize_content, ← mul_one p.content, mul_assoc, one_mul] at h1,
    apply mul_left_cancel' _ h1.symm,
    rwa ← content_eq_zero_iff at h0 },
  { rw [h, mul_eq_zero] at h0,
    classical,
    rcases (decidable.not_or_iff_and_not _ _).1 h0,
    rw [h, nat_degree_mul left right, nat_degree_C, zero_add] }
end

lemma gcd_content_eq_of_dvd_sub {a : R} {p q : polynomial R} (h : C a ∣ p - q) :
  gcd_monoid.gcd a p.content = gcd_monoid.gcd a q.content :=
begin
  rw content_eq_gcd_range_of_lt p (max p.nat_degree q.nat_degree).succ
    (lt_of_le_of_lt (le_max_left _ _) (nat.lt_succ_self _)),
  rw content_eq_gcd_range_of_lt q (max p.nat_degree q.nat_degree).succ
    (lt_of_le_of_lt (le_max_right _ _) (nat.lt_succ_self _)),
  apply finset.gcd_eq_of_dvd_sub,
  intros x hx,
  cases h with w hw,
  use w.coeff x,
  rw [← coeff_sub, hw, coeff_C_mul]
end

lemma content_mul_aux {p q : polynomial R} :
  gcd_monoid.gcd (p * q).erase_lead.content p.leading_coeff =
  gcd_monoid.gcd (p.erase_lead * q).content p.leading_coeff :=
begin
  rw [gcd_comm (content _) _, gcd_comm (content _) _],
  apply gcd_content_eq_of_dvd_sub,
  rw [← self_sub_C_mul_X_pow, ← self_sub_C_mul_X_pow, sub_mul, sub_sub, add_comm, sub_add,
    sub_sub_cancel, leading_coeff_mul, ring_hom.map_mul, mul_assoc, mul_assoc],
  apply dvd_sub (dvd.intro _ rfl) (dvd.intro _ rfl),
end

@[simp]
theorem content_mul {p q : polynomial R} : (p * q).content = p.content * q.content :=
begin
  suffices h : ∀ (n : ℕ) (p q : polynomial R), ((p * q).degree < n) →
    (p * q).content = p.content * q.content,
  { apply h,
    apply (lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 (nat.lt_succ_self _))) },
  intro n,
  induction n with n ih,
  { intros p q hpq,
    rw [with_bot.coe_zero, nat.with_bot.lt_zero_iff, degree_eq_bot, mul_eq_zero] at hpq,
    rcases hpq with rfl | rfl; simp },
  intros p q hpq,
  by_cases p0 : p = 0, { simp [p0] },
  by_cases q0 : q = 0, { simp [q0] },
  rw [degree_eq_nat_degree (mul_ne_zero p0 q0), with_bot.coe_lt_coe, nat.lt_succ_iff_lt_or_eq,
    ← with_bot.coe_lt_coe, ← degree_eq_nat_degree (mul_ne_zero p0 q0), nat_degree_mul p0 q0] at hpq,
  rcases hpq with hlt | heq, { apply ih _ _ hlt },
  rcases p.eq_C_mul_primitive with ⟨cp, p1, rfl, p1_prim, p1_deg⟩,
  rcases q.eq_C_mul_primitive with ⟨cq, q1, rfl, q1_prim, q1_deg⟩,
  suffices h : (q1 * p1).content = 1,
  { rw [mul_assoc, content_C_mul, content_C_mul, mul_comm p1, mul_assoc, content_C_mul,
    content_C_mul, h, mul_one, q1_prim.content_eq_one, p1_prim.content_eq_one, mul_one, mul_one] },
  rw [p1_deg, q1_deg, ← with_bot.coe_eq_coe, with_bot.coe_add,
    ← degree_eq_nat_degree p1_prim.ne_zero, ← degree_eq_nat_degree q1_prim.ne_zero] at heq,
  rw [← normalize_content, normalize_eq_one, is_unit_iff_dvd_one,
      content_eq_gcd_leading_coeff_content_erase_lead, leading_coeff_mul, gcd_comm],
  apply dvd_trans (gcd_mul_dvd_mul_gcd _ _ _),
  rw [content_mul_aux, ih, p1_prim.content_eq_one, mul_one, gcd_comm,
      ← content_eq_gcd_leading_coeff_content_erase_lead, q1_prim.content_eq_one, one_mul,
      mul_comm q1, content_mul_aux, ih, q1_prim.content_eq_one, mul_one, gcd_comm,
      ← content_eq_gcd_leading_coeff_content_erase_lead, p1_prim.content_eq_one],
  { rw [← heq, degree_mul, with_bot.add_lt_add_iff_right],
    { apply degree_erase_lt p1_prim.ne_zero },
    { rw [bot_lt_iff_ne_bot, ne.def, degree_eq_bot],
      apply q1_prim.ne_zero } },
  { rw [mul_comm, ← heq, degree_mul, with_bot.add_lt_add_iff_left],
    { apply degree_erase_lt q1_prim.ne_zero },
    { rw [bot_lt_iff_ne_bot, ne.def, degree_eq_bot],
      apply p1_prim.ne_zero } }
end

end gcd_monoid
end polynomial
