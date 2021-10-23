/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.degree.definitions

/-!
# Trailing degree of univariate polynomials

## Main definitions

* `trailing_degree p`: the multiplicity of `X` in the polynomial `p`
* `nat_trailing_degree`: a variant of `trailing_degree` that takes values in the natural numbers
* `trailing_coeff`: the coefficient at index `nat_trailing_degree p`

Converts most results about `degree`, `nat_degree` and `leading_coeff` to results about the bottom
end of a polynomial
-/

noncomputable theory

open function polynomial finsupp finset
open_locale big_operators classical

namespace polynomial
universes u v
variables {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

section semiring
variables [semiring R] {p q r : polynomial R}

/-- `trailing_degree p` is the multiplicity of `x` in the polynomial `p`, i.e. the smallest
`X`-exponent in `p`.
`trailing_degree p = some n` when `p ≠ 0` and `n` is the smallest power of `X` that appears
in `p`, otherwise
`trailing_degree 0 = ⊤`. -/
def trailing_degree (p : polynomial R) : with_top ℕ := p.support.inf some

lemma trailing_degree_lt_wf : well_founded
(λp q : polynomial R, trailing_degree p < trailing_degree q) :=
inv_image.wf trailing_degree (with_top.well_founded_lt nat.lt_wf)

/-- `nat_trailing_degree p` forces `trailing_degree p` to `ℕ`, by defining
`nat_trailing_degree ⊤ = 0`. -/
def nat_trailing_degree (p : polynomial R) : ℕ := (trailing_degree p).get_or_else 0

/-- `trailing_coeff p` gives the coefficient of the smallest power of `X` in `p`-/
def trailing_coeff (p : polynomial R) : R := coeff p (nat_trailing_degree p)

/-- a polynomial is `monic_at` if its trailing coefficient is 1 -/
def trailing_monic (p : polynomial R) := trailing_coeff p = (1 : R)

lemma trailing_monic.def : trailing_monic p ↔ trailing_coeff p = 1 := iff.rfl

instance trailing_monic.decidable [decidable_eq R] : decidable (trailing_monic p) :=
by unfold trailing_monic; apply_instance

@[simp] lemma trailing_monic.trailing_coeff {p : polynomial R} (hp : p.trailing_monic) :
  trailing_coeff p = 1 := hp

@[simp] lemma trailing_degree_zero : trailing_degree (0 : polynomial R) = ⊤ := rfl

@[simp] lemma trailing_coeff_zero : trailing_coeff (0 : polynomial R) = 0 := rfl

@[simp] lemma nat_trailing_degree_zero : nat_trailing_degree (0 : polynomial R) = 0 := rfl

lemma trailing_degree_eq_top : trailing_degree p = ⊤ ↔ p = 0 :=
⟨λ h, by rw [trailing_degree, ← min_eq_inf_with_top] at h;
  exact support_eq_empty.1 (min_eq_none.1 h),
λ h, by simp [h]⟩

lemma trailing_degree_eq_nat_trailing_degree (hp : p ≠ 0) :
  trailing_degree p = (nat_trailing_degree p : with_top ℕ) :=
let ⟨n, hn⟩ :=
  not_forall.1 (mt option.eq_none_iff_forall_not_mem.2 (mt trailing_degree_eq_top.1 hp)) in
have hn : trailing_degree p = some n := not_not.1 hn,
by rw [nat_trailing_degree, hn]; refl

lemma trailing_degree_eq_iff_nat_trailing_degree_eq {p : polynomial R} {n : ℕ} (hp : p ≠ 0) :
  p.trailing_degree = n ↔ p.nat_trailing_degree = n :=
by rw [trailing_degree_eq_nat_trailing_degree hp, with_top.coe_eq_coe]

lemma trailing_degree_eq_iff_nat_trailing_degree_eq_of_pos {p : polynomial R} {n : ℕ} (hn : 0 < n) :
  p.trailing_degree = n ↔ p.nat_trailing_degree = n :=
begin
  split,
  { intro H, rwa ← trailing_degree_eq_iff_nat_trailing_degree_eq, rintro rfl,
    rw trailing_degree_zero at H, exact option.no_confusion H },
  { intro H, rwa trailing_degree_eq_iff_nat_trailing_degree_eq, rintro rfl,
    rw nat_trailing_degree_zero at H, rw H at hn, exact lt_irrefl _ hn }
end

lemma nat_trailing_degree_eq_of_trailing_degree_eq_some {p : polynomial R} {n : ℕ}
  (h : trailing_degree p = n) : nat_trailing_degree p = n :=
have hp0 : p ≠ 0, from λ hp0, by rw hp0 at h; exact option.no_confusion h,
option.some_inj.1 $ show (nat_trailing_degree p : with_top ℕ) = n,
  by rwa [← trailing_degree_eq_nat_trailing_degree hp0]

@[simp] lemma nat_trailing_degree_le_trailing_degree :
  ↑(nat_trailing_degree p) ≤ trailing_degree p :=
begin
  by_cases hp : p = 0, { rw [hp, trailing_degree_zero], exact le_top },
  rw [trailing_degree_eq_nat_trailing_degree hp],
  exact le_refl _
end

lemma nat_trailing_degree_eq_of_trailing_degree_eq [semiring S] {q : polynomial S}
  (h : trailing_degree p = trailing_degree q) :
nat_trailing_degree p = nat_trailing_degree q :=
by unfold nat_trailing_degree; rw h

lemma le_trailing_degree_of_ne_zero (h : coeff p n ≠ 0) : trailing_degree p ≤ n :=
show @has_le.le (with_top ℕ) _ (p.support.inf some : with_top ℕ) (some n : with_top ℕ),
from finset.inf_le (mem_support_iff.2 h)

lemma nat_trailing_degree_le_of_ne_zero (h : coeff p n ≠ 0) : nat_trailing_degree p ≤ n :=
begin
  rw [← with_top.coe_le_coe, ← trailing_degree_eq_nat_trailing_degree],
  { exact le_trailing_degree_of_ne_zero h, },
  { assume h, subst h, exact h rfl }
end

lemma trailing_degree_le_trailing_degree (h : coeff q (nat_trailing_degree p) ≠ 0) :
  trailing_degree q ≤ trailing_degree p :=
begin
  by_cases hp : p = 0,
  { rw hp, exact le_top },
  { rw trailing_degree_eq_nat_trailing_degree hp, exact le_trailing_degree_of_ne_zero h }
end

lemma trailing_degree_ne_of_nat_trailing_degree_ne {n : ℕ} :
  p.nat_trailing_degree ≠ n → trailing_degree p ≠ n :=
mt $ λ h, by rw [nat_trailing_degree, h, option.get_or_else_coe]

theorem nat_trailing_degree_le_of_trailing_degree_le {n : ℕ} {hp : p ≠ 0}
  (H : (n : with_top ℕ) ≤ trailing_degree p) : n ≤ nat_trailing_degree p :=
begin
  rw trailing_degree_eq_nat_trailing_degree hp at H,
  exact with_top.coe_le_coe.mp H,
end

lemma nat_trailing_degree_le_nat_trailing_degree {hq : q ≠ 0}
  (hpq : p.trailing_degree ≤ q.trailing_degree) :
  p.nat_trailing_degree ≤ q.nat_trailing_degree :=
begin
  by_cases hp : p = 0, { rw [hp, nat_trailing_degree_zero], exact zero_le _ },
  rwa [trailing_degree_eq_nat_trailing_degree hp, trailing_degree_eq_nat_trailing_degree hq,
    with_top.coe_le_coe] at hpq
end

@[simp] lemma trailing_degree_monomial (ha : a ≠ 0) : trailing_degree (monomial n a) = n :=
by rw [trailing_degree, support_monomial _ _ ha, inf_singleton, with_top.some_eq_coe]

lemma nat_trailing_degree_monomial (ha : a ≠ 0) : nat_trailing_degree (monomial n a) = n :=
by rw [nat_trailing_degree, trailing_degree_monomial ha]; refl

lemma nat_trailing_degree_monomial_le : nat_trailing_degree (monomial n a) ≤ n :=
if ha : a = 0 then by simp [ha] else (nat_trailing_degree_monomial ha).le

lemma le_trailing_degree_monomial : ↑n ≤ trailing_degree (monomial n a) :=
if ha : a = 0 then by simp [ha] else (trailing_degree_monomial ha).ge

@[simp] lemma trailing_degree_C (ha : a ≠ 0) : trailing_degree (C a) = (0 : with_top ℕ) :=
trailing_degree_monomial ha

lemma le_trailing_degree_C : (0 : with_top ℕ) ≤ trailing_degree (C a) :=
le_trailing_degree_monomial

lemma trailing_degree_one_le : (0 : with_top ℕ) ≤ trailing_degree (1 : polynomial R) :=
by rw [← C_1]; exact le_trailing_degree_C

@[simp] lemma nat_trailing_degree_C (a : R) : nat_trailing_degree (C a) = 0 :=
nonpos_iff_eq_zero.1 nat_trailing_degree_monomial_le

@[simp] lemma nat_trailing_degree_one : nat_trailing_degree (1 : polynomial R) = 0 :=
nat_trailing_degree_C 1

@[simp] lemma nat_trailing_degree_nat_cast (n : ℕ) : nat_trailing_degree (n : polynomial R) = 0 :=
by simp only [←C_eq_nat_cast, nat_trailing_degree_C]

@[simp] lemma trailing_degree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) :
  trailing_degree (C a * X ^ n) = n :=
by rw [C_mul_X_pow_eq_monomial, trailing_degree_monomial ha]

lemma le_trailing_degree_C_mul_X_pow (n : ℕ) (a : R) :
  (n : with_top ℕ) ≤ trailing_degree (C a * X ^ n) :=
by { rw C_mul_X_pow_eq_monomial, exact le_trailing_degree_monomial }

lemma coeff_eq_zero_of_trailing_degree_lt (h : (n : with_top ℕ) < trailing_degree p) :
  coeff p n = 0 :=
not_not.1 (mt le_trailing_degree_of_ne_zero (not_le_of_gt h))

lemma coeff_eq_zero_of_lt_nat_trailing_degree {p : polynomial R} {n : ℕ}
  (h : n < p.nat_trailing_degree) :
  p.coeff n = 0 :=
begin
  apply coeff_eq_zero_of_trailing_degree_lt,
  by_cases hp : p = 0,
  { rw [hp, trailing_degree_zero], exact with_top.coe_lt_top n, },
  { rwa [trailing_degree_eq_nat_trailing_degree hp, with_top.coe_lt_coe] },
end

@[simp] lemma coeff_nat_trailing_degree_pred_eq_zero {p : polynomial R}
  {hp : (0 : with_top ℕ) < nat_trailing_degree p} : p.coeff (p.nat_trailing_degree - 1) = 0 :=
coeff_eq_zero_of_lt_nat_trailing_degree $ nat.sub_lt
  ((with_top.zero_lt_coe (nat_trailing_degree p)).mp hp) nat.one_pos

theorem le_trailing_degree_X_pow (n : ℕ) :
  (n : with_top ℕ) ≤ trailing_degree (X^n : polynomial R) :=
by simpa only [C_1, one_mul] using le_trailing_degree_C_mul_X_pow n (1:R)

theorem le_trailing_degree_X : (1 : with_top ℕ) ≤ trailing_degree (X : polynomial R) :=
le_trailing_degree_monomial

lemma nat_trailing_degree_X_le : (X : polynomial R).nat_trailing_degree ≤ 1 :=
nat_trailing_degree_monomial_le

@[simp] lemma trailing_coeff_eq_zero : trailing_coeff p = 0 ↔ p = 0 :=
⟨λ h, by_contradiction $ λ hp, mt mem_support_iff.1
  (not_not.2 h) (mem_of_min (trailing_degree_eq_nat_trailing_degree hp)),
λ h, h.symm ▸ leading_coeff_zero⟩

lemma trailing_coeff_nonzero_iff_nonzero : trailing_coeff p ≠ 0 ↔ p ≠ 0 :=
not_congr trailing_coeff_eq_zero

lemma nat_trailing_degree_mem_support_of_nonzero : p ≠ 0 → nat_trailing_degree p ∈ p.support :=
(mem_support_iff.mpr ∘ trailing_coeff_nonzero_iff_nonzero.mpr)

lemma nat_trailing_degree_le_of_mem_supp (a : ℕ) :
  a ∈ p.support → nat_trailing_degree p ≤ a:=
nat_trailing_degree_le_of_ne_zero ∘ mem_support_iff.mp

lemma nat_trailing_degree_eq_support_min' (h : p ≠ 0) :
  nat_trailing_degree p = p.support.min' (nonempty_support_iff.mpr h) :=
begin
  apply le_antisymm,
  { apply le_min',
    intros y hy,
    exact nat_trailing_degree_le_of_mem_supp y hy },
  { apply finset.min'_le,
    exact mem_support_iff.mpr (trailing_coeff_nonzero_iff_nonzero.mpr h), },
end

lemma nat_trailing_degree_le_nat_degree (p : polynomial R) :
  p.nat_trailing_degree ≤ p.nat_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, nat_degree_zero, nat_trailing_degree_zero] },
  { exact le_nat_degree_of_ne_zero (mt trailing_coeff_eq_zero.mp hp) },
end

lemma nat_trailing_degree_mul_X_pow {p : polynomial R} (hp : p ≠ 0) (n : ℕ) :
  (p * X ^ n).nat_trailing_degree = p.nat_trailing_degree + n :=
begin
  apply le_antisymm,
  { refine nat_trailing_degree_le_of_ne_zero (λ h, mt trailing_coeff_eq_zero.mp hp _),
    rwa [trailing_coeff, ←coeff_mul_X_pow] },
  { rw [nat_trailing_degree_eq_support_min' (λ h, hp (mul_X_pow_eq_zero h)), finset.le_min'_iff],
    intros y hy,
    have key : n ≤ y,
    { rw [mem_support_iff, coeff_mul_X_pow'] at hy,
      exact by_contra (λ h, hy (if_neg h)) },
    rw [mem_support_iff, coeff_mul_X_pow', if_pos key] at hy,
    exact (le_tsub_iff_right key).mp (nat_trailing_degree_le_of_ne_zero hy) },
end

end semiring

section nonzero_semiring
variables [semiring R] [nontrivial R] {p q : polynomial R}

@[simp] lemma trailing_degree_one : trailing_degree (1 : polynomial R) = (0 : with_top ℕ) :=
trailing_degree_C one_ne_zero

@[simp] lemma trailing_degree_X : trailing_degree (X : polynomial R) = 1 :=
trailing_degree_monomial one_ne_zero

@[simp] lemma nat_trailing_degree_X : (X : polynomial R).nat_trailing_degree = 1 :=
nat_trailing_degree_monomial one_ne_zero

end nonzero_semiring

section ring
variables [ring R]

@[simp] lemma trailing_degree_neg (p : polynomial R) : trailing_degree (-p) = trailing_degree p :=
by unfold trailing_degree; rw support_neg

@[simp] lemma nat_trailing_degree_neg (p : polynomial R) :
  nat_trailing_degree (-p) = nat_trailing_degree p :=
by simp [nat_trailing_degree]

@[simp] lemma nat_trailing_degree_int_cast (n : ℤ) : nat_trailing_degree (n : polynomial R) = 0 :=
by simp only [←C_eq_int_cast, nat_trailing_degree_C]

end ring

section semiring
variables [semiring R]

/-- The second-lowest coefficient, or 0 for constants -/
def next_coeff_up (p : polynomial R) : R :=
if p.nat_trailing_degree = 0 then 0 else p.coeff (p.nat_trailing_degree + 1)

@[simp]
lemma next_coeff_up_C_eq_zero (c : R) :
  next_coeff_up (C c) = 0 := by { rw next_coeff_up, simp }

lemma next_coeff_up_of_pos_nat_trailing_degree (p : polynomial R) (hp : 0 < p.nat_trailing_degree) :
  next_coeff_up p = p.coeff (p.nat_trailing_degree + 1) :=
by { rw [next_coeff_up, if_neg], contrapose! hp, simpa }

end semiring

section semiring
variables [semiring R] {p q : polynomial R} {ι : Type*}

lemma coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt
  (h : trailing_degree p < trailing_degree q) :
  coeff q (nat_trailing_degree p) = 0 :=
coeff_eq_zero_of_trailing_degree_lt $ nat_trailing_degree_le_trailing_degree.trans_lt h

lemma ne_zero_of_trailing_degree_lt {n : with_top ℕ} (h : trailing_degree p < n) : p ≠ 0 :=
λ h₀, h.not_le (by simp [h₀])

end semiring
end polynomial
