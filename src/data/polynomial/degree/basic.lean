/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.coeff

/-!
# Theory of univariate polynomials

The definitions include
`degree`, `monic`, `leading_coeff`
-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

local attribute [instance, priority 10] is_semiring_hom.comp is_ring_hom.comp

open finsupp finset add_monoid_algebra
open_locale big_operators

namespace polynomial
universes u v --w x y z
variables {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

section semiring
variables [semiring R] {p q r : polynomial R}

/-- `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`.
`degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise
`degree 0 = ⊥`. -/
def degree (p : polynomial R) : with_bot ℕ := p.support.sup some

lemma degree_lt_wf : well_founded (λp q : polynomial R, degree p < degree q) :=
inv_image.wf degree (with_bot.well_founded_lt nat.lt_wf)

instance : has_well_founded (polynomial R) := ⟨_, degree_lt_wf⟩

/-- `nat_degree p` forces `degree p` to ℕ, by defining nat_degree 0 = 0. -/
def nat_degree (p : polynomial R) : ℕ := (degree p).get_or_else 0

/-- `leading_coeff p` gives the coefficient of the highest power of `X` in `p`-/
def leading_coeff (p : polynomial R) : R := coeff p (nat_degree p)

/-- a polynomial is `monic` if its leading coefficient is 1 -/
def monic (p : polynomial R) := leading_coeff p = (1 : R)

lemma monic.def : monic p ↔ leading_coeff p = 1 := iff.rfl

instance monic.decidable [decidable_eq R] : decidable (monic p) :=
by unfold monic; apply_instance

@[simp] lemma monic.leading_coeff {p : polynomial R} (hp : p.monic) :
  leading_coeff p = 1 := hp

@[simp] lemma degree_zero : degree (0 : polynomial R) = ⊥ := rfl

@[simp] lemma nat_degree_zero : nat_degree (0 : polynomial R) = 0 := rfl

lemma degree_eq_bot : degree p = ⊥ ↔ p = 0 :=
⟨λ h, by rw [degree, ← max_eq_sup_with_bot] at h;
  exact support_eq_empty.1 (max_eq_none.1 h),
λ h, h.symm ▸ rfl⟩

lemma degree_eq_nat_degree (hp : p ≠ 0) : degree p = (nat_degree p : with_bot ℕ) :=
let ⟨n, hn⟩ :=
  classical.not_forall.1 (mt option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hp)) in
have hn : degree p = some n := not_not.1 hn,
by rw [nat_degree, hn]; refl

lemma degree_eq_iff_nat_degree_eq {p : polynomial R} {n : ℕ} (hp : p ≠ 0) :
  p.degree = n ↔ p.nat_degree = n :=
by rw [degree_eq_nat_degree hp, with_bot.coe_eq_coe]

lemma degree_eq_iff_nat_degree_eq_of_pos {p : polynomial R} {n : ℕ} (hn : n > 0) :
  p.degree = n ↔ p.nat_degree = n :=
begin
  split,
  { intro H, rwa ← degree_eq_iff_nat_degree_eq, rintro rfl,
    rw degree_zero at H, exact option.no_confusion H },
  { intro H, rwa degree_eq_iff_nat_degree_eq, rintro rfl,
    rw nat_degree_zero at H, rw H at hn, exact lt_irrefl _ hn }
end

lemma nat_degree_eq_of_degree_eq_some {p : polynomial R} {n : ℕ}
  (h : degree p = n) : nat_degree p = n :=
have hp0 : p ≠ 0, from λ hp0, by rw hp0 at h; exact option.no_confusion h,
option.some_inj.1 $ show (nat_degree p : with_bot ℕ) = n,
  by rwa [← degree_eq_nat_degree hp0]

@[simp] lemma degree_le_nat_degree : degree p ≤ nat_degree p :=
begin
  by_cases hp : p = 0, { rw hp, exact bot_le },
  rw [degree_eq_nat_degree hp],
  exact le_refl _
end

lemma nat_degree_eq_of_degree_eq [semiring S] {q : polynomial S} (h : degree p = degree q) :
nat_degree p = nat_degree q :=
by unfold nat_degree; rw h

lemma le_degree_of_ne_zero (h : coeff p n ≠ 0) : (n : with_bot ℕ) ≤ degree p :=
show @has_le.le (with_bot ℕ) _ (some n : with_bot ℕ) (p.support.sup some : with_bot ℕ),
from finset.le_sup (finsupp.mem_support_iff.2 h)

lemma le_nat_degree_of_ne_zero (h : coeff p n ≠ 0) : n ≤ nat_degree p :=
begin
  rw [← with_bot.coe_le_coe, ← degree_eq_nat_degree],
  exact le_degree_of_ne_zero h,
  { assume h, subst h, exact h rfl }
end

lemma degree_le_degree (h : coeff q (nat_degree p) ≠ 0) : degree p ≤ degree q :=
begin
  by_cases hp : p = 0,
  { rw hp, exact bot_le },
  { rw degree_eq_nat_degree hp, exact le_degree_of_ne_zero h }
end

lemma degree_ne_of_nat_degree_ne {n : ℕ} :
  p.nat_degree ≠ n → degree p ≠ n :=
@option.cases_on _ (λ d, d.get_or_else 0 ≠ n → d ≠ n) p.degree
  (λ _ h, option.no_confusion h)
  (λ n' h, mt option.some_inj.mp h)

theorem nat_degree_le_of_degree_le {n : ℕ} (H : degree p ≤ n) : nat_degree p ≤ n :=
show option.get_or_else (degree p) 0 ≤ n, from match degree p, H with
| none,     H := zero_le _
| (some d), H := with_bot.coe_le_coe.1 H
end

lemma nat_degree_le_nat_degree (hpq : p.degree ≤ q.degree) : p.nat_degree ≤ q.nat_degree :=
begin
  by_cases hp : p = 0, { rw [hp, nat_degree_zero], exact zero_le _ },
  by_cases hq : q = 0, { rw [hq, degree_zero, le_bot_iff, degree_eq_bot] at hpq, cc },
  rwa [degree_eq_nat_degree hp, degree_eq_nat_degree hq, with_bot.coe_le_coe] at hpq
end

@[simp] lemma degree_C (ha : a ≠ 0) : degree (C a) = (0 : with_bot ℕ) :=
show sup (ite (a = 0) ∅ {0}) some = 0, by rw if_neg ha; refl

lemma degree_C_le : degree (C a) ≤ (0 : with_bot ℕ) :=
by by_cases h : a = 0; [rw [h, C_0], rw [degree_C h]]; [exact bot_le, exact le_refl _]

lemma degree_one_le : degree (1 : polynomial R) ≤ (0 : with_bot ℕ) :=
by rw [← C_1]; exact degree_C_le

@[simp] lemma nat_degree_C (a : R) : nat_degree (C a) = 0 :=
begin
  by_cases ha : a = 0,
  { have : C a = 0, { rw [ha, C_0] },
    rw [nat_degree, degree_eq_bot.2 this],
    refl },
  { rw [nat_degree, degree_C ha], refl }
end

@[simp] lemma nat_degree_one : nat_degree (1 : polynomial R) = 0 := nat_degree_C 1

@[simp] lemma nat_degree_nat_cast (n : ℕ) : nat_degree (n : polynomial R) = 0 :=
by simp only [←C_eq_nat_cast, nat_degree_C]

@[simp] lemma degree_monomial (n : ℕ) (ha : a ≠ 0) : degree (C a * X ^ n) = n :=
by rw [← single_eq_C_mul_X, degree, monomial, support_single_ne_zero ha]; refl

lemma degree_monomial_le (n : ℕ) (a : R) : degree (C a * X ^ n) ≤ n :=
if h : a = 0 then by rw [h, C_0, zero_mul]; exact bot_le else le_of_eq (degree_monomial n h)

lemma coeff_eq_zero_of_degree_lt (h : degree p < n) : coeff p n = 0 :=
not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))

lemma coeff_eq_zero_of_nat_degree_lt {p : polynomial R} {n : ℕ} (h : p.nat_degree < n) :
  p.coeff n = 0 :=
begin
  apply coeff_eq_zero_of_degree_lt,
  by_cases hp : p = 0,
  { subst hp, exact with_bot.bot_lt_coe n },
  { rwa [degree_eq_nat_degree hp, with_bot.coe_lt_coe] }
end

@[simp] lemma coeff_nat_degree_succ_eq_zero {p : polynomial R} : p.coeff (p.nat_degree + 1) = 0 :=
coeff_eq_zero_of_nat_degree_lt (lt_add_one _)

-- We need the explicit `decidable` argument here because an exotic one shows up in a moment!
lemma ite_le_nat_degree_coeff (p : polynomial R) (n : ℕ) (I : decidable (n < 1 + nat_degree p)) :
  @ite (n < 1 + nat_degree p) I _ (coeff p n) 0 = coeff p n :=
begin
  split_ifs,
  { refl },
  { exact (coeff_eq_zero_of_nat_degree_lt (not_le.1 (λ w, h (nat.lt_one_add_iff.2 w)))).symm, }
end

lemma coeff_ne_zero_of_eq_degree (hn : degree p = n) :
  coeff p n ≠ 0 :=
λ h, mem_support_iff.mp (mem_of_max hn) h

lemma eq_X_add_C_of_degree_le_one (h : degree p ≤ 1) :
  p = C (p.coeff 1) * X + C (p.coeff 0) :=
ext (λ n, nat.cases_on n (by simp)
  (λ n, nat.cases_on n (by simp [coeff_C])
    (λ m, have degree p < m.succ.succ, from lt_of_le_of_lt h dec_trivial,
      by simp [coeff_eq_zero_of_degree_lt this, coeff_C, nat.succ_ne_zero, coeff_X,
        nat.succ_inj', @eq_comm ℕ 0])))

lemma eq_X_add_C_of_degree_eq_one (h : degree p = 1) :
  p = C (p.leading_coeff) * X + C (p.coeff 0) :=
(eq_X_add_C_of_degree_le_one (show degree p ≤ 1, from h ▸ le_refl _)).trans
  (by simp [leading_coeff, nat_degree_eq_of_degree_eq_some h])

theorem degree_C_mul_X_pow_le (r : R) (n : ℕ) : degree (C r * X^n) ≤ n :=
begin
  rw [← single_eq_C_mul_X],
  refine finset.sup_le (λ b hb, _),
  rw list.eq_of_mem_singleton (finsupp.support_single_subset hb),
  exact le_refl _
end

theorem degree_X_pow_le (n : ℕ) : degree (X^n : polynomial R) ≤ n :=
by simpa only [C_1, one_mul] using degree_C_mul_X_pow_le (1:R) n

theorem degree_X_le : degree (X : polynomial R) ≤ 1 :=
by simpa only [C_1, one_mul, pow_one] using degree_C_mul_X_pow_le (1:R) 1

lemma nat_degree_X_le : (X : polynomial R).nat_degree ≤ 1 :=
nat_degree_le_of_degree_le degree_X_le

end semiring


section nonzero_semiring
variables [semiring R] [nontrivial R] {p q : polynomial R}

@[simp] lemma degree_one : degree (1 : polynomial R) = (0 : with_bot ℕ) :=
degree_C (show (1 : R) ≠ 0, from zero_ne_one.symm)

@[simp] lemma degree_X : degree (X : polynomial R) = 1 :=
begin
  unfold X degree monomial single finsupp.support,
  rw if_neg (one_ne_zero : (1 : R) ≠ 0),
  refl
end

@[simp] lemma nat_degree_X : (X : polynomial R).nat_degree = 1 :=
nat_degree_eq_of_degree_eq_some degree_X

end nonzero_semiring


section ring
variables [ring R]


lemma coeff_mul_X_sub_C {p : polynomial R} {r : R} {a : ℕ} :
  coeff (p * (X - C r)) (a + 1) = coeff p a - coeff p (a + 1) * r :=
by simp [mul_sub]


@[simp]
lemma C_eq_int_cast (n : ℤ) : C ↑n = (n : polynomial R) :=
(C : R →+* _).map_int_cast n

@[simp] lemma degree_neg (p : polynomial R) : degree (-p) = degree p :=
by unfold degree; rw support_neg

@[simp] lemma nat_degree_neg (p : polynomial R) : nat_degree (-p) = nat_degree p :=
by simp [nat_degree]

@[simp] lemma nat_degree_int_cast (n : ℤ) : nat_degree (n : polynomial R) = 0 :=
by simp only [←C_eq_int_cast, nat_degree_C]

end ring

section semiring
variables [semiring R]

/-- The second-highest coefficient, or 0 for constants -/
def next_coeff (p : polynomial R) : R :=
if p.nat_degree = 0 then 0 else p.coeff (p.nat_degree - 1)

@[simp]
lemma next_coeff_C_eq_zero (c : R) :
  next_coeff (C c) = 0 := by { rw next_coeff, simp }

lemma next_coeff_of_pos_nat_degree (p : polynomial R) (hp : 0 < p.nat_degree) :
  next_coeff p = p.coeff (p.nat_degree - 1) :=
by { rw [next_coeff, if_neg], contrapose! hp, simpa }
end semiring


end polynomial
