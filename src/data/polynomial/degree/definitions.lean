/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.nat.with_bot
import data.polynomial.induction
import data.polynomial.monomial

/-!
# Theory of univariate polynomials

The definitions include
`degree`, `monic`, `leading_coeff`

Results include
- `degree_mul` : The degree of the product is the sum of degrees
- `leading_coeff_add_of_degree_eq` and `leading_coeff_add_of_degree_lt` :
    The leading_coefficient of a sum is determined by the leading coefficients and degrees
-/

noncomputable theory

open finsupp finset
open_locale big_operators classical

namespace polynomial
universes u v
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

@[nontriviality] lemma monic_of_subsingleton [subsingleton R] (p : polynomial R) : monic p :=
subsingleton.elim _ _

lemma monic.def : monic p ↔ leading_coeff p = 1 := iff.rfl

instance monic.decidable [decidable_eq R] : decidable (monic p) :=
by unfold monic; apply_instance

@[simp] lemma monic.leading_coeff {p : polynomial R} (hp : p.monic) :
  leading_coeff p = 1 := hp

lemma monic.coeff_nat_degree {p : polynomial R} (hp : p.monic) : p.coeff p.nat_degree = 1 := hp

@[simp] lemma degree_zero : degree (0 : polynomial R) = ⊥ := rfl

@[simp] lemma nat_degree_zero : nat_degree (0 : polynomial R) = 0 := rfl

@[simp] lemma coeff_nat_degree : coeff p (nat_degree p) = leading_coeff p := rfl

lemma degree_eq_bot : degree p = ⊥ ↔ p = 0 :=
⟨λ h, by rw [degree, ← max_eq_sup_with_bot] at h;
  exact support_eq_empty.1 (max_eq_none.1 h),
λ h, h.symm ▸ rfl⟩

@[nontriviality] lemma degree_of_subsingleton [subsingleton R] : degree p = ⊥ :=
by rw [subsingleton.elim p 0, degree_zero]

@[nontriviality] lemma nat_degree_of_subsingleton [subsingleton R] : nat_degree p = 0 :=
by rw [subsingleton.elim p 0, nat_degree_zero]

lemma degree_eq_nat_degree (hp : p ≠ 0) : degree p = (nat_degree p : with_bot ℕ) :=
let ⟨n, hn⟩ :=
  not_forall.1 (mt option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hp)) in
have hn : degree p = some n := not_not.1 hn,
by rw [nat_degree, hn]; refl

lemma degree_eq_iff_nat_degree_eq {p : polynomial R} {n : ℕ} (hp : p ≠ 0) :
  p.degree = n ↔ p.nat_degree = n :=
by rw [degree_eq_nat_degree hp, with_bot.coe_eq_coe]

lemma degree_eq_iff_nat_degree_eq_of_pos {p : polynomial R} {n : ℕ} (hn : 0 < n) :
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
with_bot.gi_get_or_else_bot.gc.le_u_l _

lemma nat_degree_eq_of_degree_eq [semiring S] {q : polynomial S} (h : degree p = degree q) :
  nat_degree p = nat_degree q :=
by unfold nat_degree; rw h

lemma le_degree_of_ne_zero (h : coeff p n ≠ 0) : (n : with_bot ℕ) ≤ degree p :=
show @has_le.le (with_bot ℕ) _ (some n : with_bot ℕ) (p.support.sup some : with_bot ℕ),
from finset.le_sup (mem_support_iff.2 h)

lemma le_nat_degree_of_ne_zero (h : coeff p n ≠ 0) : n ≤ nat_degree p :=
begin
  rw [← with_bot.coe_le_coe, ← degree_eq_nat_degree],
  exact le_degree_of_ne_zero h,
  { assume h, subst h, exact h rfl }
end

lemma le_nat_degree_of_mem_supp (a : ℕ) :
  a ∈ p.support → a ≤ nat_degree p:=
le_nat_degree_of_ne_zero ∘ mem_support_iff.mp

lemma supp_subset_range (h : nat_degree p < m) : p.support ⊆ finset.range m :=
λ n hn, mem_range.2 $ (le_nat_degree_of_mem_supp _ hn).trans_lt h

lemma supp_subset_range_nat_degree_succ : p.support ⊆ finset.range (nat_degree p + 1) :=
supp_subset_range (nat.lt_succ_self _)

lemma degree_le_degree (h : coeff q (nat_degree p) ≠ 0) : degree p ≤ degree q :=
begin
  by_cases hp : p = 0,
  { rw hp, exact bot_le },
  { rw degree_eq_nat_degree hp, exact le_degree_of_ne_zero h }
end

lemma degree_ne_of_nat_degree_ne {n : ℕ} :
  p.nat_degree ≠ n → degree p ≠ n :=
mt $ λ h, by rw [nat_degree, h, option.get_or_else_coe]

theorem nat_degree_le_iff_degree_le {n : ℕ} : nat_degree p ≤ n ↔ degree p ≤ n :=
with_bot.get_or_else_bot_le_iff

alias polynomial.nat_degree_le_iff_degree_le ↔ . .

lemma nat_degree_le_nat_degree [semiring S] {q : polynomial S} (hpq : p.degree ≤ q.degree) :
  p.nat_degree ≤ q.nat_degree :=
with_bot.gi_get_or_else_bot.gc.monotone_l hpq

@[simp] lemma degree_C (ha : a ≠ 0) : degree (C a) = (0 : with_bot ℕ) :=
by { rw [degree, ← monomial_zero_left, support_monomial 0 _ ha, sup_singleton], refl }

lemma degree_C_le : degree (C a) ≤ 0 :=
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

@[simp] lemma degree_monomial (n : ℕ) (ha : a ≠ 0) : degree (monomial n a) = n :=
by rw [degree, support_monomial _ _ ha]; refl

@[simp] lemma degree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) : degree (C a * X ^ n) = n :=
by rw [← monomial_eq_C_mul_X, degree_monomial n ha]

lemma degree_monomial_le (n : ℕ) (a : R) : degree (monomial n a) ≤ n :=
if h : a = 0 then by rw [h, (monomial n).map_zero]; exact bot_le else le_of_eq (degree_monomial n h)

lemma degree_C_mul_X_pow_le (n : ℕ) (a : R) : degree (C a * X ^ n) ≤ n :=
by { rw C_mul_X_pow_eq_monomial, apply degree_monomial_le }

lemma degree_C_mul_X_le (a : R) : degree (C a * X) ≤ 1 :=
by simpa only [pow_one] using degree_C_mul_X_pow_le 1 a

@[simp] lemma nat_degree_C_mul_X_pow (n : ℕ) (a : R) (ha : a ≠ 0) : nat_degree (C a * X ^ n) = n :=
nat_degree_eq_of_degree_eq_some (degree_C_mul_X_pow n ha)

@[simp] lemma nat_degree_C_mul_X (a : R) (ha : a ≠ 0) : nat_degree (C a * X) = 1 :=
by simpa only [pow_one] using nat_degree_C_mul_X_pow 1 a ha

@[simp] lemma nat_degree_monomial (i : ℕ) (r : R) (hr : r ≠ 0) :
  nat_degree (monomial i r) = i :=
by rw [← C_mul_X_pow_eq_monomial, nat_degree_C_mul_X_pow i r hr]

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
  @ite _ (n < 1 + nat_degree p) I (coeff p n) 0 = coeff p n :=
begin
  split_ifs,
  { refl },
  { exact (coeff_eq_zero_of_nat_degree_lt (not_le.1 (λ w, h (nat.lt_one_add_iff.2 w)))).symm, }
end

lemma as_sum_support (p : polynomial R) :
  p = ∑ i in p.support, monomial i (p.coeff i) :=
(sum_monomial_eq p).symm

lemma as_sum_support_C_mul_X_pow (p : polynomial R) :
  p = ∑ i in p.support, C (p.coeff i) * X^i :=
trans p.as_sum_support $ by simp only [C_mul_X_pow_eq_monomial]

/--
We can reexpress a sum over `p.support` as a sum over `range n`,
for any `n` satisfying `p.nat_degree < n`.
-/
lemma sum_over_range' [add_comm_monoid S] (p : polynomial R) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0)
  (n : ℕ) (w : p.nat_degree < n) :
  p.sum f = ∑ (a : ℕ) in range n, f a (coeff p a) :=
begin
  rcases p,
  have := supp_subset_range w,
  simp only [polynomial.sum, support, coeff, nat_degree, degree] at ⊢ this,
  exact finsupp.sum_of_support_subset _ this _ (λ n hn, h n)
end

/--
We can reexpress a sum over `p.support` as a sum over `range (p.nat_degree + 1)`.
-/
lemma sum_over_range [add_comm_monoid S] (p : polynomial R) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) :
  p.sum f = ∑ (a : ℕ) in range (p.nat_degree + 1), f a (coeff p a) :=
sum_over_range' p h (p.nat_degree + 1) (lt_add_one _)

lemma as_sum_range' (p : polynomial R) (n : ℕ) (w : p.nat_degree < n) :
  p = ∑ i in range n, monomial i (coeff p i) :=
p.sum_monomial_eq.symm.trans $ p.sum_over_range' monomial_zero_right _ w

lemma as_sum_range (p : polynomial R) :
  p = ∑ i in range (p.nat_degree + 1), monomial i (coeff p i) :=
p.sum_monomial_eq.symm.trans $ p.sum_over_range $ monomial_zero_right

lemma as_sum_range_C_mul_X_pow (p : polynomial R) :
  p = ∑ i in range (p.nat_degree + 1), C (coeff p i) * X ^ i :=
p.as_sum_range.trans $ by simp only [C_mul_X_pow_eq_monomial]

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

lemma eq_X_add_C_of_nat_degree_le_one (h : nat_degree p ≤ 1) :
  p = C (p.coeff 1) * X + C (p.coeff 0) :=
eq_X_add_C_of_degree_le_one $ degree_le_of_nat_degree_le h

lemma exists_eq_X_add_C_of_nat_degree_le_one (h : nat_degree p ≤ 1) :
  ∃ a b, p = C a * X + C b :=
⟨p.coeff 1, p.coeff 0, eq_X_add_C_of_nat_degree_le_one h⟩

theorem degree_X_pow_le (n : ℕ) : degree (X^n : polynomial R) ≤ n :=
by simpa only [C_1, one_mul] using degree_C_mul_X_pow_le n (1:R)

theorem degree_X_le : degree (X : polynomial R) ≤ 1 :=
degree_monomial_le _ _

lemma nat_degree_X_le : (X : polynomial R).nat_degree ≤ 1 :=
nat_degree_le_of_degree_le degree_X_le

lemma support_C_mul_X_pow (c : R) (n : ℕ) : (C c * X ^ n).support ⊆ singleton n :=
begin
  rw [C_mul_X_pow_eq_monomial],
  exact support_monomial' _ _
end

lemma mem_support_C_mul_X_pow {n a : ℕ} {c : R} (h : a ∈ (C c * X ^ n).support) : a = n :=
mem_singleton.1 $ support_C_mul_X_pow _ _ h

lemma card_support_C_mul_X_pow_le_one {c : R} {n : ℕ} : (C c * X ^ n).support.card ≤ 1 :=
begin
  rw ← card_singleton n,
  apply card_le_of_subset (support_C_mul_X_pow c n),
end

lemma card_supp_le_succ_nat_degree (p : polynomial R) : p.support.card ≤ p.nat_degree + 1 :=
begin
  rw ← finset.card_range (p.nat_degree + 1),
  exact finset.card_le_of_subset supp_subset_range_nat_degree_succ,
end

lemma le_degree_of_mem_supp (a : ℕ) :
  a ∈ p.support → ↑a ≤ degree p :=
le_degree_of_ne_zero ∘ mem_support_iff.mp

lemma nonempty_support_iff : p.support.nonempty ↔ p ≠ 0 :=
by rw [ne.def, nonempty_iff_ne_empty, ne.def, ← support_eq_empty]

lemma support_C_mul_X_pow_nonzero {c : R} {n : ℕ} (h : c ≠ 0) :
  (C c * X ^ n).support = singleton n :=
begin
  rw [C_mul_X_pow_eq_monomial],
  exact support_monomial _ _ h
end

end semiring

section nonzero_semiring
variables [semiring R] [nontrivial R] {p q : polynomial R}

@[simp] lemma degree_one : degree (1 : polynomial R) = (0 : with_bot ℕ) :=
degree_C (show (1 : R) ≠ 0, from zero_ne_one.symm)

@[simp] lemma degree_X : degree (X : polynomial R) = 1 :=
degree_monomial _ one_ne_zero

@[simp] lemma nat_degree_X : (X : polynomial R).nat_degree = 1 :=
nat_degree_eq_of_degree_eq_some degree_X

end nonzero_semiring

section ring
variables [ring R]

lemma coeff_mul_X_sub_C {p : polynomial R} {r : R} {a : ℕ} :
  coeff (p * (X - C r)) (a + 1) = coeff p a - coeff p (a + 1) * r :=
by simp [mul_sub]

lemma C_eq_int_cast (n : ℤ) : C (n : R) = n :=
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

section semiring
variables [semiring R] {p q : polynomial R} {ι : Type*}

lemma coeff_nat_degree_eq_zero_of_degree_lt (h : degree p < degree q) :
  coeff p (nat_degree q) = 0 :=
coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h degree_le_nat_degree)

lemma ne_zero_of_degree_gt {n : with_bot ℕ} (h : n < degree p) : p ≠ 0 :=
mt degree_eq_bot.2 (ne.symm (ne_of_lt (lt_of_le_of_lt bot_le h)))

lemma ne_zero_of_degree_ge_degree (hpq : p.degree ≤ q.degree) (hp : p ≠ 0) : q ≠ 0 :=
polynomial.ne_zero_of_degree_gt (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr
  (by rwa [ne.def, polynomial.degree_eq_bot])) hpq : q.degree > ⊥)

lemma ne_zero_of_nat_degree_gt {n : ℕ} (h : n < nat_degree p) : p ≠ 0 :=
λ H, by simpa [H, nat.not_lt_zero] using h

lemma degree_lt_degree (h : nat_degree p < nat_degree q) : degree p < degree q :=
begin
  by_cases hp : p = 0,
  { simp [hp],
    rw bot_lt_iff_ne_bot,
    intro hq,
    simpa [hp, degree_eq_bot.mp hq, lt_irrefl] using h },
  { rw [degree_eq_nat_degree hp, degree_eq_nat_degree $ ne_zero_of_nat_degree_gt h],
    exact_mod_cast h }
end

lemma nat_degree_lt_nat_degree_iff (hp : p ≠ 0) :
  nat_degree p < nat_degree q ↔ degree p < degree q :=
⟨degree_lt_degree, begin
  intro h,
  have hq : q ≠ 0 := ne_zero_of_degree_gt h,
  rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq] at h,
  exact_mod_cast h
end⟩

lemma eq_C_of_degree_le_zero (h : degree p ≤ 0) : p = C (coeff p 0) :=
begin
  ext (_|n), { simp },
  rw [coeff_C, if_neg (nat.succ_ne_zero _), coeff_eq_zero_of_degree_lt],
  exact h.trans_lt (with_bot.some_lt_some.2 n.succ_pos),
end

lemma eq_C_of_degree_eq_zero (h : degree p = 0) : p = C (coeff p 0) :=
eq_C_of_degree_le_zero (h ▸ le_refl _)

lemma degree_le_zero_iff : degree p ≤ 0 ↔ p = C (coeff p 0) :=
⟨eq_C_of_degree_le_zero, λ h, h.symm ▸ degree_C_le⟩

lemma degree_add_le (p q : polynomial R) : degree (p + q) ≤ max (degree p) (degree q) :=
calc degree (p + q) = ((p + q).support).sup some : rfl
  ... ≤ (p.support ∪ q.support).sup some : sup_mono support_add
  ... = p.support.sup some ⊔ q.support.sup some : sup_union

lemma nat_degree_add_le (p q : polynomial R) :
  nat_degree (p + q) ≤ max (nat_degree p) (nat_degree q) :=
begin
  cases le_max_iff.1 (degree_add_le p q);
  simp [nat_degree_le_nat_degree h]
end

@[simp] lemma leading_coeff_zero : leading_coeff (0 : polynomial R) = 0 := rfl

@[simp] lemma leading_coeff_eq_zero : leading_coeff p = 0 ↔ p = 0 :=
⟨λ h, by_contradiction $ λ hp, mt mem_support_iff.1
  (not_not.2 h) (mem_of_max (degree_eq_nat_degree hp)),
λ h, h.symm ▸ leading_coeff_zero⟩

lemma leading_coeff_ne_zero : leading_coeff p ≠ 0 ↔ p ≠ 0 :=
by rw [ne.def, leading_coeff_eq_zero]

lemma leading_coeff_eq_zero_iff_deg_eq_bot : leading_coeff p = 0 ↔ degree p = ⊥ :=
by rw [leading_coeff_eq_zero, degree_eq_bot]

lemma nat_degree_mem_support_of_nonzero (H : p ≠ 0) : p.nat_degree ∈ p.support :=
by { rw mem_support_iff, exact (not_congr leading_coeff_eq_zero).mpr H }

lemma nat_degree_eq_support_max' (h : p ≠ 0) :
  p.nat_degree = p.support.max' (nonempty_support_iff.mpr h) :=
(le_max' _ _ $ nat_degree_mem_support_of_nonzero h).antisymm $
  max'_le _ _ _ le_nat_degree_of_mem_supp

lemma nat_degree_C_mul_X_pow_le (a : R) (n : ℕ) : nat_degree (C a * X ^ n) ≤ n :=
nat_degree_le_iff_degree_le.2 $ degree_C_mul_X_pow_le _ _

lemma degree_add_eq_left_of_degree_lt (h : degree q < degree p) : degree (p + q) = degree p :=
le_antisymm (max_eq_left_of_lt h ▸ degree_add_le _ _) $ degree_le_degree $
  begin
    rw [coeff_add, coeff_nat_degree_eq_zero_of_degree_lt h, add_zero],
    exact mt leading_coeff_eq_zero.1 (ne_zero_of_degree_gt h)
  end

lemma degree_add_eq_right_of_degree_lt (h : degree p < degree q) : degree (p + q) = degree q :=
by rw [add_comm, degree_add_eq_left_of_degree_lt h]

lemma degree_add_C (hp : 0 < degree p) : degree (p + C a) = degree p :=
add_comm (C a) p ▸ degree_add_eq_right_of_degree_lt $ lt_of_le_of_lt degree_C_le hp

lemma degree_add_eq_of_leading_coeff_add_ne_zero (h : leading_coeff p + leading_coeff q ≠ 0) :
  degree (p + q) = max p.degree q.degree :=
le_antisymm (degree_add_le _ _) $
  match lt_trichotomy (degree p) (degree q) with
  | or.inl hlt :=
    by rw [degree_add_eq_right_of_degree_lt hlt, max_eq_right_of_lt hlt]; exact le_refl _
  | or.inr (or.inl heq) :=
    le_of_not_gt $
      assume hlt : max (degree p) (degree q) > degree (p + q),
      h $ show leading_coeff p + leading_coeff q = 0,
      begin
        rw [heq, max_self] at hlt,
        rw [leading_coeff, leading_coeff, nat_degree_eq_of_degree_eq heq, ← coeff_add],
        exact coeff_nat_degree_eq_zero_of_degree_lt hlt
      end
  | or.inr (or.inr hlt) :=
    by rw [degree_add_eq_left_of_degree_lt hlt, max_eq_left_of_lt hlt]; exact le_refl _
  end

lemma degree_erase_le (p : polynomial R) (n : ℕ) : degree (p.erase n) ≤ degree p :=
by { rcases p, simp only [erase, degree, coeff, support], convert sup_mono (erase_subset _ _) }

lemma degree_erase_lt (hp : p ≠ 0) : degree (p.erase (nat_degree p)) < degree p :=
begin
  apply lt_of_le_of_ne (degree_erase_le _ _),
  rw [degree_eq_nat_degree hp, degree, support_erase],
  exact λ h, not_mem_erase _ _ (mem_of_max h),
end

lemma degree_update_le (p : polynomial R) (n : ℕ) (a : R) :
  degree (p.update n a) ≤ max (degree p) n :=
begin
  simp only [degree, coeff_update_apply, le_max_iff, finset.sup_le_iff, mem_support_iff],
  intros b hb,
  split_ifs at hb with h,
  { subst b,
    exact or.inr le_rfl },
  { exact or.inl (le_degree_of_ne_zero hb) }
end

lemma degree_sum_le (s : finset ι) (f : ι → polynomial R) :
  degree (∑ i in s, f i) ≤ s.sup (λ b, degree (f b)) :=
finset.induction_on s (by simp only [sum_empty, sup_empty, degree_zero, le_refl]) $
  assume a s has ih,
  calc degree (∑ i in insert a s, f i) ≤ max (degree (f a)) (degree (∑ i in s, f i)) :
    by rw sum_insert has; exact degree_add_le _ _
  ... ≤ _ : by rw [sup_insert, sup_eq_max]; exact max_le_max le_rfl ih

lemma degree_mul_le (p q : polynomial R) : degree (p * q) ≤ degree p + degree q :=
calc degree (p * q) ≤ (p.support).sup (λi, degree (sum q (λj a, C (coeff p i * a) * X ^ (i + j)))) :
    begin
      simp only [monomial_eq_C_mul_X.symm],
      convert degree_sum_le _ _,
      exact mul_eq_sum_sum
    end
  ... ≤ p.support.sup (λi, q.support.sup (λj, degree (C (coeff p i * coeff q j) * X ^ (i + j)))) :
    finset.sup_mono_fun (assume i hi,  degree_sum_le _ _)
  ... ≤ degree p + degree q :
    begin
      refine finset.sup_le (λ a ha, finset.sup_le (λ b hb, le_trans (degree_C_mul_X_pow_le _ _) _)),
      rw [with_bot.coe_add],
      rw mem_support_iff at ha hb,
      exact add_le_add (le_degree_of_ne_zero ha) (le_degree_of_ne_zero hb)
    end

lemma degree_pow_le (p : polynomial R) : ∀ (n : ℕ), degree (p ^ n) ≤ n • (degree p)
| 0     := by rw [pow_zero, zero_nsmul]; exact degree_one_le
| (n+1) := calc degree (p ^ (n + 1)) ≤ degree p + degree (p ^ n) :
    by rw pow_succ; exact degree_mul_le _ _
  ... ≤ _ : by rw succ_nsmul; exact add_le_add (le_refl _) (degree_pow_le _)

@[simp] lemma leading_coeff_monomial (a : R) (n : ℕ) : leading_coeff (monomial n a) = a :=
begin
  by_cases ha : a = 0,
  { simp only [ha, (monomial n).map_zero, leading_coeff_zero] },
  { rw [leading_coeff, nat_degree_monomial _ _ ha, coeff_monomial], simp }
end

lemma leading_coeff_C_mul_X_pow (a : R) (n : ℕ) : leading_coeff (C a * X ^ n) = a :=
by rw [C_mul_X_pow_eq_monomial, leading_coeff_monomial]

@[simp] lemma leading_coeff_C (a : R) : leading_coeff (C a) = a :=
leading_coeff_monomial a 0

@[simp] lemma leading_coeff_X_pow (n : ℕ) : leading_coeff ((X : polynomial R) ^ n) = 1 :=
by simpa only [C_1, one_mul] using leading_coeff_C_mul_X_pow (1 : R) n

@[simp] lemma leading_coeff_X : leading_coeff (X : polynomial R) = 1 :=
by simpa only [pow_one] using @leading_coeff_X_pow R _ 1

@[simp] lemma monic_X_pow (n : ℕ) : monic (X ^ n : polynomial R) := leading_coeff_X_pow n

@[simp] lemma monic_X : monic (X : polynomial R) := leading_coeff_X

@[simp] lemma leading_coeff_one : leading_coeff (1 : polynomial R) = 1 :=
leading_coeff_C 1

@[simp] lemma monic_one : monic (1 : polynomial R) := leading_coeff_C _

lemma monic.ne_zero {R : Type*} [semiring R] [nontrivial R] {p : polynomial R} (hp : p.monic) :
  p ≠ 0 :=
by { rintro rfl, simpa [monic] using hp }

lemma monic.ne_zero_of_ne (h : (0:R) ≠ 1) {p : polynomial R} (hp : p.monic) :
  p ≠ 0 :=
by { nontriviality R, exact hp.ne_zero }

lemma monic.ne_zero_of_polynomial_ne {r} (hp : monic p) (hne : q ≠ r) : p ≠ 0 :=
by { haveI := nontrivial.of_polynomial_ne hne, exact hp.ne_zero }

lemma leading_coeff_add_of_degree_lt (h : degree p < degree q) :
  leading_coeff (p + q) = leading_coeff q :=
have coeff p (nat_degree q) = 0, from coeff_nat_degree_eq_zero_of_degree_lt h,
by simp only [leading_coeff, nat_degree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h),
  this, coeff_add, zero_add]

lemma leading_coeff_add_of_degree_eq (h : degree p = degree q)
  (hlc : leading_coeff p + leading_coeff q ≠ 0) :
  leading_coeff (p + q) = leading_coeff p + leading_coeff q :=
have nat_degree (p + q) = nat_degree p,
  by apply nat_degree_eq_of_degree_eq;
    rw [degree_add_eq_of_leading_coeff_add_ne_zero hlc, h, max_self],
by simp only [leading_coeff, this, nat_degree_eq_of_degree_eq h, coeff_add]

@[simp] lemma coeff_mul_degree_add_degree (p q : polynomial R) :
  coeff (p * q) (nat_degree p + nat_degree q) = leading_coeff p * leading_coeff q :=
calc coeff (p * q) (nat_degree p + nat_degree q) =
    ∑ x in nat.antidiagonal (nat_degree p + nat_degree q),
    coeff p x.1 * coeff q x.2 : coeff_mul _ _ _
... = coeff p (nat_degree p) * coeff q (nat_degree q) :
  begin
    refine finset.sum_eq_single (nat_degree p, nat_degree q) _ _,
    { rintro ⟨i,j⟩ h₁ h₂, rw nat.mem_antidiagonal at h₁,
      by_cases H : nat_degree p < i,
      { rw [coeff_eq_zero_of_degree_lt
          (lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 H)), zero_mul] },
      { rw not_lt_iff_eq_or_lt at H, cases H,
        { subst H, rw add_left_cancel_iff at h₁, dsimp at h₁, subst h₁, exfalso, exact h₂ rfl },
        { suffices : nat_degree q < j,
          { rw [coeff_eq_zero_of_degree_lt
              (lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 this)), mul_zero] },
          { by_contra H', rw not_lt at H',
            exact ne_of_lt (nat.lt_of_lt_of_le
              (nat.add_lt_add_right H j) (nat.add_le_add_left H' _)) h₁ } } } },
    { intro H, exfalso, apply H, rw nat.mem_antidiagonal }
  end

lemma degree_mul' (h : leading_coeff p * leading_coeff q ≠ 0) :
  degree (p * q) = degree p + degree q :=
have hp : p ≠ 0 := by refine mt _ h; exact λ hp, by rw [hp, leading_coeff_zero, zero_mul],
have hq : q ≠ 0 := by refine mt _ h; exact λ hq, by rw [hq, leading_coeff_zero, mul_zero],
le_antisymm (degree_mul_le _ _)
begin
  rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq],
  refine le_degree_of_ne_zero _,
  rwa coeff_mul_degree_add_degree
end

lemma monic.degree_mul (hq : monic q) : degree (p * q) = degree p + degree q :=
if hp : p = 0 then by simp [hp]
else degree_mul' $ by rwa [hq.leading_coeff, mul_one, ne.def, leading_coeff_eq_zero]

lemma nat_degree_mul' (h : leading_coeff p * leading_coeff q ≠ 0) :
  nat_degree (p * q) = nat_degree p + nat_degree q :=
have hp : p ≠ 0 := mt leading_coeff_eq_zero.2 (λ h₁, h $ by rw [h₁, zero_mul]),
have hq : q ≠ 0 := mt leading_coeff_eq_zero.2 (λ h₁, h $ by rw [h₁, mul_zero]),
nat_degree_eq_of_degree_eq_some $
  by rw [degree_mul' h, with_bot.coe_add, degree_eq_nat_degree hp, degree_eq_nat_degree hq]

lemma leading_coeff_mul' (h : leading_coeff p * leading_coeff q ≠ 0) :
  leading_coeff (p * q) = leading_coeff p * leading_coeff q :=
begin
  unfold leading_coeff,
  rw [nat_degree_mul' h, coeff_mul_degree_add_degree],
  refl
end

lemma monomial_nat_degree_leading_coeff_eq_self (h : p.support.card ≤ 1) :
  monomial p.nat_degree p.leading_coeff = p :=
begin
  rcases card_support_le_one_iff_monomial.1 h with ⟨n, a, rfl⟩,
  by_cases ha : a = 0;
  simp [ha]
end

lemma C_mul_X_pow_eq_self (h : p.support.card ≤ 1) :
  C p.leading_coeff * X^p.nat_degree = p :=
by rw [C_mul_X_pow_eq_monomial, monomial_nat_degree_leading_coeff_eq_self h]

lemma leading_coeff_pow' : leading_coeff p ^ n ≠ 0 →
  leading_coeff (p ^ n) = leading_coeff p ^ n :=
nat.rec_on n (by simp) $
λ n ih h,
have h₁ : leading_coeff p ^ n ≠ 0 :=
  λ h₁, h $ by rw [pow_succ, h₁, mul_zero],
have h₂ : leading_coeff p * leading_coeff (p ^ n) ≠ 0 :=
  by rwa [pow_succ, ← ih h₁] at h,
by rw [pow_succ, pow_succ, leading_coeff_mul' h₂, ih h₁]

lemma degree_pow' : ∀ {n : ℕ}, leading_coeff p ^ n ≠ 0 →
  degree (p ^ n) = n • (degree p)
| 0     := λ h, by rw [pow_zero, ← C_1] at *;
  rw [degree_C h, zero_nsmul]
| (n+1) := λ h,
have h₁ : leading_coeff p ^ n ≠ 0 := λ h₁, h $
  by rw [pow_succ, h₁, mul_zero],
have h₂ : leading_coeff p * leading_coeff (p ^ n) ≠ 0 :=
  by rwa [pow_succ, ← leading_coeff_pow' h₁] at h,
by rw [pow_succ, degree_mul' h₂, succ_nsmul, degree_pow' h₁]

lemma nat_degree_pow' {n : ℕ} (h : leading_coeff p ^ n ≠ 0) :
  nat_degree (p ^ n) = n * nat_degree p :=
if hp0 : p = 0 then
  if hn0 : n = 0 then by simp *
  else by rw [hp0, zero_pow (nat.pos_of_ne_zero hn0)]; simp
else
have hpn : p ^ n ≠ 0, from λ hpn0,  have h1 : _ := h,
  by rw [← leading_coeff_pow' h1, hpn0, leading_coeff_zero] at h;
  exact h rfl,
option.some_inj.1 $ show (nat_degree (p ^ n) : with_bot ℕ) = (n * nat_degree p : ℕ),
  by rw [← degree_eq_nat_degree hpn, degree_pow' h, degree_eq_nat_degree hp0,
    ← with_bot.coe_nsmul]; simp

theorem leading_coeff_mul_monic {p q : polynomial R} (hq : monic q) :
  leading_coeff (p * q) = leading_coeff p :=
decidable.by_cases
  (λ H : leading_coeff p = 0, by rw [H, leading_coeff_eq_zero.1 H, zero_mul, leading_coeff_zero])
  (λ H : leading_coeff p ≠ 0,
    by rw [leading_coeff_mul', hq.leading_coeff, mul_one];
      rwa [hq.leading_coeff, mul_one])

@[simp] theorem leading_coeff_mul_X_pow {p : polynomial R} {n : ℕ} :
  leading_coeff (p * X ^ n) = leading_coeff p :=
leading_coeff_mul_monic (monic_X_pow n)

@[simp] theorem leading_coeff_mul_X {p : polynomial R} :
  leading_coeff (p * X) = leading_coeff p :=
leading_coeff_mul_monic monic_X

lemma nat_degree_mul_le {p q : polynomial R} : nat_degree (p * q) ≤ nat_degree p + nat_degree q :=
begin
  apply nat_degree_le_of_degree_le,
  apply le_trans (degree_mul_le p q),
  rw with_bot.coe_add,
  refine add_le_add _ _; apply degree_le_nat_degree,
end

lemma subsingleton_of_monic_zero (h : monic (0 : polynomial R)) :
  (∀ p q : polynomial R, p = q) ∧ (∀ a b : R, a = b) :=
by rw [monic.def, leading_coeff_zero] at h;
  exact ⟨λ p q, by rw [← mul_one p, ← mul_one q, ← C_1, ← h, C_0, mul_zero, mul_zero],
    λ a b, by rw [← mul_one a, ← mul_one b, ← h, mul_zero, mul_zero]⟩

lemma zero_le_degree_iff {p : polynomial R} : 0 ≤ degree p ↔ p ≠ 0 :=
by rw [ne.def, ← degree_eq_bot];
  cases degree p; exact dec_trivial

lemma degree_nonneg_iff_ne_zero : 0 ≤ degree p ↔ p ≠ 0 :=
⟨λ h0p hp0, absurd h0p (by rw [hp0, degree_zero]; exact dec_trivial),
  λ hp0, le_of_not_gt (λ h, by simp [gt, degree_eq_bot, *] at *)⟩

lemma nat_degree_eq_zero_iff_degree_le_zero : p.nat_degree = 0 ↔ p.degree ≤ 0 :=
by rw [← nonpos_iff_eq_zero, nat_degree_le_iff_degree_le, with_bot.coe_zero]

theorem degree_le_iff_coeff_zero (f : polynomial R) (n : with_bot ℕ) :
  degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 :=
⟨λ (H : finset.sup (f.support) some ≤ n) m (Hm : n < (m : with_bot ℕ)), decidable.of_not_not $ λ H4,
  have H1 : m ∉ f.support,
    from λ H2, not_lt_of_ge ((finset.sup_le_iff.1 H) m H2 : ((m : with_bot ℕ) ≤ n)) Hm,
  H1 $ mem_support_iff.2 H4,
λ H, finset.sup_le $ λ b Hb, decidable.of_not_not $ λ Hn,
  mem_support_iff.1 Hb $ H b $ lt_of_not_ge Hn⟩

theorem degree_lt_iff_coeff_zero (f : polynomial R) (n : ℕ) :
  degree f < n ↔ ∀ m : ℕ, n ≤ m → coeff f m = 0 :=
begin
  refine ⟨λ hf m hm, coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hf (with_bot.coe_le_coe.2 hm)), _⟩,
  simp only [degree, finset.sup_lt_iff (with_bot.bot_lt_coe n), mem_support_iff,
    with_bot.some_eq_coe, with_bot.coe_lt_coe, ← @not_le ℕ],
  exact λ h m, mt (h m),
end

lemma degree_smul_le (a : R) (p : polynomial R) : degree (a • p) ≤ degree p :=
begin
  apply (degree_le_iff_coeff_zero _ _).2 (λ m hm, _),
  rw degree_lt_iff_coeff_zero at hm,
  simp [hm m (le_refl _)],
end

lemma nat_degree_smul_le (a : R) (p : polynomial R) : nat_degree (a • p) ≤ nat_degree p :=
nat_degree_le_nat_degree (degree_smul_le a p)

lemma degree_lt_degree_mul_X (hp : p ≠ 0) : p.degree < (p * X).degree :=
by haveI := nontrivial.of_polynomial_ne hp; exact
have leading_coeff p * leading_coeff X ≠ 0, by simpa,
by erw [degree_mul' this, degree_eq_nat_degree hp,
    degree_X, ← with_bot.coe_one, ← with_bot.coe_add, with_bot.coe_lt_coe];
  exact nat.lt_succ_self _

lemma nat_degree_pos_iff_degree_pos :
  0 < nat_degree p ↔ 0 < degree p :=
lt_iff_lt_of_le_iff_le nat_degree_le_iff_degree_le

lemma eq_C_of_nat_degree_le_zero (h : nat_degree p ≤ 0) : p = C (coeff p 0) :=
eq_C_of_degree_le_zero $ degree_le_of_nat_degree_le h

lemma eq_C_of_nat_degree_eq_zero (h : nat_degree p = 0) : p = C (coeff p 0) :=
eq_C_of_nat_degree_le_zero h.le

lemma ne_zero_of_coe_le_degree (hdeg : ↑n ≤ p.degree) : p ≠ 0 :=
by rw ← degree_nonneg_iff_ne_zero; exact trans (by exact_mod_cast n.zero_le) hdeg

lemma le_nat_degree_of_coe_le_degree (hdeg : ↑n ≤ p.degree) :
  n ≤ p.nat_degree :=
with_bot.coe_le_coe.mp ((degree_eq_nat_degree $ ne_zero_of_coe_le_degree hdeg) ▸ hdeg)

end semiring


section nontrivial_semiring
variables [semiring R] [nontrivial R] {p q : polynomial R}

@[simp] lemma degree_X_pow (n : ℕ) : degree ((X : polynomial R) ^ n) = n :=
by rw [X_pow_eq_monomial, degree_monomial _ (@one_ne_zero R _ _)]

@[simp] lemma nat_degree_X_pow (n : ℕ) : nat_degree ((X : polynomial R) ^ n) = n :=
nat_degree_eq_of_degree_eq_some (degree_X_pow n)

theorem not_is_unit_X : ¬ is_unit (X : polynomial R) :=
λ ⟨⟨_, g, hfg, hgf⟩, rfl⟩, @zero_ne_one R _ _ $
by { change g * monomial 1 1 = 1 at hgf, rw [← coeff_one_zero, ← hgf], simp }

@[simp] lemma degree_mul_X : degree (p * X) = degree p + 1 := by simp [monic_X.degree_mul]

@[simp] lemma degree_mul_X_pow : degree (p * X ^ n) = degree p + n :=
by simp [(monic_X_pow n).degree_mul]

end nontrivial_semiring

section ring
variables [ring R] {p q : polynomial R}

lemma degree_sub_le (p q : polynomial R) : degree (p - q) ≤ max (degree p) (degree q) :=
by simpa only [sub_eq_add_neg, degree_neg q] using degree_add_le p (-q)

lemma degree_sub_lt (hd : degree p = degree q)
  (hp0 : p ≠ 0) (hlc : leading_coeff p = leading_coeff q) :
  degree (p - q) < degree p :=
have hp : monomial (nat_degree p) (leading_coeff p) + p.erase (nat_degree p) = p :=
  monomial_add_erase _ _,
have hq : monomial (nat_degree q) (leading_coeff q) + q.erase (nat_degree q) = q :=
  monomial_add_erase _ _,
have hd' : nat_degree p = nat_degree q := by unfold nat_degree; rw hd,
have hq0 : q ≠ 0 := mt degree_eq_bot.2 (hd ▸ mt degree_eq_bot.1 hp0),
calc degree (p - q) = degree (erase (nat_degree q) p + -erase (nat_degree q) q) :
  by conv { to_lhs, rw [← hp, ← hq, hlc, hd', add_sub_add_left_eq_sub, sub_eq_add_neg] }
... ≤ max (degree (erase (nat_degree q) p)) (degree (erase (nat_degree q) q))
  : degree_neg (erase (nat_degree q) q) ▸ degree_add_le _ _
... < degree p : max_lt_iff.2 ⟨hd' ▸ degree_erase_lt hp0, hd.symm ▸ degree_erase_lt hq0⟩


lemma nat_degree_X_sub_C_le {r : R} : (X - C r).nat_degree ≤ 1 :=
nat_degree_le_iff_degree_le.2 $ le_trans (degree_sub_le _ _) $ max_le degree_X_le $
le_trans degree_C_le $ with_bot.coe_le_coe.2 zero_le_one

lemma degree_sum_fin_lt {n : ℕ} (f : fin n → R) :
  degree (∑ i : fin n, C (f i) * X ^ (i : ℕ)) < n :=
begin
  haveI : is_commutative (with_bot ℕ) max := ⟨max_comm⟩,
  haveI : is_associative (with_bot ℕ) max := ⟨max_assoc⟩,
  calc  (∑ i, C (f i) * X ^ (i : ℕ)).degree
      ≤ finset.univ.fold (⊔) ⊥ (λ i, (C (f i) * X ^ (i : ℕ)).degree) : degree_sum_le _ _
  ... = finset.univ.fold max ⊥ (λ i, (C (f i) * X ^ (i : ℕ)).degree) : rfl
  ... < n : (finset.fold_max_lt (n : with_bot ℕ)).mpr ⟨with_bot.bot_lt_coe _, _⟩,

  rintros ⟨i, hi⟩ -,
  calc (C (f ⟨i, hi⟩) * X ^ i).degree
      ≤ (C _).degree + (X ^ i).degree : degree_mul_le _ _
  ... ≤ 0 + i : add_le_add degree_C_le (degree_X_pow_le i)
  ... = i : zero_add _
  ... < n : with_bot.some_lt_some.mpr hi,
end

lemma degree_sub_eq_left_of_degree_lt (h : degree q < degree p) : degree (p - q) = degree p :=
by { rw ← degree_neg q at h, rw [sub_eq_add_neg, degree_add_eq_left_of_degree_lt h] }

lemma degree_sub_eq_right_of_degree_lt (h : degree p < degree q) : degree (p - q) = degree q :=
by { rw ← degree_neg q at h, rw [sub_eq_add_neg, degree_add_eq_right_of_degree_lt h, degree_neg] }

end ring

section nonzero_ring
variables [nontrivial R] [ring R]

@[simp] lemma degree_X_sub_C (a : R) : degree (X - C a) = 1 :=
have degree (C a) < degree (X : polynomial R),
from calc degree (C a) ≤ 0 : degree_C_le
                   ... < 1 : with_bot.some_lt_some.mpr zero_lt_one
                   ... = degree X : degree_X.symm,
by rw [degree_sub_eq_left_of_degree_lt this, degree_X]

@[simp] lemma degree_X_add_C (a : R) : degree (X + C a) = 1 :=
have degree (C a) < degree (X : polynomial R),
from calc degree (C a) ≤ 0 : degree_C_le
                   ... < 1 : with_bot.some_lt_some.mpr zero_lt_one
                   ... = degree X : degree_X.symm,
by rw [degree_add_eq_left_of_degree_lt this, degree_X]

@[simp] lemma nat_degree_X_sub_C (x : R) : (X - C x).nat_degree = 1 :=
nat_degree_eq_of_degree_eq_some $ degree_X_sub_C x

@[simp]
lemma next_coeff_X_sub_C (c : R) : next_coeff (X - C c) = - c :=
by simp [next_coeff_of_pos_nat_degree]

lemma degree_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
  degree ((X : polynomial R) ^ n - C a) = n :=
have degree (C a) < degree ((X : polynomial R) ^ n),
  from calc degree (C a) ≤ 0 : degree_C_le
  ... < degree ((X : polynomial R) ^ n) : by rwa [degree_X_pow];
    exact with_bot.coe_lt_coe.2 hn,
by rw [degree_sub_eq_left_of_degree_lt this, degree_X_pow]

lemma X_pow_sub_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) :
  (X : polynomial R) ^ n - C a ≠ 0 :=
mt degree_eq_bot.2 (show degree ((X : polynomial R) ^ n - C a) ≠ ⊥,
  by rw degree_X_pow_sub_C hn a; exact dec_trivial)

theorem X_sub_C_ne_zero (r : R) : X - C r ≠ 0 :=
pow_one (X : polynomial R) ▸ X_pow_sub_C_ne_zero zero_lt_one r

theorem zero_nmem_multiset_map_X_sub_C {α : Type*} (m : multiset α) (f : α → R) :
  (0 : polynomial R) ∉ m.map (λ a, X - C (f a)) :=
λ mem, let ⟨a, _, ha⟩ := multiset.mem_map.mp mem in X_sub_C_ne_zero _ ha

lemma nat_degree_X_pow_sub_C {n : ℕ} {r : R} :
  (X ^ n - C r).nat_degree = n :=
begin
  by_cases hn : n = 0,
  { rw [hn, pow_zero, ←C_1, ←ring_hom.map_sub, nat_degree_C] },
  { exact nat_degree_eq_of_degree_eq_some (degree_X_pow_sub_C (pos_iff_ne_zero.mpr hn) r) },
end

@[simp] lemma leading_coeff_X_pow_sub_C {n : ℕ} (hn : 0 < n) {r : R} :
  (X ^ n - C r).leading_coeff = 1 :=
by rw [leading_coeff, nat_degree_X_pow_sub_C, coeff_sub, coeff_X_pow_self,
  coeff_C, if_neg (pos_iff_ne_zero.mp hn), sub_zero]

@[simp] lemma leading_coeff_X_pow_sub_one {n : ℕ} (hn : 0 < n) :
  (X ^ n - 1 : polynomial R).leading_coeff = 1 :=
leading_coeff_X_pow_sub_C hn

end nonzero_ring

section no_zero_divisors
variables [semiring R] [no_zero_divisors R] {p q : polynomial R}

@[simp] lemma degree_mul : degree (p * q) = degree p + degree q :=
if hp0 : p = 0 then by simp only [hp0, degree_zero, zero_mul, with_bot.bot_add]
else if hq0 : q = 0 then  by simp only [hq0, degree_zero, mul_zero, with_bot.add_bot]
else degree_mul' $ mul_ne_zero (mt leading_coeff_eq_zero.1 hp0)
    (mt leading_coeff_eq_zero.1 hq0)

@[simp] lemma degree_pow [nontrivial R] (p : polynomial R) (n : ℕ) :
  degree (p ^ n) = n • (degree p) :=
by induction n; [simp only [pow_zero, degree_one, zero_nsmul],
simp only [*, pow_succ, succ_nsmul, degree_mul]]

@[simp] lemma leading_coeff_mul (p q : polynomial R) : leading_coeff (p * q) =
  leading_coeff p * leading_coeff q :=
begin
  by_cases hp : p = 0,
  { simp only [hp, zero_mul, leading_coeff_zero] },
  { by_cases hq : q = 0,
    { simp only [hq, mul_zero, leading_coeff_zero] },
    { rw [leading_coeff_mul'],
      exact mul_ne_zero (mt leading_coeff_eq_zero.1 hp) (mt leading_coeff_eq_zero.1 hq) } }
end

@[simp] lemma leading_coeff_X_add_C [nontrivial R] (a b : R) (ha : a ≠ 0):
  leading_coeff (C a * X + C b) = a :=
begin
  rw [add_comm, leading_coeff_add_of_degree_lt],
  { simp },
  { simpa [degree_C ha] using lt_of_le_of_lt degree_C_le (with_bot.coe_lt_coe.2 zero_lt_one)}
end

/-- `polynomial.leading_coeff` bundled as a `monoid_hom` when `R` has `no_zero_divisors`, and thus
  `leading_coeff` is multiplicative -/
def leading_coeff_hom : polynomial R →* R :=
{ to_fun := leading_coeff,
  map_one' := by simp,
  map_mul' := leading_coeff_mul }

@[simp] lemma leading_coeff_hom_apply (p : polynomial R) :
  leading_coeff_hom p = leading_coeff p := rfl

@[simp] lemma leading_coeff_pow (p : polynomial R) (n : ℕ) :
  leading_coeff (p ^ n) = leading_coeff p ^ n :=
(leading_coeff_hom : polynomial R →* R).map_pow p n

end no_zero_divisors

end polynomial
