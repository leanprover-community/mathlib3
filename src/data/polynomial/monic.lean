/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.degree
import algebra.associated
import tactic.omega

/-!
# Theory of monic polynomials

We give several tools for proving that polynomials are monic, e.g.
`monic_mul`, `monic_map`.
-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

open finset
open_locale big_operators

namespace polynomial
universes u v y
variables {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

section semiring
variables [semiring R] {p q r : polynomial R}

lemma monic.as_sum {p : polynomial R} (hp : p.monic) :
  p = X^(p.nat_degree) + (∑ i in finset.range p.nat_degree, C (p.coeff i) * X^i) :=
begin
  conv_lhs { rw [p.as_sum_range, finset.sum_range_succ] },
  suffices : C (p.coeff p.nat_degree) = 1,
  { rw [this, one_mul] },
  exact congr_arg C hp
end

lemma ne_zero_of_monic_of_zero_ne_one (hp : monic p) (h : (0 : R) ≠ 1) :
  p ≠ 0 := mt (congr_arg leading_coeff) $ by rw [monic.def.1 hp, leading_coeff_zero]; cc

lemma ne_zero_of_ne_zero_of_monic (hp : p ≠ 0) (hq : monic q) : q ≠ 0 :=
begin
  intro h, rw [h, monic.def, leading_coeff_zero] at hq,
  rw [← mul_one p, ← C_1, ← hq, C_0, mul_zero] at hp,
  exact hp rfl
end

lemma monic_map [semiring S] (f : R →+* S) (hp : monic p) : monic (p.map f) :=
if h : (0 : S) = 1 then
  by haveI := subsingleton_of_zero_eq_one h;
  exact subsingleton.elim _ _
else
have f (leading_coeff p) ≠ 0,
  by rwa [show _ = _, from hp, is_semiring_hom.map_one f, ne.def, eq_comm],
by
begin
  rw [monic, leading_coeff, coeff_map],
  suffices : p.coeff (map f p).nat_degree = 1, simp [this],
  suffices : (map f p).nat_degree = p.nat_degree, rw this, exact hp,
  rwa nat_degree_eq_of_degree_eq (degree_map_eq_of_leading_coeff_ne_zero _ _),
end

lemma monic_mul_C_of_leading_coeff_mul_eq_one [nontrivial R] {b : R}
  (hp : p.leading_coeff * b = 1) : monic (p * C b) :=
by rw [monic, leading_coeff_mul' _]; simp [leading_coeff_C b, hp]

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
pow_one (X : polynomial R) ▸ monic_X_pow_add degree_C_le

lemma monic_mul (hp : monic p) (hq : monic q) : monic (p * q) :=
if h0 : (0 : R) = 1 then by haveI := subsingleton_of_zero_eq_one h0;
  exact subsingleton.elim _ _
else
  have leading_coeff p * leading_coeff q ≠ 0, by simp [monic.def.1 hp, monic.def.1 hq, ne.symm h0],
  by rw [monic.def, leading_coeff_mul' this, monic.def.1 hp, monic.def.1 hq, one_mul]

lemma monic_pow (hp : monic p) : ∀ (n : ℕ), monic (p ^ n)
| 0     := monic_one
| (n+1) := monic_mul hp (monic_pow n)

end semiring

section comm_semiring
variables [comm_semiring R] {p : polynomial R}

lemma monic_prod_of_monic (s : finset ι) (f : ι → polynomial R) (hs : ∀ i ∈ s, monic (f i)) :
monic (∏ i in s, f i) :=
prod_induction _ _ (@monic_mul _ _) monic_one hs

lemma is_unit_C {x : R} : is_unit (C x) ↔ is_unit x :=
begin
  rw [is_unit_iff_dvd_one, is_unit_iff_dvd_one],
  split,
  { rintros ⟨g, hg⟩,
    replace hg := congr_arg (eval 0) hg,
    rw [eval_one, eval_mul, eval_C] at hg,
    exact ⟨g.eval 0, hg⟩ },
  { rintros ⟨y, hy⟩,
    exact ⟨C y, by rw [← C_mul, ← hy, C_1]⟩ }
end

lemma eq_one_of_is_unit_of_monic (hm : monic p) (hpu : is_unit p) : p = 1 :=
have degree p ≤ 0,
  from calc degree p ≤ degree (1 : polynomial R) :
    let ⟨u, hu⟩ := is_unit_iff_dvd_one.1 hpu in
    if hu0 : u = 0
    then begin
        rw [hu0, mul_zero] at hu,
        rw [← mul_one p, hu, mul_zero],
        simp
      end
    else have p.leading_coeff * u.leading_coeff ≠ 0,
        by rw [hm.leading_coeff, one_mul, ne.def, leading_coeff_eq_zero];
          exact hu0,
      by rw [hu, degree_mul' this];
        exact le_add_of_nonneg_right (degree_nonneg_iff_ne_zero.2 hu0)
  ... ≤ 0 : degree_one_le,
by rw [eq_C_of_degree_le_zero this, ← nat_degree_eq_zero_iff_degree_le_zero.2 this,
    ← leading_coeff, hm.leading_coeff, C_1]


end comm_semiring

section comm_ring
variables [comm_ring R]
namespace monic

lemma coeff_nat_degree {p : polynomial R} (hp : p.monic) : p.coeff (p.nat_degree) = 1 := hp

@[simp]
lemma degree_eq_zero_iff_eq_one {p : polynomial R} (hp : p.monic) :
p.nat_degree = 0 ↔ p = 1 :=
begin
  split; intro h,
  swap, { rw h, exact nat_degree_one },
  have : p = C (p.coeff 0),
  { rw ← polynomial.degree_le_zero_iff,
    rwa polynomial.nat_degree_eq_zero_iff_degree_le_zero at h },
  rw this, convert C_1, rw ← h, apply hp,
end

lemma nat_degree_mul [nontrivial R] {p q : polynomial R} (hp : p.monic) (hq : q.monic) :
(p * q).nat_degree = p.nat_degree + q.nat_degree :=
by { apply nat_degree_mul', rw [hp.leading_coeff, hq.leading_coeff], simp }

lemma next_coeff_mul {p q : polynomial R} (hp : monic p) (hq : monic q) :
next_coeff (p * q) = next_coeff p + next_coeff q :=
begin
  classical,
  by_cases h : nontrivial R, swap,
  { rw nontrivial_iff at h, push_neg at h, apply h, },
  haveI := h, clear h,
  have := monic.nat_degree_mul hp hq,
  dsimp only [next_coeff], rw this,
  simp only [hp, hq, degree_eq_zero_iff_eq_one, add_eq_zero_iff], clear this,
  split_ifs; try { tauto <|> simp [h_1, h_2] },
  rename h_1 hp0, rename h_2 hq0, clear h,
  rw ← degree_eq_zero_iff_eq_one at hp0 hq0, assumption',
  -- we've reduced to the case where the degrees dp and dq are nonzero
  set dp := p.nat_degree, set dq := q.nat_degree,
  rw coeff_mul,
  have : {(dp, dq - 1), (dp - 1, dq)} ⊆ nat.antidiagonal (dp + dq - 1),
  { rw insert_subset, split,
    work_on_goal 0 { rw [nat.mem_antidiagonal, nat.add_sub_assoc] },
    work_on_goal 1 { simp only [singleton_subset_iff, nat.mem_antidiagonal],
      apply nat.sub_add_eq_add_sub },
    all_goals { apply nat.succ_le_of_lt, apply nat.pos_of_ne_zero, assumption } },
  rw ← sum_subset this,
  { rw [sum_insert, sum_singleton], iterate 2 { rw coeff_nat_degree }, ring, assumption',
    suffices : dp ≠ dp - 1, { rw mem_singleton, simp [this] }, omega }, clear this,
  intros x hx hx1,
  simp only [nat.mem_antidiagonal] at hx, simp only [mem_insert, mem_singleton] at hx1,
  suffices : p.coeff x.fst = 0 ∨ q.coeff x.snd = 0, cases this; simp [this],
  suffices : dp < x.fst ∨ dq < x.snd, cases this,
  { left,  apply coeff_eq_zero_of_nat_degree_lt, assumption },
  { right, apply coeff_eq_zero_of_nat_degree_lt, assumption },
  by_cases h : dp < x.fst, { left, exact h }, push_neg at h, right,
  have : x.fst ≠ dp - 1, { contrapose! hx1, right, ext, assumption, dsimp only, omega },
  have : x.fst ≠ dp,     { contrapose! hx1, left,  ext, assumption, dsimp only, omega },
  omega,
end

lemma next_coeff_prod
  (s : finset ι) (f : ι → polynomial R) (h : ∀ i ∈ s, monic (f i)) :
next_coeff (∏ i in s, f i) = ∑ i in s, next_coeff (f i) :=
begin
  classical,
  revert h, apply finset.induction_on s,
  { simp only [finset.not_mem_empty, forall_prop_of_true, forall_prop_of_false, finset.sum_empty,
  finset.prod_empty, not_false_iff, forall_true_iff],
  rw ← C_1, rw next_coeff_C_eq_zero },
  { intros a s ha hs monic,
    rw finset.prod_insert ha,
    rw finset.sum_insert ha,
    rw next_coeff_mul (monic a (finset.mem_insert_self a s)), swap,
    { apply monic_prod_of_monic, intros b bs,
      apply monic, apply finset.mem_insert_of_mem bs },
    { refine congr rfl (hs _),
      intros b bs, apply monic, apply finset.mem_insert_of_mem bs }}
end

end monic
end comm_ring

section ring
variables [ring R] {p : polynomial R}

theorem monic_X_sub_C (x : R) : monic (X - C x) :=
by simpa only [C_neg] using monic_X_add_C (-x)

theorem monic_X_pow_sub {n : ℕ} (H : degree p ≤ n) : monic (X ^ (n+1) - p) :=
monic_X_pow_add ((degree_neg p).symm ▸ H)

/-`X ^ n - a` is monic. -/
lemma monic_X_pow_sub_C {R : Type u} [ring R] (a : R) {n : ℕ} : n ≠ 0 → (X ^ n - C a).monic :=
begin
  intro h,
  obtain ⟨k, hk⟩ := nat.exists_eq_succ_of_ne_zero h,
  rw [hk],
  apply monic_X_pow_sub,
  have hleq := le_trans (@degree_C_le _ a _) (with_bot.coe_le_coe.2 (nat.zero_le ↑k)),
  norm_cast at hleq,
  exact hleq
end

section injective
open function
variables [semiring S] {f : R →+* S} (hf : injective f)
include hf


lemma leading_coeff_of_injective (p : polynomial R) :
  leading_coeff (p.map f) = f (leading_coeff p) :=
begin
  delta leading_coeff,
  rw [coeff_map f, nat_degree_map' hf p]
end

lemma monic_of_injective {p : polynomial R} (hp : (p.map f).monic) : p.monic :=
begin
  apply hf,
  rw [← leading_coeff_of_injective hf, hp.leading_coeff, is_semiring_hom.map_one f]
end

end injective
end ring


section nonzero_semiring
variables [semiring R] [nontrivial R] {p q : polynomial R}

@[simp] lemma not_monic_zero : ¬monic (0 : polynomial R) :=
by simpa only [monic, leading_coeff_zero] using (zero_ne_one : (0 : R) ≠ 1)

lemma ne_zero_of_monic (h : monic p) : p ≠ 0 :=
λ h₁, @not_monic_zero R _ _ (h₁ ▸ h)

/-If we have a morphism of semiring `f : R →+* S` and a polynomial `P : polynomial S` that comes via `f` from a polynomial `Q : polynomial R`, then it comes from a polynomial of the same degree. -/
lemma lifts_of_same_degree {R : Type u} {S : Type v} [comm_semiring R] [comm_semiring S] [nontrivial R] [nontrivial S] (f : R →+* S) (P : polynomial S) : (∃ (Q : polynomial R), map f Q = P) → (∃ (Q₁ : polynomial R), map f Q₁ = P ∧ Q₁.degree = P.degree) :=
begin
  intro hexist,
  obtain ⟨Q, hQ⟩ := hexist,
  by_cases hzero : P = 0,
  {
    use 0,
    simp only [hzero, degree_zero, eq_self_iff_true, and_self, map_zero] },
  have hcoeff : ∀ n ∈ finset.range (P.nat_degree + 1), f (Q.coeff n) = P.coeff n,
  { intros n hn,
    rw [← hQ, coeff_map] },
  use (∑ (i : ℕ) in finset.range (P.nat_degree + 1), (C (Q.coeff i)) * polynomial.X ^ i),
  split,
  { simp only [map_sum, map_C, map_pow, map_X, map_mul],
    conv_lhs { apply_congr,
               skip,
               simp only [hcoeff, H] },
    nth_rewrite 1 as_sum_range P },
  rw finset.range_succ,
  simp only [finset.not_mem_range_self, finset.sum_insert, not_false_iff],
  have deglt : (∑ (n : ℕ) in finset.range P.nat_degree, C (Q.coeff n) * X ^ n).degree < P.nat_degree,
  { refine lt_of_le_of_lt (degree_sum_le (finset.range P.nat_degree) (λ i, C (Q.coeff i) * X ^ i)) _,
    simp only [with_bot.bot_lt_coe P.nat_degree, finset.mem_range, finset.sup_lt_iff],
    intros b hb,
    refine lt_of_le_of_lt (degree_mul_le (C (Q.coeff b)) (X ^ b) ) _,
    by_cases coef_zero : Q.coeff b = 0,
    { simp only [coef_zero, with_bot.bot_lt_coe P.nat_degree, degree_zero, with_bot.bot_add, ring_hom.map_zero] },
    simp only [coef_zero, degree_C, degree_X_pow, ne.def, zero_add, not_false_iff],
    norm_cast,
    exact hb },
  have leadcoef : Q.coeff P.nat_degree ≠ 0,
  { by_contra habs,
    rw [not_not] at habs,
    replace hcoeff := hcoeff P.nat_degree (finset.self_mem_range_succ P.nat_degree),
    simp only [habs, ring_hom.map_zero] at hcoeff,
    exact coeff_ne_zero_of_eq_degree (degree_eq_nat_degree hzero) (eq.symm hcoeff) },
  rw add_comm,
  simp only [degree_add_eq_of_degree_lt, leadcoef, deglt, degree_eq_nat_degree hzero, ne.def, not_false_iff, degree_monomial]
end

/-If we have a morphism of semiring `f : R →+* S` and a monic polynomial `P : polynomial S` that comes via `f` from polynomial `Q : polynomial R`, then it comes from a monic polynomial of the same degree. -/
lemma monic_lifts_of_same_degree {R : Type u} {S : Type v} [comm_semiring R] [comm_semiring S] [nontrivial R] [nontrivial S] {f : R →+* S} {P : polynomial S} (hmonic : P.monic) : (∃ (Q : polynomial R), map f Q = P) → (∃ (Q₁ : polynomial R), map f Q₁ = P ∧ Q₁.degree = P.degree ∧ Q₁.monic) :=
begin
  intro hexist,
  obtain ⟨Q, hQ⟩ := hexist,
  have hcoeff : ∀ n ∈ finset.range P.nat_degree, f (Q.coeff n) = P.coeff n,
  { intros n hn,
    rw [← hQ, coeff_map] },
  use (X ^ P.nat_degree + ∑ (i : ℕ) in finset.range P.nat_degree, (C (Q.coeff i)) * polynomial.X ^ i),
  have deglt : (∑ (n : ℕ) in finset.range P.nat_degree, C (Q.coeff n) * X ^ n).degree < P.nat_degree,
  { refine lt_of_le_of_lt (degree_sum_le (finset.range P.nat_degree) (λ i, C (Q.coeff i) * X ^ i)) _,
    simp only [with_bot.bot_lt_coe P.nat_degree, finset.mem_range, finset.sup_lt_iff],
    intros b hb,
    refine lt_of_le_of_lt (degree_mul_le (C (Q.coeff b)) (X ^ b) ) _,
    by_cases coef_zero : Q.coeff b = 0,
    { simp only [coef_zero, with_bot.bot_lt_coe P.nat_degree, degree_zero, with_bot.bot_add, ring_hom.map_zero] },
    simp [coef_zero, degree_C, degree_X_pow, ne.def, zero_add, not_false_iff],
    norm_cast,
    exact hb },
  have degreeres : (X ^ P.nat_degree + ∑ (i : ℕ) in finset.range P.nat_degree, C (Q.coeff i) * X ^ i).degree = P.degree,
  { rw add_comm,
    simp only [degree_add_eq_of_degree_lt, deglt, degree_eq_nat_degree hmonic.ne_zero, degree_X_pow] },
  repeat {split},
  { simp only [map_sum,map_add, map_pow, map_X],
    have rwpartial : ∑ (i : ℕ) in finset.range P.nat_degree, map f (C (Q.coeff i) * X ^ i) = (∑ (i : ℕ) in finset.range P.nat_degree, C (P.coeff i) * X ^ i),
    { conv_lhs { apply_congr,
                 skip,
                 simp [hcoeff, H] } },
    nth_rewrite 2 monic.as_sum hmonic,
    rw [rwpartial] },
  { exact degreeres },
  { rw monic,
    nth_rewrite 0 ← degree_eq_nat_degree hmonic.ne_zero at deglt,
    rw [add_comm, polynomial.leading_coeff_add_of_degree_lt _],
    { simp only [leading_coeff_X_pow] },
    apply lt_of_lt_of_le deglt _,
    simp only [degree_X_pow, degree_le_nat_degree]},
end

end nonzero_semiring


end polynomial
