/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau.
-/

import ring_theory.polynomial

/-!

# Separable polynomials

We define a polynomial to be separable if it is coprime with its derivative. We prove basic
properties about separable polynomials here.

## Main definitions

* `polynomial.separable f`: a polynomial `f` is separable iff it is coprime with its derivative.
* `polynomial.expand R p f`: expand the polynomial `f` with coefficients in a
  commutative semiring `R` by a factor of p, so `expand R p (∑ aₙ xⁿ)` is `∑ aₙ xⁿᵖ`.
* `polynomial.contract p f`: the opposite of `expand`, so it sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`.

-/

universes u v w
open_locale classical

namespace polynomial

section comm_semiring

variables {R : Type u} [comm_semiring R] {S : Type v} [comm_semiring S]

/-- A polynomial is separable iff it is coprime with its derivative. -/
def separable (f : polynomial R) : Prop :=
is_coprime f f.derivative

lemma separable_def (f : polynomial R) :
  f.separable ↔ is_coprime f f.derivative :=
iff.rfl

lemma separable_def' (f : polynomial R) :
  f.separable ↔ ∃ a b : polynomial R, a * f + b * f.derivative = 1 :=
iff.rfl

lemma separable_one : (1 : polynomial R).separable :=
is_coprime_one_left

lemma separable_X_add_C (a : R) : (X + C a).separable :=
by { rw [separable_def, derivative_add, derivative_X, derivative_C, add_zero],
  exact is_coprime_one_right }

lemma separable_X : (X : polynomial R).separable :=
by { rw [separable_def, derivative_X], exact is_coprime_one_right }

lemma separable_C (r : R) : (C r).separable ↔ is_unit r :=
by rw [separable_def, derivative_C, is_coprime_zero_right, is_unit_C]

lemma separable.of_mul_left {f g : polynomial R} (h : (f * g).separable) : f.separable :=
begin
  have := h.of_mul_left_left, rw derivative_mul at this,
  exact is_coprime.of_mul_right_left (is_coprime.of_add_mul_left_right this)
end

lemma separable.of_mul_right {f g : polynomial R} (h : (f * g).separable) : g.separable :=
by { rw mul_comm at h, exact h.of_mul_left }

lemma separable.is_coprime {f g : polynomial R} (h : (f * g).separable) : is_coprime f g :=
begin
  have := h.of_mul_left_left, rw derivative_mul at this,
  exact is_coprime.of_mul_right_right (is_coprime.of_add_mul_left_right this)
end

theorem separable.of_pow' {f : polynomial R} :
  ∀ {n : ℕ} (h : (f ^ n).separable), is_unit f ∨ (f.separable ∧ n = 1) ∨ n = 0
| 0     := λ h, or.inr $ or.inr rfl
| 1     := λ h, or.inr $ or.inl ⟨pow_one f ▸ h, rfl⟩
| (n+2) := λ h, or.inl $ is_coprime_self.1 h.is_coprime.of_mul_right_left

theorem separable.of_pow {f : polynomial R} (hf : ¬is_unit f) {n : ℕ} (hn : n ≠ 0)
  (hfs : (f ^ n).separable) : f.separable ∧ n = 1 :=
(hfs.of_pow'.resolve_left hf).resolve_right hn

theorem separable.map {p : polynomial R} (h : p.separable) {f : R →+* S} : (p.map f).separable :=
let ⟨a, b, H⟩ := h in ⟨a.map f, b.map f,
by rw [derivative_map, ← map_mul, ← map_mul, ← map_add, H, map_one]⟩

variables (R) (p q : ℕ)

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`. -/
noncomputable def expand : polynomial R →ₐ[R] polynomial R :=
{ commutes' := λ r, eval₂_C _ _,
  .. (eval₂_ring_hom C (X ^ p) : polynomial R →+* polynomial R) }

lemma coe_expand : (expand R p : polynomial R → polynomial R) = eval₂ C (X ^ p) := rfl

variables {R}

@[simp] lemma expand_C (r : R) : expand R p (C r) = C r := eval₂_C _ _
@[simp] lemma expand_X : expand R p X = X ^ p := eval₂_X _ _
@[simp] lemma expand_monomial (r : R) : expand R p (monomial q r) = monomial (q * p) r :=
by simp_rw [monomial_eq_smul_X, alg_hom.map_smul, alg_hom.map_pow, expand_X, mul_comm, pow_mul]

theorem expand_expand (f : polynomial R) : expand R p (expand R q f) = expand R (p * q) f :=
polynomial.induction_on f (λ r, by simp_rw expand_C)
  (λ f g ihf ihg, by simp_rw [alg_hom.map_add, ihf, ihg])
  (λ n r ih, by simp_rw [alg_hom.map_mul, expand_C, alg_hom.map_pow, expand_X,
    alg_hom.map_pow, expand_X, pow_mul])

theorem expand_mul (f : polynomial R) : expand R (p * q) f = expand R p (expand R q f) :=
(expand_expand p q f).symm

@[simp] theorem expand_one (f : polynomial R) : expand R 1 f = f :=
polynomial.induction_on f
  (λ r, by rw expand_C)
  (λ f g ihf ihg, by rw [alg_hom.map_add, ihf, ihg])
  (λ n r ih, by rw [alg_hom.map_mul, expand_C, alg_hom.map_pow, expand_X, pow_one])

theorem expand_pow (f : polynomial R) : expand R (p ^ q) f = (expand R p ^[q] f) :=
nat.rec_on q (by rw [nat.pow_zero, expand_one, function.iterate_zero, id]) $ λ n ih,
by rw [function.iterate_succ_apply', nat.pow_succ, mul_comm, expand_mul, ih]

theorem derivative_expand (f : polynomial R) :
  (expand R p f).derivative = expand R p f.derivative * (p * X ^ (p - 1)) :=
by rw [coe_expand, derivative_eval₂_C, derivative_pow, derivative_X, mul_one]

theorem coeff_expand {p : ℕ} (hp : 0 < p) (f : polynomial R) (n : ℕ) :
  (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0 :=
begin
  change (show ℕ →₀ R, from (f.sum (λ e a, C a * (X ^ p) ^ e) : polynomial R)) n = _,
  simp_rw [finsupp.sum_apply, finsupp.sum, ← pow_mul, C_mul', ← monomial_eq_smul_X,
    monomial, finsupp.single_apply],
  split_ifs with h,
  { rw [finset.sum_eq_single (n/p), nat.mul_div_cancel' h, if_pos rfl], refl,
    { intros b hb1 hb2, rw if_neg, intro hb3, apply hb2, rw [← hb3, nat.mul_div_cancel_left b hp] },
    { intro hn, rw finsupp.not_mem_support_iff.1 hn, split_ifs; refl } },
  { rw finset.sum_eq_zero, intros k hk, rw if_neg, exact λ hkn, h ⟨k, hkn.symm⟩, },
end

@[simp] theorem coeff_expand_mul {p : ℕ} (hp : 0 < p) (f : polynomial R) (n : ℕ) :
  (expand R p f).coeff (n * p) = f.coeff n :=
by rw [coeff_expand hp, if_pos (dvd_mul_left _ _), nat.mul_div_cancel _ hp]

@[simp] theorem coeff_expand_mul' {p : ℕ} (hp : 0 < p) (f : polynomial R) (n : ℕ) :
  (expand R p f).coeff (p * n) = f.coeff n :=
by rw [mul_comm, coeff_expand_mul hp]

theorem expand_eq_map_domain (p : ℕ) (f : polynomial R) :
  expand R p f = f.map_domain (*p) :=
finsupp.induction f rfl $ λ n r f hf hr ih,
by rw [finsupp.map_domain_add, finsupp.map_domain_single, alg_hom.map_add, ← monomial,
  expand_monomial, ← monomial, ih]

theorem expand_inj {p : ℕ} (hp : 0 < p) {f g : polynomial R} :
  expand R p f = expand R p g ↔ f = g :=
⟨λ H, ext $ λ n, by rw [← coeff_expand_mul hp, H, coeff_expand_mul hp], congr_arg _⟩

theorem expand_eq_zero {p : ℕ} (hp : 0 < p) {f : polynomial R} : expand R p f = 0 ↔ f = 0 :=
by rw [← (expand R p).map_zero, expand_inj hp, alg_hom.map_zero]

theorem expand_eq_C {p : ℕ} (hp : 0 < p) {f : polynomial R} {r : R} :
  expand R p f = C r ↔ f = C r :=
by rw [← expand_C, expand_inj hp, expand_C]

theorem nat_degree_expand (p : ℕ) (f : polynomial R) :
  (expand R p f).nat_degree = f.nat_degree * p :=
begin
  cases p.eq_zero_or_pos with hp hp,
  { rw [hp, coe_expand, pow_zero, mul_zero, ← C_1, eval₂_hom, nat_degree_C] },
  by_cases hf : f = 0,
  { rw [hf, alg_hom.map_zero, nat_degree_zero, zero_mul] },
  have hf1 : expand R p f ≠ 0 := mt (expand_eq_zero hp).1 hf,
  rw [← with_bot.coe_eq_coe, ← degree_eq_nat_degree hf1],
  refine le_antisymm ((degree_le_iff_coeff_zero _ _).2 $ λ n hn, _) _,
  { rw coeff_expand hp, split_ifs with hpn,
    { rw coeff_eq_zero_of_nat_degree_lt, contrapose! hn,
      rw [with_bot.coe_le_coe, ← nat.div_mul_cancel hpn], exact nat.mul_le_mul_right p hn },
    { refl } },
  { refine le_degree_of_ne_zero _,
    rw [coeff_expand_mul hp, ← leading_coeff], exact mt leading_coeff_eq_zero.1 hf }
end

end comm_semiring

section comm_ring

variables {R : Type u} [comm_ring R]

lemma separable.mul {f g : polynomial R} (hf : f.separable) (hg : g.separable)
  (h : is_coprime f g) : (f * g).separable :=
by { rw [separable_def, derivative_mul], exact ((hf.mul_right h).add_mul_left_right _).mul_left
  ((h.symm.mul_right hg).mul_add_right_right _) }

end comm_ring

section integral_domain

variables (R : Type u) [integral_domain R]

theorem is_local_ring_hom_expand {p : ℕ} (hp : 0 < p) :
  is_local_ring_hom (↑(expand R p) : polynomial R →+* polynomial R) :=
begin
  refine ⟨λ f hf1, _⟩, rw ← coe_fn_coe_base at hf1,
  have hf2 := eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf1),
  rw [coeff_expand hp, if_pos (dvd_zero _), p.zero_div] at hf2,
  rw [hf2, is_unit_C] at hf1, rw expand_eq_C hp at hf2, rwa [hf2, is_unit_C]
end

end integral_domain

section field

variables {F : Type u} [field F]

theorem separable_iff_derivative_ne_zero {f : polynomial F} (hf : irreducible f) :
  f.separable ↔ f.derivative ≠ 0 :=
⟨λ h1 h2, hf.1 $ is_coprime_zero_right.1 $ h2 ▸ h1,
λ h, is_coprime_of_dvd (mt and.right h) $ λ g hg1 hg2 ⟨p, hg3⟩ hg4,
let ⟨u, hu⟩ := (hf.2 _ _ hg3).resolve_left hg1 in
have f ∣ f.derivative, by { conv_lhs { rw [hg3, ← hu] }, rwa mul_unit_dvd_iff },
not_lt_of_le (nat_degree_le_of_dvd this h) $ nat_degree_derivative_lt h⟩

section char_p

variables (p : ℕ) [hp : fact p.prime]
include hp

/-- The opposite of `expand`: sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`. -/
noncomputable def contract (f : polynomial F) : polynomial F :=
⟨@finset.preimage ℕ ℕ (*p) f.support $ λ _ _ _ _, (nat.mul_left_inj hp.pos).1,
λ n, f.coeff (n * p),
λ n, by { rw [finset.mem_preimage, finsupp.mem_support_iff], refl }⟩

theorem coeff_contract (f : polynomial F) (n : ℕ) : (contract p f).coeff n = f.coeff (n * p) := rfl

theorem of_irreducible_expand {f : polynomial F} (hf : irreducible (expand F p f)) :
  irreducible f :=
@@of_irreducible_map _ _ _ (is_local_ring_hom_expand F hp.pos) hf

theorem of_irreducible_expand_pow {f : polynomial F} {n : ℕ} :
  irreducible (expand F (p ^ n) f) → irreducible f :=
nat.rec_on n (λ hf, by rwa [nat.pow_zero, expand_one] at hf) $ λ n ih hf,
ih $ of_irreducible_expand p $ by rwa [expand_expand, mul_comm]

variables [HF : char_p F p]
include HF

theorem expand_contract {f : polynomial F} (hf : f.derivative = 0) :
  expand F p (contract p f) = f :=
begin
  ext n, rw [coeff_expand hp.pos, coeff_contract], split_ifs with h,
  { rw nat.div_mul_cancel h },
  { cases n, { exact absurd (dvd_zero p) h },
    have := coeff_derivative f n, rw [hf, coeff_zero, zero_eq_mul] at this, cases this, { rw this },
    rw [← nat.cast_succ, char_p.cast_eq_zero_iff F p] at this,
    exact absurd this h }
end

theorem separable_or {f : polynomial F} (hf : irreducible f) : f.separable ∨
  ¬f.separable ∧ ∃ g : polynomial F, irreducible g ∧ expand F p g = f :=
if H : f.derivative = 0 then or.inr
  ⟨by rw [separable_iff_derivative_ne_zero hf, not_not, H],
  contract p f,
  by haveI := is_local_ring_hom_expand F hp.pos; exact
    of_irreducible_map ↑(expand F p) (by rwa ← expand_contract p H at hf),
  expand_contract p H⟩
else or.inl $ (separable_iff_derivative_ne_zero hf).2 H

theorem exists_separable_of_irreducible {f : polynomial F} (hf : irreducible f) (hf0 : f ≠ 0) :
  ∃ (n : ℕ) (g : polynomial F), g.separable ∧ expand F (p ^ n) g = f :=
begin
  generalize hn : f.nat_degree = N, unfreezingI { revert f },
  apply nat.strong_induction_on N, intros N ih f hf hf0 hn,
  rcases separable_or p hf with h | ⟨h1, g, hg, hgf⟩,
  { refine ⟨0, f, h, _⟩, rw [nat.pow_zero, expand_one] },
  { cases N with N,
    { rw [nat_degree_eq_zero_iff_degree_le_zero, degree_le_zero_iff] at hn,
      rw [hn, separable_C, is_unit_iff_ne_zero, not_not] at h1,
      rw [h1, C_0] at hn, exact absurd hn hf0 },
    have hg1 : g.nat_degree * p = N.succ,
    { rwa [← nat_degree_expand, hgf] },
    have hg2 : g.nat_degree ≠ 0,
    { intro this, rw [this, zero_mul] at hg1, cases hg1 },
    have hg3 : g.nat_degree < N.succ,
    { rw [← mul_one g.nat_degree, ← hg1],
      exact nat.mul_lt_mul_of_pos_left hp.one_lt (nat.pos_of_ne_zero hg2) },
    have hg4 : g ≠ 0,
    { rintro rfl, exact hg2 nat_degree_zero },
    rcases ih _ hg3 hg hg4 rfl with ⟨n, g, hg5, rfl⟩, refine ⟨n+1, g, hg5, _⟩,
    rw [← hgf, expand_expand, nat.pow_succ, mul_comm] }
end

theorem is_unit_or_eq_zero_of_separable_expand {f : polynomial F} (n : ℕ)
  (hf : (expand F (p ^ n) f).separable) : is_unit f ∨ n = 0 :=
begin
  rw classical.or_iff_not_imp_right, intro hn,
  have hf2 : (expand F (p ^ n) f).derivative = 0,
  { by rw [derivative_expand, nat.cast_pow, char_p.cast_eq_zero,
      zero_pow (nat.pos_of_ne_zero hn), zero_mul, mul_zero] },
  rw [separable_def, hf2, is_coprime_zero_right, is_unit_iff] at hf, rcases hf with ⟨r, hr, hrf⟩,
  rw [eq_comm, expand_eq_C (nat.pow_pos hp.pos _)] at hrf,
  rwa [hrf, is_unit_C]
end

theorem unique_separable_of_irreducible {f : polynomial F} (hf : irreducible f) (hf0 : f ≠ 0)
  (n₁ : ℕ) (g₁ : polynomial F) (hg₁ : g₁.separable) (hgf₁ : expand F (p ^ n₁) g₁ = f)
  (n₂ : ℕ) (g₂ : polynomial F) (hg₂ : g₂.separable) (hgf₂ : expand F (p ^ n₂) g₂ = f) :
  n₁ = n₂ ∧ g₁ = g₂ :=
begin
  revert g₁ g₂, wlog hn : n₁ ≤ n₂ := le_total n₁ n₂ using [n₁ n₂, n₂ n₁] tactic.skip,
  unfreezingI { intros, rw le_iff_exists_add at hn, rcases hn with ⟨k, rfl⟩,
    rw [← hgf₁, nat.pow_add, expand_mul, expand_inj (nat.pow_pos hp.pos n₁)] at hgf₂, subst hgf₂,
    subst hgf₁,
    rcases is_unit_or_eq_zero_of_separable_expand p k hg₁ with h | rfl,
    { rw is_unit_iff at h, rcases h with ⟨r, hr, rfl⟩,
      simp_rw expand_C at hf, exact absurd (is_unit_C.2 hr) hf.1 },
    { rw [add_zero, nat.pow_zero, expand_one], split; refl } },
  exact λ g₁ g₂ hg₁ hgf₁ hg₂ hgf₂, let ⟨hn, hg⟩ := this g₂ g₁ hg₂ hgf₂ hg₁ hgf₁ in ⟨hn.symm, hg.symm⟩
end

end char_p

end field

end polynomial

open polynomial

theorem irreducible.separable {F : Type u} [field F] [char_zero F] {f : polynomial F}
  (hf : irreducible f) (hf0 : f ≠ 0) : f.separable :=
begin
  rw [separable_iff_derivative_ne_zero hf, ne, ← degree_eq_bot, degree_derivative_eq], rintro ⟨⟩,
  rw [nat.pos_iff_ne_zero, ne, nat_degree_eq_zero_iff_degree_le_zero, degree_le_zero_iff],
  refine λ hf1, hf.1 _, rw [hf1, is_unit_C, is_unit_iff_ne_zero],
  intro hf2, rw [hf2, C_0] at hf1, exact absurd hf1 hf0
end
