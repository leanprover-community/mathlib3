/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
import field_theory.separable
import algebra.algebra.basic
import data.polynomial.degree
import algebra.char_p.exp_char

/-!

# Separable degree

This file contains basics about the separable degree of a polynomial.

## Main results

- `separable_degree`: the definition of the separable degree
- `irreducible_has_separable_contraction`: any nonzero irreducible polynomial can be contracted
  to a separable polynomial
- `separable_degree_dvd_degree'`: the separable degree divides the degree, in function of the
  exponential characteristic of the field
- `separable_degree_dvd_degree` and `separable_degree_eq_degree` specialize the statement of
  `separable_degree_dvd_degree`
- `separable_degree_eq`: the separable degree is unique (for polynomials over a field)

## Tags

separable degree, degree, polynomial
-/

namespace polynomial

noncomputable theory
open_locale classical

section comm_semiring

variables {F : Type} [comm_semiring F]
  (q : ℕ)

/-- A separable contraction of a polynomial `f` is a separable polynomial `g` such that
`g(x^(q^m)) = f(x)` for some `m : ℕ`.-/
def has_separable_contraction (f : polynomial F) : Prop :=
∃ g : polynomial F, g.separable ∧ ∃ m : ℕ, expand F (q^m) g = f

variables {f : polynomial F} (hf : has_separable_contraction q f)

/-- A choice of a separable contraction. -/
def separable_contraction : polynomial F := classical.some hf

/-- The separable degree of a polynomial is the degree of a given separable contraction. -/
def separable_degree : ℕ := nat_degree (separable_contraction q hf)

/-- The separable degree divides the degree, in function of the exponential characteristic of F. -/
lemma separable_degree_dvd_degree' : ∃ m : ℕ, (separable_degree q hf) * (q ^ m) = f.nat_degree :=
begin
  cases (classical.some_spec hf).2 with m hm,
  use m,
  let g := classical.some hf,
  have deg_g : g.nat_degree = separable_degree q hf, by refl,
  rw [←deg_g, ←hm, nat_degree_expand (q^m) g, mul_comm],
end

/-- The separable degree divides the degree. -/
lemma separable_degree_dvd_degree :
  (separable_degree q hf) ∣ f.nat_degree :=
let ⟨a, ha⟩ := separable_degree_dvd_degree' q hf in dvd.intro (q ^ a) ha

/-- In exponential characteristic one, the separable degree equals the degree. -/
lemma separable_degree_eq_degree {f : polynomial F}
  (hf : has_separable_contraction 1 f) : (separable_degree 1 hf) = f.nat_degree :=
exists.elim (separable_degree_dvd_degree' 1 hf) (λ a, λ ha, by rw [←ha, one_pow a, mul_one])

lemma exists_eq_add_nonneg_of_lt (m m' : ℕ) (h : m < m') : ∃ s : ℕ, 0 < s ∧ m' = m + s :=
let ⟨k, hk⟩ := nat.exists_eq_add_of_lt h in ⟨k.succ, k.zero_lt_succ, hk⟩

end comm_semiring

section field

variables {F : Type} [field F]
  (q : ℕ)
  {f : polynomial F} (hf : has_separable_contraction q f)

/-- Every irreducible polynomial can be contracted to a separable polynomial.
https://stacks.math.columbia.edu/tag/09H0 -/
lemma irreducible_has_separable_contraction (q : ℕ) [hF : exp_char F q]
  (f : polynomial F) [irred : irreducible f] (fn : f ≠ 0) : has_separable_contraction q f :=
begin
  casesI hF,
  { use f,
    exact ⟨irreducible.separable irred, ⟨0, by rw [pow_zero, expand_one]⟩⟩ },
  { haveI qp : fact (nat.prime q) := fact_iff.mpr hF_hprime,
    rcases exists_separable_of_irreducible q irred fn with ⟨n, g, hg⟩,
    use g,
    exact ⟨hg.1, ⟨n, hg.2⟩⟩, }
end

/-- A helper lemma: if two expansions (along the positive characteristic) of two polynomials `g` and
`g'` agree, then either their degrees are the same, or one of them is not separable. -/
lemma contraction_degree_eq_aux [hq : fact q.prime] [hF : char_p F q]
  (g g' : polynomial F) (m m' : ℕ)
  (h_expand : expand F (q^m) g = expand F (q^m') g')
  (h : m < m') :
  (g.nat_degree =  g'.nat_degree) ∨ ¬g.separable :=
begin
  suffices : g.separable → g.nat_degree = g'.nat_degree,
  from (not_or_of_imp this).symm,

  cases exists_eq_add_nonneg_of_lt m m' h with s hs,
  intro g_sep,

  rw [hs.2, pow_add, expand_mul] at h_expand,

  have r := expand_injective (pow_pos hq.1.pos m) h_expand,
  rw r at g_sep,

  cases (is_unit_or_eq_zero_of_separable_expand q s g_sep) with g'_is_unit s_zero,
  { rw [r, nat_degree_expand (q^s) g',
      nat_degree_eq_of_degree_eq_some (degree_eq_zero_of_is_unit g'_is_unit), zero_mul ] },
  { apply false.elim,
    exact (ne_of_lt hs.1).symm s_zero },
end

/-- If two expansions (along the positive characteristic) of two polynomials `g` and `g'` agree,
then they have the same degree or one of them is inseparable. -/
theorem contraction_degree_eq_or_insep
  [hq : fact q.prime] [char_p F q]
  (g g' : polynomial F) (m m' : ℕ)
  (h_expand : expand F (q^m) g = expand F (q^m') g') :
  (g.nat_degree = g'.nat_degree) ∨ ¬g.separable ∨ ¬g'.separable :=
begin
  by_cases h : m = m',
  { apply or.inl,
    -- if `m = m'` then we show `g.nat_degree = g'.nat_degree` by unfolding the definitions
    rw h at h_expand,
    have expand_deg : ((expand F (q ^ m')) g).nat_degree =
      (expand F (q ^ m') g').nat_degree, by rw h_expand,
    rw [nat_degree_expand (q^m') g, nat_degree_expand (q^m') g'] at expand_deg,
    apply nat.eq_of_mul_eq_mul_left (pow_pos hq.1.pos m'),
    rw [mul_comm] at expand_deg, rw expand_deg, rw [mul_comm] },
  { cases ne.lt_or_lt h,
    { rw ←or_assoc, -- if `m < m'`, we show that the degrees agree or that `g'` is not separable
      apply or.inl,
      apply contraction_degree_eq_aux q g g' m m' h_expand h_1 },
    { rw ←or.left_comm, -- if `m' < m`, we show that the degrees agree or that `g` is not separable
      apply or.inr,
      cases contraction_degree_eq_aux q g' g m' m h_expand.symm h_1,
      exact or.inl h_2.symm,
      exact or.inr h_2 } }
end

/-- The separable degree is unique. -/
theorem separable_degree_eq {n n' : ℕ} [hF : exp_char F q] :
  separable_degree q hf = n → separable_degree q hf = n' → n = n' :=
λ h, λ h',
begin
  casesI hF,
  { rw separable_degree_eq_degree hf at h h',
    rw h at h',
    exact h' },
  { let g := classical.some hf,
    cases (classical.some_spec hf).2 with m hm,

    let g' := classical.some hf,
    cases (classical.some_spec hf).2 with m' hm',

    suffices : g.nat_degree = g'.nat_degree ∨ ¬g.separable ∨ ¬g'.separable, by tidy,

    haveI : fact q.prime := fact_iff.2 hF_hprime,
    apply contraction_degree_eq_or_insep q g g' m m',
    rw [hm, hm'] }
end

end field

end polynomial
