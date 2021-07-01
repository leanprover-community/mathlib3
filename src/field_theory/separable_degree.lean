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

- `is_separable_contraction`: is the condition that `g(x^(q^m)) = f(x)` for some `m : ℕ`
- `has_separable_contraction`: the condition of having a separable contraction
- `has_separable_contraction.degree`: the separable degree, defined as the degree of some
  separable contraction
- `irreducible_has_separable_contraction`: any nonzero irreducible polynomial can be contracted
  to a separable polynomial
- `has_separable_contraction.dvd_degree'`: the degree of a separable contraction divides the degree,
  in function of the exponential characteristic of the field
- `has_separable_contraction.dvd_degree` and `has_separable_contraction.eq_degree` specialize the
  statement of `separable_degree_dvd_degree`
- `is_separable_contraction.degree_eq`: the separable degree is well-defined, implemented as the
  statement that the degree of any separable contraction equals `has_separable_contraction.degree`

## Tags

separable degree, degree, polynomial
-/

namespace polynomial

noncomputable theory
open_locale classical

section comm_semiring

variables {F : Type} [comm_semiring F] (q : ℕ)

/-- A separable contraction of a polynomial `f` is a separable polynomial `g` such that
`g(x^(q^m)) = f(x)` for some `m : ℕ`.-/
def is_separable_contraction (f : polynomial F) (g : polynomial F) : Prop :=
g.separable ∧ ∃ m : ℕ, expand F (q^m) g = f

/-- The condition of having a separable contration. -/
def has_separable_contraction (f : polynomial F) : Prop :=
∃ g : polynomial F, is_separable_contraction q f g

variables {q} {f : polynomial F} (hf : has_separable_contraction q f)

/-- A choice of a separable contraction. -/
def has_separable_contraction.contraction : polynomial F := classical.some hf

/-- The separable degree of a polynomial is the degree of a given separable contraction. -/
def has_separable_contraction.degree : ℕ := hf.contraction.nat_degree

/-- The separable degree divides the degree, in function of the exponential characteristic of F. -/
lemma is_separable_contraction.dvd_degree' {g} (hf : is_separable_contraction q f g) :
  ∃ m : ℕ, g.nat_degree * (q ^ m) = f.nat_degree :=
begin
  obtain ⟨m, rfl⟩ := hf.2,
  use m,
  rw nat_degree_expand,
end

lemma has_separable_contraction.dvd_degree' : ∃ m : ℕ, hf.degree * (q ^ m) = f.nat_degree :=
(classical.some_spec hf).dvd_degree'

/-- The separable degree divides the degree. -/
lemma has_separable_contraction.dvd_degree :
  hf.degree ∣ f.nat_degree :=
let ⟨a, ha⟩ := hf.dvd_degree' in dvd.intro (q ^ a) ha

/-- In exponential characteristic one, the separable degree equals the degree. -/
lemma has_separable_contraction.eq_degree {f : polynomial F}
  (hf : has_separable_contraction 1 f) : hf.degree = f.nat_degree :=
let ⟨a, ha⟩ := hf.dvd_degree' in by rw [←ha, one_pow a, mul_one]

end comm_semiring

section field

variables {F : Type} [field F]
variables (q : ℕ) {f : polynomial F} (hf : has_separable_contraction q f)

/-- Every irreducible polynomial can be contracted to a separable polynomial.
https://stacks.math.columbia.edu/tag/09H0 -/
lemma irreducible_has_separable_contraction (q : ℕ) [hF : exp_char F q]
  (f : polynomial F) [irred : irreducible f] (fn : f ≠ 0) : has_separable_contraction q f :=
begin
  casesI hF,
  { use f,
    exact ⟨irreducible.separable irred, ⟨0, by rw [pow_zero, expand_one]⟩⟩ },
  { haveI qp : fact (nat.prime q) := ⟨hF_hprime⟩,
    rcases exists_separable_of_irreducible q irred fn with ⟨n, g, hgs, hge⟩,
    exact ⟨g, hgs, n, hge⟩, }
end

/-- A helper lemma: if two expansions (along the positive characteristic) of two polynomials `g` and
`g'` agree, and the one with the larger degree is separable, then their degrees are the same. -/
lemma contraction_degree_eq_aux [hq : fact q.prime] [hF : char_p F q]
  (g g' : polynomial F) (m m' : ℕ)
  (h_expand : expand F (q^m) g = expand F (q^m') g')
  (h : m < m') (hg : g.separable):
  g.nat_degree =  g'.nat_degree :=
begin
  obtain ⟨s, rfl⟩ := nat.exists_eq_add_of_lt h,
  rw [add_assoc, pow_add, expand_mul] at h_expand,
  let aux := expand_injective (pow_pos hq.1.pos m) h_expand,
  rw aux at hg,
  have := (is_unit_or_eq_zero_of_separable_expand q (s + 1) hg).resolve_right
    s.succ_ne_zero,
  rw [aux, nat_degree_expand,
    nat_degree_eq_of_degree_eq_some (degree_eq_zero_of_is_unit this),
    zero_mul]
end

/-- If two expansions (along the positive characteristic) of two separable polynomials
`g` and `g'` agree, then they have the same degree. -/
theorem contraction_degree_eq_or_insep
  [hq : fact q.prime] [char_p F q]
  (g g' : polynomial F) (m m' : ℕ)
  (h_expand : expand F (q^m) g = expand F (q^m') g')
  (hg : g.separable) (hg' : g'.separable) :
  g.nat_degree = g'.nat_degree :=
begin
  by_cases h : m = m',
  { -- if `m = m'` then we show `g.nat_degree = g'.nat_degree` by unfolding the definitions
    rw h at h_expand,
    have expand_deg : ((expand F (q ^ m')) g).nat_degree =
      (expand F (q ^ m') g').nat_degree, by rw h_expand,
    rw [nat_degree_expand (q^m') g, nat_degree_expand (q^m') g'] at expand_deg,
    apply nat.eq_of_mul_eq_mul_left (pow_pos hq.1.pos m'),
    rw [mul_comm] at expand_deg, rw expand_deg, rw [mul_comm] },
  { cases ne.lt_or_lt h,
    { exact contraction_degree_eq_aux q g g' m m' h_expand h_1 hg },
    { exact (contraction_degree_eq_aux q g' g m' m h_expand.symm h_1 hg').symm, } }
end

/-- The separable degree equals the degree of any separable contraction, i.e., it is unique. -/
theorem is_separable_contraction.degree_eq [hF : exp_char F q]
  (g : polynomial F) (hg : is_separable_contraction q f g) :
  g.nat_degree = hf.degree :=
begin
  casesI hF,
  { rcases hg with ⟨g, m, hm⟩,
    rw [one_pow, expand_one] at hm,
    rw hf.eq_degree,
    rw hm, },
  { rcases hg with ⟨hg, m, hm⟩,
    let g' := classical.some hf,
    cases (classical.some_spec hf).2 with m' hm',
    haveI : fact q.prime := fact_iff.2 hF_hprime,
    apply contraction_degree_eq_or_insep q g g' m m',
    rw [hm, hm'],
    exact hg, exact (classical.some_spec hf).1 }
end

end field

end polynomial
