/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
import algebra.algebra.basic
import algebra.char_p.exp_char
import field_theory.separable

/-!

# Separable degree

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains basics about the separable degree of a polynomial.

## Main results

- `is_separable_contraction`: is the condition that, for `g` a separable polynomial, we have that
   `g(x^(q^m)) = f(x)` for some `m : ℕ`.
- `has_separable_contraction`: the condition of having a separable contraction
- `has_separable_contraction.degree`: the separable degree, defined as the degree of some
  separable contraction
- `irreducible.has_separable_contraction`: any irreducible polynomial can be contracted
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
open_locale classical polynomial

section comm_semiring

variables {F : Type*} [comm_semiring F] (q : ℕ)

/-- A separable contraction of a polynomial `f` is a separable polynomial `g` such that
`g(x^(q^m)) = f(x)` for some `m : ℕ`.-/
def is_separable_contraction (f : F[X]) (g : F[X]) : Prop :=
g.separable ∧ ∃ m : ℕ, expand F (q^m) g = f

/-- The condition of having a separable contration. -/
def has_separable_contraction (f : F[X]) : Prop :=
∃ g : F[X], is_separable_contraction q f g

variables {q} {f : F[X]} (hf : has_separable_contraction q f)

/-- A choice of a separable contraction. -/
def has_separable_contraction.contraction : F[X] := classical.some hf

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
lemma has_separable_contraction.eq_degree {f : F[X]}
  (hf : has_separable_contraction 1 f) : hf.degree = f.nat_degree :=
let ⟨a, ha⟩ := hf.dvd_degree' in by rw [←ha, one_pow a, mul_one]

end comm_semiring

section field

variables {F : Type*} [field F]
variables (q : ℕ) {f : F[X]} (hf : has_separable_contraction q f)

/-- Every irreducible polynomial can be contracted to a separable polynomial.
https://stacks.math.columbia.edu/tag/09H0 -/
lemma _root_.irreducible.has_separable_contraction (q : ℕ) [hF : exp_char F q]
  (f : F[X]) (irred : irreducible f) : has_separable_contraction q f :=
begin
  casesI hF,
  { exact ⟨f, irred.separable, ⟨0, by rw [pow_zero, expand_one]⟩⟩ },
  { rcases exists_separable_of_irreducible q irred ‹q.prime›.ne_zero with ⟨n, g, hgs, hge⟩,
    exact ⟨g, hgs, n, hge⟩, }
end

/-- If two expansions (along the positive characteristic) of two separable polynomials `g` and `g'`
agree, then they have the same degree. -/
theorem contraction_degree_eq_or_insep
  [hq : ne_zero q] [char_p F q]
  (g g' : F[X]) (m m' : ℕ)
  (h_expand : expand F (q^m) g = expand F (q^m') g')
  (hg : g.separable) (hg' : g'.separable) :
  g.nat_degree = g'.nat_degree :=
begin
  wlog hm : m ≤ m',
  { exact (this g' g m' m h_expand.symm hg' hg (le_of_not_le hm)).symm },
  obtain ⟨s, rfl⟩ := exists_add_of_le hm,
  rw [pow_add, expand_mul, expand_inj (pow_pos (ne_zero.pos q) m)] at h_expand,
  subst h_expand,
  rcases is_unit_or_eq_zero_of_separable_expand q s (ne_zero.pos q) hg with h | rfl,
  { rw [nat_degree_expand, nat_degree_eq_zero_of_is_unit h, zero_mul] },
  { rw [nat_degree_expand, pow_zero, mul_one] },
end

/-- The separable degree equals the degree of any separable contraction, i.e., it is unique. -/
theorem is_separable_contraction.degree_eq [hF : exp_char F q]
  (g : F[X]) (hg : is_separable_contraction q f g) :
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
