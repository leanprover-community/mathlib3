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

## Tags
separable degree, degree, polynomial
-/

noncomputable theory
open_locale classical

variables {F : Type} [comm_semiring F]
  (q : ℕ) [exp_char F q]

/-- A separable contraction of a polynomial `f` is a separable polynomial `g` such that 
`g(x^(q^m)) = f(x)` for some `m : ℕ`.-/
class has_separable_contraction (f : polynomial F) : Prop :=
(has_separable_contraction' : ∃ g : polynomial F,
  g.separable ∧ ∃ m : ℕ, polynomial.expand F (q^m) g = f)

/-- A choice of a separable contraction. -/
def separable_contraction (f : polynomial F) [hf : has_separable_contraction q f] :
  polynomial F := classical.some hf.has_separable_contraction'

/-- The separable degree of a polynomial is the degree of a given separable contraction. -/
def separable_degree (f : polynomial F) [has_separable_contraction q f] : ℕ :=
polynomial.nat_degree (separable_contraction q f)

/-- Every irreducible polynomial can be contracted to a separable polynomial.
https://stacks.math.columbia.edu/tag/09H0 -/
lemma irreducible_has_separable_contraction {F : Type} [field F] (q : ℕ) [hF : exp_char F q]
  (f : polynomial F) (irred : irreducible f) (fn : f ≠ 0) : has_separable_contraction q f :=
begin
  casesI hF,
  { use f,
    exact ⟨irreducible.separable irred, ⟨0, by rw [one_pow, polynomial.expand_one]⟩⟩ },
  { haveI qp : fact (nat.prime q) := fact_iff.mpr hF_hprime,
    rcases polynomial.exists_separable_of_irreducible q irred fn with ⟨n, g, hg⟩,
    use g,
    exact ⟨hg.1, ⟨n, hg.2⟩⟩, }
end

/-- The separable degree divides the degree, in function of the exponential characteristic of F. -/
lemma separable_degree_dvd_degree' (f : polynomial F) [hf : has_separable_contraction q f] :
  ∃ m : ℕ, (separable_degree q f) * (q ^ m) = f.nat_degree :=
begin
  cases (classical.some_spec hf.has_separable_contraction').2 with m hm,
  use m,
  let g := classical.some hf.has_separable_contraction',
  have deg_g : g.nat_degree = separable_degree q f, by refl,
  rw [←deg_g, ←hm, polynomial.nat_degree_expand (q^m) g, mul_comm],
end

/-- The separable degree divides the degree. -/
lemma separable_degree_dvd_degree (f : polynomial F) [hf : has_separable_contraction q f] :
  (separable_degree q f) ∣ f.nat_degree :=
begin
  cases separable_degree_dvd_degree' q f with m hm,
  use q^m,
  rw hm,
end

/-- In exponential characteristic one, the separable degree equals the degree. -/
lemma separable_degree_eq_degree (f : polynomial F) [exp_char F 1]
  [hf : has_separable_contraction 1 f] : (separable_degree 1 f) = f.nat_degree :=
begin
  cases separable_degree_dvd_degree' 1 f with m hm,
  rw [one_pow m, mul_one] at hm,
  exact hm,
end
