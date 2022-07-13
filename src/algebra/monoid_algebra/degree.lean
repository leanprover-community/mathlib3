/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.monoid_algebra.basic
import data.multiset.lattice
/-!  #  Degree of an `add_monoid_algebra`

Let `R` be a semiring and let `A` be a `semilattice_sup`.

For an element `f : add_monoid_algebra R A`, this file defines
* the degree `f.degree` taking values in `with_bot A`,
* the trailing degree `f.trailing_degree` taking values in `with_top A`.
If the grading type `A` is a linearly ordered additive monoid, then this notions of degree
coincide with the standard one:
* the degree is the maximum of the exponents of the monomials that appear with non-zero
  coefficient in `f`, or `⊥`, if `f = 0`;
* the trailing degree is the minimum of the exponents of the monomials that appear with non-zero
  coefficient in `f`, or `⊤`, if `f = 0`.

Currently, the only results are
* `degree_mul_le` -- the degree of a product is at most the sum of the degrees,
*  `le_trailing_degree_mul` -- the trailing degree of a product is at least the sum of the
  trailing degrees.
-/

namespace add_monoid_algebra
open_locale classical

variables {R A : Type*} [semiring R]

section degree
variables [semilattice_sup A]

/--  Let `R` be a semiring, let `A` be a Type with a linear order, and let `f : R[A]` be an
an element of `add_monoid_algebra R A`.  The degree of `f` takes values in `with_bot A` and
it is the maximum of the support of `f` or `⊥`, depending on whether `f` is non-zero or not. -/
def degree (f : add_monoid_algebra R A) : with_bot A :=
f.support.sup coe

variables [add_monoid A] [covariant_class A A (+) (≤)] [covariant_class A A (function.swap (+)) (≤)]

lemma degree_mul_le (f g : add_monoid_algebra R A) :
  (f * g).degree ≤ f.degree + g.degree :=
begin
  refine (finset.sup_le (λ d ds, _)),
  obtain ⟨a, af, b, bg, rfl⟩ : ∃ a, a ∈ f.support ∧ ∃ b, b ∈ g.support ∧ d = a + b,
  { simpa only [finset.mem_bUnion, finset.mem_singleton, exists_prop] using f.support_mul g ds },
  refine (with_bot.coe_add _ _).le.trans (add_le_add _ _);
  exact finset.le_sup ‹_›,
end

end degree

section trailing_degree

variables [semilattice_inf A]

/--  Let `R` be a semiring, let `A` be a Type with a linear order, and let `f : R[A]` be an
an element of `add_monoid_algebra R A`.  The trailing degree of `f` takes values in `with_top A`
and it is the minimum of the support of `f` or `⊤`, depending on whether `f` is non-zero or not. -/
def trailing_degree (f : add_monoid_algebra R A) : with_top A :=
f.support.inf coe

variables [add_monoid A] [covariant_class A A (+) (≤)] [covariant_class A A (function.swap (+)) (≤)]

lemma le_trailing_degree_mul (f g : add_monoid_algebra R A) :
  f.trailing_degree + g.trailing_degree ≤ (f * g).trailing_degree :=
begin
  refine (finset.le_inf (λ d ds, _)),
  obtain ⟨a, af, b, bg, rfl⟩ : ∃ a, a ∈ f.support ∧ ∃ b, b ∈ g.support ∧ d = a + b,
  { simpa only [finset.mem_bUnion, finset.mem_singleton, exists_prop] using f.support_mul g ds },
  refine (add_le_add _ _).trans (with_bot.coe_add _ _).ge;
  exact finset.inf_le ‹_›,
end

end trailing_degree

end add_monoid_algebra
