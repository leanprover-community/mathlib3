/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.monoid_algebra.basic
import data.multiset.lattice
/-!  #  Degree of an `add_monoid_algebra`

Let `R` be a semiring, let `A` be a Type with a linear order.

This file defines the degree of an element of `add_monoid_algebra R A`.  It takes values in
the grading Type `A` to which we add an element `⊥`, smaller than all the elements of `A`.

Currently, the only result is `degree_mul_le`: the degree of a product is at most the sum of the
degrees. -/

namespace add_monoid_algebra
open_locale classical

variables {R A : Type*} [semiring R] [semilattice_sup A]

/--  Let `R` be a semiring, let `A` be a Type with a linear order, and let `f : R[A]` be an
an element of `add_monoid_algebra R A`.  The degree of `f` takes values in `with_bot A` and
it is the maximum of the support of `f` or `⊥`, depending on whether `f` is non-zero or not. -/
def degree (f : add_monoid_algebra R A) : with_bot A :=
f.support.sup coe

section degree

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

end add_monoid_algebra
