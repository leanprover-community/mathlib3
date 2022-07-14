/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.monoid_algebra.basic

/-!  #  Max-degree and min-degree of an `add_monoid_algebra`

Let `R` be a semiring and let `A` be a `semilattice_sup`.

For an element `f : add_monoid_algebra R A`, this file defines
* `add_monoid_algebra.max_degree`: the max-degree taking values in `with_bot A`,
* `add_monoid_algebra.min_degree`: the min-degree taking values in `with_top A`.
If the grading type `A` is a linearly ordered additive monoid, then these two notions of degree
coincide with the standard one:
* the max-degree is the maximum of the exponents of the monomials that appear with non-zero
  coefficient in `f`, or `⊥`, if `f = 0`;
* the min-degree is the minimum of the exponents of the monomials that appear with non-zero
  coefficient in `f`, or `⊤`, if `f = 0`.

Currently, the only results are
* `max_degree_mul_le` -- the max-degree of a product is at most the sum of the max-degrees,
* `le_min_degree_mul` -- the min-degree of a product is at least the sum of the min-degrees.
-/

variables {R A B ι : Type*} [semilattice_sup B] [order_bot B]

namespace add_monoid_algebra
open_locale classical big_operators

section general_results_assuming_semilattice_sup

section semiring

variables [semiring R]

section add_only

variables [has_add A] [has_add B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]

lemma sup_support_mul_le {D : A → B} (Dm : ∀ {a b}, D (a + b) ≤ D a + D b)
  (f g : add_monoid_algebra R A) :
  (f * g).support.sup D ≤ f.support.sup D + g.support.sup D :=
begin
  refine (finset.sup_le (λ d ds, _)),
  obtain ⟨a, af, b, bg, rfl⟩ : ∃ a, a ∈ f.support ∧ ∃ b, b ∈ g.support ∧ d = a + b,
  { simpa only [finset.mem_bUnion, finset.mem_singleton, exists_prop] using f.support_mul g ds },
  refine Dm.trans (add_le_add _ _);
  exact finset.le_sup ‹_›,
end

end add_only

lemma sup_support_list_prod_le [add_monoid A] [add_monoid B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  {D : A → B} (D0 : D 0 ≤ 0) (Dm : ∀ a b, D (a + b) ≤ D a + D b) :
  ∀ F : list (add_monoid_algebra R A),
    F.prod.support.sup D ≤ (F.map (λ f : add_monoid_algebra R A, f.support.sup D)).sum
| [] := begin
    rw [list.map_nil, finset.sup_le_iff, list.prod_nil, list.sum_nil],
    exact λ a ha, by rwa [finset.mem_singleton.mp (finsupp.support_single_subset ha)]
  end
| (f::fs) := begin
    rw [list.prod_cons, list.map_cons, list.sum_cons],
    exact (sup_support_mul_le Dm _ _).trans (add_le_add_left (sup_support_list_prod_le _) _)
  end

end semiring

lemma sup_support_pow_le [comm_semiring R] [add_monoid A] [add_monoid B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  {D : A → B} (D0 : D 0 ≤ 0) (Dm : ∀ a b, D (a + b) ≤ D a + D b) (n : ℕ)
  (f : add_monoid_algebra R A) :
  (f ^ n).support.sup D ≤ n • (f.support.sup D) :=
begin
  induction n with n hn,
  { simp only [pow_zero, zero_smul, finset.sup_le_iff],
    exact λ a ha, by rwa finset.mem_singleton.mp (finsupp.support_single_subset ha) },
  { rw [pow_succ, succ_nsmul],
    exact (sup_support_mul_le Dm _ _).trans (add_le_add rfl.le hn) }
end

variables [comm_semiring R] [add_comm_monoid A] [add_comm_monoid B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]

lemma sup_support_multiset_prod_le
  {D : A → B} (D0 : D 0 ≤ 0) (Dm : ∀ a b, D (a + b) ≤ D a + D b)
  (F : multiset (add_monoid_algebra R A)) :
  F.prod.support.sup D ≤ (F.map (λ f : add_monoid_algebra R A, f.support.sup D)).sum :=
begin
  induction F using quot.induction_on,
  rw [multiset.quot_mk_to_coe'', multiset.coe_map, multiset.coe_sum, multiset.coe_prod],
  exact sup_support_list_prod_le D0 Dm F,
end

lemma sup_support_finset_prod_le
  {D : A → B} (D0 : D 0 ≤ 0) (Dm : ∀ a b, D (a + b) ≤ D a + D b)
  (s : finset ι) (f : ι → add_monoid_algebra R A):
  (∏ i in s, f i).support.sup D ≤ ∑ i in s, (f i).support.sup D :=
begin
  refine (sup_support_multiset_prod_le D0 Dm _).trans (le_of_eq _),
  simp only [multiset.map_map, function.comp_app],
  refl,
end

end general_results_assuming_semilattice_sup

section degrees

variables [semiring R]

section max_degree

variables [semilattice_sup A]

/--  Let `R` be a semiring, let `A` be a `semilattice_sup`, and let `f : R[A]` be an
an element of `add_monoid_algebra R A`.  The max-degree of `f` takes values in `with_bot A`
and it is the supremum of the support of `f` or `⊥`, depending on whether `f` is non-zero or not.

If `A` has a linear order, then this notion coincides with the usual one, using the maximum of
the exponents. -/
@[reducible] def max_degree (f : add_monoid_algebra R A) : with_bot A :=
f.support.sup coe

variables [add_monoid A] [covariant_class A A (+) (≤)] [covariant_class A A (function.swap (+)) (≤)]
variables (f g : add_monoid_algebra R A)

lemma max_degree_mul_le : (f * g).max_degree ≤ f.max_degree + g.max_degree :=
sup_support_mul_le (λ a b, (with_bot.coe_add _ _).le) f g

end max_degree

section min_degree

variables [semilattice_inf A]

/--  Let `R` be a semiring, let `A` be a `semilattice_inf`, and let `f : R[A]` be an
an element of `add_monoid_algebra R A`.  The min-degree of `f` takes values in `with_top A`
and it is the infimum of the support of `f` or `⊤`, depending on whether `f` is non-zero or not.

If `A` has a linear order, then this notion coincides with the usual one, using the minimum of
the exponents. -/
@[reducible] def min_degree (f : add_monoid_algebra R A) : with_top A :=
f.support.inf coe

variables [add_monoid A] [covariant_class A A (+) (≤)] [covariant_class A A (function.swap (+)) (≤)]
  (f g : add_monoid_algebra R A)

lemma le_min_degree_mul :
  f.min_degree + g.min_degree ≤ (f * g).min_degree :=
sup_support_mul_le (λ a b : Aᵒᵈ, (with_bot.coe_add _ _).le) _ _

end min_degree

end degrees

end add_monoid_algebra
