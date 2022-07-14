/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.monoid_algebra.basic

/-!  #  Degree of an `add_monoid_algebra`

Let `R` be a semiring and let `A` be a `semilattice_sup`.

For an element `f : add_monoid_algebra R A`, this file defines
* `add_monoid_algebra.degree`: the degree taking values in `with_bot A`,
* `add_monoid_algebra.trailing_degree`: the trailing degree taking values in `with_top A`.
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

variables {R A B : Type*} [semiring R]

section general_results_assuming_semilattice_sup

section add_only
variables [has_add A]
variables [semilattice_sup B] [order_bot B] [has_add B]
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

variables [semilattice_sup B] [order_bot B]

lemma supo {R A B : Type*} [semilattice_sup B] [semiring R] [has_zero A] [has_zero B]
  {D : A → B} (D0 : D 0 ≤ 0) (b : A) (hb : b ∈ (1 : add_monoid_algebra R A).support) :
  D b ≤ 0 :=
by rwa [finset.mem_singleton.mp (finsupp.support_single_subset hb)]
--  exact λ a ha, by simpa [finset.mem_singleton.mp (finsupp.support_single_subset ha)]

lemma sup_support_list_prod_le [add_monoid A]
  [add_monoid B] [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
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

lemma cons {A B : Type*} [comm_monoid B]
  (f : A → B) (a : A) (s : multiset A) :
  (list.map f (a ::ₘ s).to_list).prod = f a * (multiset.map f s).prod :=
begin
  rw ← multiset.prod_to_list,
  rw multiset.add
  --library_search,
  admit,
end

@[to_additive]
lemma _root_.multiset.to_list_map_prod {ι A : Type*} [comm_monoid A]
  (s : multiset ι) (f : ι → A) :
  (s.to_list.map f).prod = (s.map f).prod :=
begin
  rw ← multiset.prod_to_list,
  apply finset.prod_congr
  sorry
end

lemma sup_support_multiset_prod_le {R} [comm_semiring R] [add_comm_monoid A] [add_comm_monoid B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  {D : A → B} (D0 : D 0 ≤ 0) (Dm : ∀ a b, D (a + b) ≤ D a + D b)
  (F : multiset (add_monoid_algebra R A)) :
  F.prod.support.sup D ≤ (F.map (λ f : add_monoid_algebra R A, f.support.sup D)).sum :=
begin
  rw ← F.prod_to_list,
  refine (sup_support_list_prod_le D0 Dm F.to_list).trans (le_of_eq _),
  exact (F.to_list_map_sum _),
end

lemma sup_support_multiset_prod_le {R} [comm_semiring R] [add_comm_monoid A] [add_comm_monoid B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  {D : A → B} (D0 : D 0 ≤ 0) (Dm : ∀ a b, D (a + b) ≤ D a + D b)
  (F : multiset (add_monoid_algebra R A)) :
  F.prod.support.sup D ≤ (F.map (λ f : add_monoid_algebra R A, f.support.sup D)).sum :=
begin
  apply F.induction_on,
  { rw [multiset.prod_zero, multiset.map_zero, multiset.sum_zero, finset.sup_le_iff],
    exact λ a ha, by rwa [finset.mem_singleton.mp (finsupp.support_single_subset ha)] },
  { simp only [finset.sup_le_iff, multiset.prod_cons, multiset.map_cons, multiset.sum_cons],
    intros f F hF a ha,
    obtain ⟨c, cf, b, bg, rfl⟩ : ∃ c, c ∈ f.support ∧ ∃ b, b ∈ F.prod.support ∧ a = c + b,
    { simpa only [finset.mem_bUnion, finset.mem_singleton, exists_prop]
        using f.support_mul F.prod ha },
    exact (Dm _ _).trans (add_le_add (finset.le_sup cf) (hF _ bg)) }
end

lemma sup_support_finset_prod_le {R} [comm_semiring R] [add_comm_monoid A] [add_comm_monoid B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  {D : A → B} (D0 : D 0 ≤ 0) (Dm : ∀ a b, D (a + b) ≤ D a + D b)
  (F : finset (add_monoid_algebra R A)) :
  (finset.prod F id).support.sup D ≤ finset.sum F (λ f, f.support.sup D) :=
begin
  rcases F with ⟨F, hF⟩,
  rw [finset.prod_mk, multiset.map_id],
  exact sup_support_multiset_prod_le D0 Dm F,
end

lemma sup_support_pow_le {R} [comm_semiring R] [add_monoid A] [add_monoid B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  {D : A → B} (D0 : D 0 ≤ 0) (Dm : ∀ a b, D (a + b) ≤ D a + D b) (n : ℕ)
  (f : add_monoid_algebra R A) :
  (f ^ n).support.sup D ≤ n • (f.support.sup D) :=
begin
  induction n with n hn,
  { simpa only [pow_zero, zero_smul, finset.sup_le_iff] using supo D0 },
  { rw [pow_succ, succ_nsmul],
    exact (sup_support_mul_le Dm _ _).trans (add_le_add rfl.le hn) }
end

end general_results_assuming_semilattice_sup

section degrees

section degree

variables [semilattice_sup A]

/--  Let `R` be a semiring, let `A` be a `semilattice_sup`, and let `f : R[A]` be an
an element of `add_monoid_algebra R A`.  The degree of `f` takes values in `with_bot A` and
it is the supremum of the support of `f` or `⊥`, depending on whether `f` is non-zero or not.

If `A` has a linear order, then this notion coincides with the usual one, using the maximum of
the exponents. -/
def degree (f : add_monoid_algebra R A) : with_bot A :=
f.support.sup coe

variables [add_monoid A] [covariant_class A A (+) (≤)] [covariant_class A A (function.swap (+)) (≤)]
variables (f g : add_monoid_algebra R A)

lemma degree_mul_le : (f * g).degree ≤ f.degree + g.degree :=
sup_support_mul_le (λ a b, (with_bot.coe_add _ _).le) f g

end degree

section trailing_degree

variables [semilattice_inf A]

/--  Let `R` be a semiring, let `A` be a `semilattice_inf`, and let `f : R[A]` be an
an element of `add_monoid_algebra R A`.  The trailing degree of `f` takes values in `with_top A`
and it is the infimum of the support of `f` or `⊤`, depending on whether `f` is non-zero or not.

If `A` has a linear order, then this notion coincides with the usual one, using the minimum of
the exponents. -/
def trailing_degree (f : add_monoid_algebra R A) : with_top A :=
f.support.inf coe

variables [add_monoid A] [covariant_class A A (+) (≤)] [covariant_class A A (function.swap (+)) (≤)]
  (f g : add_monoid_algebra R A)

lemma le_trailing_degree_mul :
  f.trailing_degree + g.trailing_degree ≤ (f * g).trailing_degree :=
sup_support_mul_le (λ a b : Aᵒᵈ, (with_bot.coe_add _ _).le) _ _

end trailing_degree

end degrees

end add_monoid_algebra
