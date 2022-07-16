/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.monoid_algebra.basic

/-!
# Max-degree and min-degree of an `add_monoid_algebra`

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

The main results are
* `add_monoid_algebra.max_degree_mul_le`:
  the max-degree of a product is at most the sum of the max-degrees,
* `add_monoid_algebra.le_min_degree_mul`:
  the min-degree of a product is at least the sum of the min-degrees,
* `add_monoid_algebra.max_degree_add_le`:
  the max-degree of a sum is at most the sup of the max-degrees,
* `add_monoid_algebra.le_min_degree_add`:
  the min-degree of a sum is at least the inf of the min-degrees.

## Implementation notes

The current plan is to state and prove lemmas about `finset.sup (finsupp.support f) D` with a
"generic" degree/weight function `D` from the grading Type `A` to a somewhat ordered Type `B`.

Next, the general lemmas get specialized twice:
* once for `max_degree` (essentially a simple application) and
* once for `min_degree` (a simple application, via `order_dual`).
These final lemmas are the ones that likely get used the most.  The generic lemmas about
`finset.support.sup` may not be used directly much outside of this file.

To see this in action, you can look at the triple
`(sup_support_mul_le, max_degree_mul_le, le_min_degree_mul)`.
-/

variables {R A T B ι : Type*}

namespace add_monoid_algebra
open_locale classical big_operators

/-! ### Results about the `finset.sup` and `finset.inf` of `finsupp.support` -/

section general_results_assuming_semilattice_sup
variables [semilattice_sup B] [order_bot B] [semilattice_inf T] [order_top T]

section semiring

variables [semiring R]

section explicit_Ds
variables (DB : A → B) (DT : A → T) (f g : add_monoid_algebra R A)

lemma sup_support_add_le : (f + g).support.sup DB ≤ (f.support.sup DB) ⊔ (g.support.sup DB) :=
begin
  refine (finset.sup_le (λ d ds, _)),
  cases finset.mem_union.mp (finsupp.support_add ds) with df dg,
  { exact (finset.le_sup df).trans le_sup_left },
  { exact (finset.le_sup dg).trans le_sup_right }
end

lemma le_inf_support_add : f.support.inf DT ⊓ g.support.inf DT ≤ (f + g).support.inf DT :=
sup_support_add_le (λ a : A, order_dual.to_dual (DT a)) f g

end explicit_Ds

section add_only
variables [has_add A] [has_add B] [has_add T]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  [covariant_class T T (+) (≤)] [covariant_class T T (function.swap (+)) (≤)]

lemma sup_support_mul_le {DB : A → B} (DBm : ∀ {a b}, DB (a + b) ≤ DB a + DB b)
  (f g : add_monoid_algebra R A) :
  (f * g).support.sup DB ≤ f.support.sup DB + g.support.sup DB :=
begin
  refine (finset.sup_le (λ d ds, _)),
  obtain ⟨a, af, b, bg, rfl⟩ : ∃ a, a ∈ f.support ∧ ∃ b, b ∈ g.support ∧ d = a + b,
  { simpa only [finset.mem_bUnion, finset.mem_singleton, exists_prop] using f.support_mul g ds },
  refine DBm.trans (add_le_add _ _);
  exact finset.le_sup ‹_›,
end

lemma le_inf_support_mul {DT : A → T} (DTm : ∀ {a b}, DT a + DT b ≤ DT (a + b))
  (f g : add_monoid_algebra R A) :
  f.support.inf DT + g.support.inf DT ≤ (f * g).support.inf DT :=
order_dual.of_dual_le_of_dual.mpr $
  sup_support_mul_le (λ a b, order_dual.of_dual_le_of_dual.mp DTm) f g

end add_only

section add_monoids
variables [add_monoid A]
  [add_monoid B] [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  [add_monoid T] [covariant_class T T (+) (≤)] [covariant_class T T (function.swap (+)) (≤)]
  {DB : A → B} {DT : A → T}

lemma sup_support_list_prod_le (DB0 : DB 0 ≤ 0) (DBm : ∀ a b, DB (a + b) ≤ DB a + DB b) :
  ∀ l : list (add_monoid_algebra R A),
    l.prod.support.sup DB ≤ (l.map (λ f : add_monoid_algebra R A, f.support.sup DB)).sum
| [] := begin
    rw [list.map_nil, finset.sup_le_iff, list.prod_nil, list.sum_nil],
    exact λ a ha, by rwa [finset.mem_singleton.mp (finsupp.support_single_subset ha)]
  end
| (f::fs) := begin
    rw [list.prod_cons, list.map_cons, list.sum_cons],
    exact (sup_support_mul_le DBm _ _).trans (add_le_add_left (sup_support_list_prod_le _) _)
  end

lemma le_inf_support_sum (DT0 : 0 ≤ DT 0) (DTm : ∀ a b, DT a + DT b ≤ DT (a + b))
  (l : list (add_monoid_algebra R A)) :
  (l.map (λ f : add_monoid_algebra R A, f.support.inf DT)).sum ≤ l.prod.support.inf DT :=
order_dual.of_dual_le_of_dual.mpr $ sup_support_list_prod_le (order_dual.of_dual_le_of_dual.mp DT0)
  (λ a b, order_dual.of_dual_le_of_dual.mp (DTm _ _)) l

lemma sup_support_pow_le (DB0 : DB 0 ≤ 0) (DBm : ∀ a b, DB (a + b) ≤ DB a + DB b) (n : ℕ)
  (f : add_monoid_algebra R A) :
  (f ^ n).support.sup DB ≤ n • (f.support.sup DB) :=
begin
  rw [← list.prod_repeat, ←list.sum_repeat],
  refine (sup_support_list_prod_le DB0 DBm _).trans_eq _,
  rw list.map_repeat,
end

lemma le_inf_support_pow (DT0 : 0 ≤ DT 0) (DTm : ∀ a b, DT a + DT b ≤ DT (a + b)) (n : ℕ)
  (f : add_monoid_algebra R A) :
  n • (f.support.inf DT) ≤ (f ^ n).support.inf DT :=
order_dual.of_dual_le_of_dual.mpr $ sup_support_pow_le (order_dual.of_dual_le_of_dual.mp DT0)
  (λ a b, order_dual.of_dual_le_of_dual.mp (DTm _ _)) n f

end add_monoids

end semiring

section commutative_lemmas
variables [comm_semiring R] [add_comm_monoid A]
  [add_comm_monoid B] [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  [add_comm_monoid T] [covariant_class T T (+) (≤)] [covariant_class T T (function.swap (+)) (≤)]
  {DB : A → B} {DT : A → T}

lemma sup_support_multiset_prod_le
  (DB0 : DB 0 ≤ 0) (DBm : ∀ a b, DB (a + b) ≤ DB a + DB b)
  (m : multiset (add_monoid_algebra R A)) :
  m.prod.support.sup DB ≤ (m.map (λ f : add_monoid_algebra R A, f.support.sup DB)).sum :=
begin
  induction m using quot.induction_on,
  rw [multiset.quot_mk_to_coe'', multiset.coe_map, multiset.coe_sum, multiset.coe_prod],
  exact sup_support_list_prod_le DB0 DBm m,
end

lemma le_inf_support_multiset_prod
  (DT0 : 0 ≤ DT 0) (DTm : ∀ a b, DT a + DT b ≤ DT (a + b))
  (F : multiset (add_monoid_algebra R A)) :
  (F.map (λ f : add_monoid_algebra R A, f.support.inf DT)).sum ≤ F.prod.support.inf DT :=
order_dual.of_dual_le_of_dual.mpr $
  sup_support_multiset_prod_le (order_dual.of_dual_le_of_dual.mp DT0)
    (λ a b, order_dual.of_dual_le_of_dual.mp (DTm _ _)) F

lemma sup_support_finset_prod_le
  (DB0 : DB 0 ≤ 0) (DBm : ∀ a b, DB (a + b) ≤ DB a + DB b)
  (s : finset ι) (f : ι → add_monoid_algebra R A):
  (∏ i in s, f i).support.sup DB ≤ ∑ i in s, (f i).support.sup DB :=
(sup_support_multiset_prod_le DB0 DBm _).trans_eq $ congr_arg _ $ multiset.map_map _ _ _

lemma finset_sum_inf_support_le
  (DT0 : 0 ≤ DT 0) (DTm : ∀ a b, DT a + DT b ≤ DT (a + b))
  (s : finset ι) (f : ι → add_monoid_algebra R A):
  ∑ i in s, (f i).support.inf DT ≤ (∏ i in s, f i).support.inf DT :=
order_dual.of_dual_le_of_dual.mpr $
  sup_support_finset_prod_le (order_dual.of_dual_le_of_dual.mp DT0)
    (λ a b, order_dual.of_dual_le_of_dual.mp (DTm _ _)) s f

end commutative_lemmas

end general_results_assuming_semilattice_sup

/-! ### Shorthands for special cases

Note that these definitions are reducible, in order to make it easier to apply the more generic
lemmas above. -/

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

lemma max_degree_add_le (f g : add_monoid_algebra R A) :
  (f + g).max_degree ≤ f.max_degree ⊔ g.max_degree :=
sup_support_add_le coe f g

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

lemma le_min_degree_add (f g : add_monoid_algebra R A) :
  f.min_degree ⊓ g.min_degree ≤ (f + g).min_degree :=
sup_support_add_le (coe : Aᵒᵈ → with_bot Aᵒᵈ) f g

variables [add_monoid A] [covariant_class A A (+) (≤)] [covariant_class A A (function.swap (+)) (≤)]
  (f g : add_monoid_algebra R A)

lemma le_min_degree_mul : f.min_degree + g.min_degree ≤ (f * g).min_degree :=
sup_support_mul_le (λ a b : Aᵒᵈ, (with_bot.coe_add _ _).le) _ _

end min_degree

end degrees

end add_monoid_algebra
