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

The main results are
* `add_monoid_algebra.max_degree_mul_le`: the max-degree of a product is at most the sum of the max-degrees,
* `add_monoid_algebra.le_min_degree_mul`: the min-degree of a product is at least the sum of the min-degrees,
* `add_monoid_algebra.max_degree_add_le`: the max-degree of a sum is at most the sup of the max-degrees,
* `le_min_degree_add`: the min-degree of a sum is at least the inf of the min-degrees.

## Implementation notes

The current plan is to state and prove lemmas about `finset.sup (finsupp.support f) D` with a "generic"
degree/weight function `D` from the grading Type `A` to a somewhat ordered Type `B`.

Next, the general lemmas get specialized twice:
* once for `max_degree` (essentially a simple application) and
* once for `min_degree` (a simple application, via `order_dual`).
These final lemmas are the ones that likely get used the most.  The generic lemmas about
`finset.support.sup` may not be used directly much outside of this file.

To see this in action, you can look at the triple
`(sup_support_mul_le, max_degree_mul_le, le_min_degree_mul)`.
-/

variables {R A B ι : Type*}

namespace add_monoid_algebra
open_locale classical big_operators


/-! ### Results about the `finset.sup` and `finset.inf` of `finsupp.support` -/

section general_results_assuming_semilattice_sup

section semiring

variables [semiring R]

lemma sup_support_add_le [semilattice_sup B] [order_bot B]
  (D : A → B) (f g : add_monoid_algebra R A) :
  (f + g).support.sup D ≤ (f.support.sup D) ⊔ (g.support.sup D) :=
begin
  refine (finset.sup_le (λ d ds, _)),
  cases finset.mem_union.mp (finsupp.support_add ds) with df dg,
  { exact (finset.le_sup df).trans le_sup_left },
  { exact (finset.le_sup dg).trans le_sup_right }
end

lemma le_inf_degree_add [semilattice_inf B] [order_top B]
  (D : A → B) (f g : add_monoid_algebra R A) :
  f.support.inf D ⊓ g.support.inf D ≤ (f + g).support.inf D :=
sup_support_add_le (λ a : A, order_dual.to_dual (D a)) f g

section add_only

variables [has_add A] [has_add B]

lemma sup_support_mul_le [semilattice_sup B] [order_bot B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  {D : A → B} (Dm : ∀ {a b}, D (a + b) ≤ D a + D b)
  (f g : add_monoid_algebra R A) :
  (f * g).support.sup D ≤ f.support.sup D + g.support.sup D :=
begin
  refine (finset.sup_le (λ d ds, _)),
  obtain ⟨a, af, b, bg, rfl⟩ : ∃ a, a ∈ f.support ∧ ∃ b, b ∈ g.support ∧ d = a + b,
  { simpa only [finset.mem_bUnion, finset.mem_singleton, exists_prop] using f.support_mul g ds },
  refine Dm.trans (add_le_add _ _);
  exact finset.le_sup ‹_›,
end

lemma le_inf_degree_mul [semilattice_inf B] [order_top B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  {D : A → B} (Dm : ∀ {a b}, D a + D b ≤ D (a + b))
  (f g : add_monoid_algebra R A) :
  f.support.inf D + g.support.inf D ≤ (f * g).support.inf D :=
order_dual.of_dual_le_of_dual.mpr $
  sup_support_mul_le (λ a b, order_dual.of_dual_le_of_dual.mp Dm) f g

end add_only

lemma sup_support_list_prod_le [add_monoid A] [add_monoid B] [semilattice_sup B] [order_bot B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  {D : A → B} (D0 : D 0 ≤ 0) (Dm : ∀ a b, D (a + b) ≤ D a + D b) :
  ∀ l : list (add_monoid_algebra R A),
    l.prod.support.sup D ≤ (l.map (λ f : add_monoid_algebra R A, f.support.sup D)).sum
| [] := begin
    rw [list.map_nil, finset.sup_le_iff, list.prod_nil, list.sum_nil],
    exact λ a ha, by rwa [finset.mem_singleton.mp (finsupp.support_single_subset ha)]
  end
| (f::fs) := begin
    rw [list.prod_cons, list.map_cons, list.sum_cons],
    exact (sup_support_mul_le Dm _ _).trans (add_le_add_left (sup_support_list_prod_le _) _)
  end

lemma list_prod_le_sup_support_sum [add_monoid A] [add_monoid B] [semilattice_inf B] [order_top B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)] {D : A → B}
  (D0 : 0 ≤ D 0) (Dm : ∀ a b, D a + D b ≤ D (a + b)) (l : list (add_monoid_algebra R A)) :
  (l.map (λ f : add_monoid_algebra R A, f.support.inf D)).sum ≤ l.prod.support.inf D :=
order_dual.of_dual_le_of_dual.mpr $ sup_support_list_prod_le (order_dual.of_dual_le_of_dual.mp D0)
  (λ a b, order_dual.of_dual_le_of_dual.mp (Dm _ _)) l

lemma sup_support_pow_le [add_monoid A] [add_monoid B] [semilattice_sup B] [order_bot B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  {D : A → B} (D0 : D 0 ≤ 0) (Dm : ∀ a b, D (a + b) ≤ D a + D b) (n : ℕ)
  (f : add_monoid_algebra R A) :
  (f ^ n).support.sup D ≤ n • (f.support.sup D) :=
begin
  rw [← list.prod_repeat, ←list.sum_repeat],
  refine (sup_support_list_prod_le D0 Dm _).trans_eq _,
  rw list.map_repeat,
end

lemma nsmul_inf_support_le_pow [add_monoid A] [add_monoid B] [semilattice_inf B] [order_top B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  {D : A → B} (D0 : 0 ≤ D 0) (Dm : ∀ a b, D a + D b ≤ D (a + b)) (n : ℕ)
  (f : add_monoid_algebra R A) :
  n • (f.support.inf D) ≤ (f ^ n).support.inf D :=
order_dual.of_dual_le_of_dual.mpr $ sup_support_pow_le (order_dual.of_dual_le_of_dual.mp D0)
  (λ a b, order_dual.of_dual_le_of_dual.mp (Dm _ _)) n f

end semiring

variables [comm_semiring R] [add_comm_monoid A] [add_comm_monoid B]

lemma sup_support_multiset_prod_le [semilattice_sup B] [order_bot B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  {D : A → B} (D0 : D 0 ≤ 0) (Dm : ∀ a b, D (a + b) ≤ D a + D b)
  (F : multiset (add_monoid_algebra R A)) :
  F.prod.support.sup D ≤ (F.map (λ f : add_monoid_algebra R A, f.support.sup D)).sum :=
begin
  induction F using quot.induction_on,
  rw [multiset.quot_mk_to_coe'', multiset.coe_map, multiset.coe_sum, multiset.coe_prod],
  exact sup_support_list_prod_le D0 Dm F,
end

lemma multiset_map_inf_support_sum_le [semilattice_inf B] [order_top B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  {D : A → B} (D0 : 0 ≤ D 0) (Dm : ∀ a b, D a + D b ≤ D (a + b))
  (F : multiset (add_monoid_algebra R A)) :
  (F.map (λ f : add_monoid_algebra R A, f.support.inf D)).sum ≤ F.prod.support.inf D :=
order_dual.of_dual_le_of_dual.mpr $
  sup_support_multiset_prod_le (order_dual.of_dual_le_of_dual.mp D0)
    (λ a b, order_dual.of_dual_le_of_dual.mp (Dm _ _)) F


lemma sup_support_finset_prod_le [semilattice_sup B] [order_bot B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  {D : A → B} (D0 : D 0 ≤ 0) (Dm : ∀ a b, D (a + b) ≤ D a + D b)
  (s : finset ι) (f : ι → add_monoid_algebra R A):
  (∏ i in s, f i).support.sup D ≤ ∑ i in s, (f i).support.sup D :=
(sup_support_multiset_prod_le D0 Dm _).trans_eq $ congr_arg _ $ multiset.map_map _ _ _

lemma finset_sum_inf_support_le [semilattice_inf B] [order_top B]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  {D : A → B} (D0 : 0 ≤ D 0) (Dm : ∀ a b, D a + D b ≤ D (a + b))
  (s : finset ι) (f : ι → add_monoid_algebra R A):
  ∑ i in s, (f i).support.inf D ≤ (∏ i in s, f i).support.inf D :=
order_dual.of_dual_le_of_dual.mpr $
  sup_support_finset_prod_le (order_dual.of_dual_le_of_dual.mp D0)
    (λ a b, order_dual.of_dual_le_of_dual.mp (Dm _ _)) s f

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
