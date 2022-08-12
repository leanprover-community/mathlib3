/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.monoid_algebra.basic

/-!
# Lemmas about the `sup` and `inf` of the support of `add_monoid_algebra`

## TODO
The current plan is to state and prove lemmas about `finset.sup (finsupp.support f) D` with a
"generic" degree/weight function `D` from the grading Type `A` to a somewhat ordered Type `B`.

Next, the general lemmas get specialized for some yet-to-be-defined `degree`s.
-/

variables {R A T B ι : Type*}

namespace add_monoid_algebra
open_locale classical big_operators

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

section general_results_assuming_semilattice_sup
variables [semilattice_sup B] [order_bot B] [semilattice_inf T] [order_top T]

section semiring
variables [semiring R]

section explicit_degrees
/-!

In this section, we use `degb` and `degt` to denote "degree functions" on `A` with values in
a type with *b*ot or *t*op respectively.
-/
variables (degb : A → B) (degt : A → T) (f g : add_monoid_algebra R A)

lemma sup_support_add_le : (f + g).support.sup degb ≤ (f.support.sup degb) ⊔ (g.support.sup degb) :=
(finset.sup_mono finsupp.support_add).trans_eq finset.sup_union

lemma le_inf_support_add : f.support.inf degt ⊓ g.support.inf degt ≤ (f + g).support.inf degt :=
sup_support_add_le (λ a : A, order_dual.to_dual (degt a)) f g

end explicit_degrees

section add_only
variables [has_add A] [has_add B] [has_add T]
  [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  [covariant_class T T (+) (≤)] [covariant_class T T (function.swap (+)) (≤)]

lemma sup_support_mul_le {degb : A → B} (degbm : ∀ {a b}, degb (a + b) ≤ degb a + degb b)
  (f g : add_monoid_algebra R A) :
  (f * g).support.sup degb ≤ f.support.sup degb + g.support.sup degb :=
begin
  refine (finset.sup_mono $ support_mul _ _).trans _,
  simp_rw [finset.sup_bUnion, finset.sup_singleton],
  refine (finset.sup_le $ λ fd fds, finset.sup_le $ λ gd gds, degbm.trans $ add_le_add _ _);
  exact finset.le_sup ‹_›,
end

lemma le_inf_support_mul {degt : A → T} (degtm : ∀ {a b}, degt a + degt b ≤ degt (a + b))
  (f g : add_monoid_algebra R A) :
  f.support.inf degt + g.support.inf degt ≤ (f * g).support.inf degt :=
order_dual.of_dual_le_of_dual.mpr $
  sup_support_mul_le (λ a b, order_dual.of_dual_le_of_dual.mp degtm) f g

end add_only

section add_monoids
variables [add_monoid A]
  [add_monoid B] [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  [add_monoid T] [covariant_class T T (+) (≤)] [covariant_class T T (function.swap (+)) (≤)]
  {degb : A → B} {degt : A → T}

lemma sup_support_list_prod_le (degb0 : degb 0 ≤ 0)
  (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) :
  ∀ l : list (add_monoid_algebra R A),
    l.prod.support.sup degb ≤ (l.map (λ f : add_monoid_algebra R A, f.support.sup degb)).sum
| [] := begin
    rw [list.map_nil, finset.sup_le_iff, list.prod_nil, list.sum_nil],
    exact λ a ha, by rwa [finset.mem_singleton.mp (finsupp.support_single_subset ha)]
  end
| (f::fs) := begin
    rw [list.prod_cons, list.map_cons, list.sum_cons],
    exact (sup_support_mul_le degbm _ _).trans (add_le_add_left (sup_support_list_prod_le _) _)
  end

lemma le_inf_support_list_prod (degt0 : 0 ≤ degt 0) (degtm : ∀ a b, degt a + degt b ≤ degt (a + b))
  (l : list (add_monoid_algebra R A)) :
  (l.map (λ f : add_monoid_algebra R A, f.support.inf degt)).sum ≤ l.prod.support.inf degt :=
order_dual.of_dual_le_of_dual.mpr $ sup_support_list_prod_le
  (order_dual.of_dual_le_of_dual.mp degt0) (λ a b, order_dual.of_dual_le_of_dual.mp (degtm _ _)) l

lemma sup_support_pow_le (degb0 : degb 0 ≤ 0) (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b)
  (n : ℕ) (f : add_monoid_algebra R A) :
  (f ^ n).support.sup degb ≤ n • (f.support.sup degb) :=
begin
  rw [← list.prod_repeat, ←list.sum_repeat],
  refine (sup_support_list_prod_le degb0 degbm _).trans_eq _,
  rw list.map_repeat,
end

lemma le_inf_support_pow (degt0 : 0 ≤ degt 0) (degtm : ∀ a b, degt a + degt b ≤ degt (a + b))
  (n : ℕ) (f : add_monoid_algebra R A) :
  n • (f.support.inf degt) ≤ (f ^ n).support.inf degt :=
order_dual.of_dual_le_of_dual.mpr $ sup_support_pow_le (order_dual.of_dual_le_of_dual.mp degt0)
  (λ a b, order_dual.of_dual_le_of_dual.mp (degtm _ _)) n f

end add_monoids

end semiring

section commutative_lemmas
variables [comm_semiring R] [add_comm_monoid A]
  [add_comm_monoid B] [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]
  [add_comm_monoid T] [covariant_class T T (+) (≤)] [covariant_class T T (function.swap (+)) (≤)]
  {degb : A → B} {degt : A → T}

lemma sup_support_multiset_prod_le
  (degb0 : degb 0 ≤ 0) (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b)
  (m : multiset (add_monoid_algebra R A)) :
  m.prod.support.sup degb ≤ (m.map (λ f : add_monoid_algebra R A, f.support.sup degb)).sum :=
begin
  induction m using quot.induction_on,
  rw [multiset.quot_mk_to_coe'', multiset.coe_map, multiset.coe_sum, multiset.coe_prod],
  exact sup_support_list_prod_le degb0 degbm m,
end

lemma le_inf_support_multiset_prod
  (degt0 : 0 ≤ degt 0) (degtm : ∀ a b, degt a + degt b ≤ degt (a + b))
  (m : multiset (add_monoid_algebra R A)) :
  (m.map (λ f : add_monoid_algebra R A, f.support.inf degt)).sum ≤ m.prod.support.inf degt :=
order_dual.of_dual_le_of_dual.mpr $
  sup_support_multiset_prod_le (order_dual.of_dual_le_of_dual.mp degt0)
    (λ a b, order_dual.of_dual_le_of_dual.mp (degtm _ _)) m

lemma sup_support_finset_prod_le
  (degb0 : degb 0 ≤ 0) (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b)
  (s : finset ι) (f : ι → add_monoid_algebra R A) :
  (∏ i in s, f i).support.sup degb ≤ ∑ i in s, (f i).support.sup degb :=
(sup_support_multiset_prod_le degb0 degbm _).trans_eq $ congr_arg _ $ multiset.map_map _ _ _

lemma le_inf_support_finset_prod
  (degt0 : 0 ≤ degt 0) (degtm : ∀ a b, degt a + degt b ≤ degt (a + b))
  (s : finset ι) (f : ι → add_monoid_algebra R A) :
  ∑ i in s, (f i).support.inf degt ≤ (∏ i in s, f i).support.inf degt :=
le_of_eq_of_le (by rw [multiset.map_map]; refl) (le_inf_support_multiset_prod degt0 degtm _)

end commutative_lemmas

end general_results_assuming_semilattice_sup

/-! ### Shorthands for special cases
Note that these definitions are reducible, in order to make it easier to apply the more generic
lemmas above. -/

section degrees

variables [semiring R]

section sup_degree

variables [semilattice_sup A]

/--  Let `R` be a semiring, let `A` be a `semilattice_sup`, and let `f : R[A]` be an
an element of `add_monoid_algebra R A`.  The sup-degree of `f` takes values in `with_bot A`
and it is the supremum of the support of `f` or `⊥`, depending on whether `f` is non-zero or not.
If `A` has a linear order, then this notion coincides with the usual one, using the maximum of
the exponents. -/
@[reducible] def sup_degree (f : add_monoid_algebra R A) : with_bot A :=
f.support.sup coe

lemma sup_degree_add_le (f g : add_monoid_algebra R A) :
  (f + g).sup_degree ≤ f.sup_degree ⊔ g.sup_degree :=
sup_support_add_le coe f g

variables [add_monoid A] [covariant_class A A (+) (≤)] [covariant_class A A (function.swap (+)) (≤)]
variables (f g : add_monoid_algebra R A)

lemma sup_degree_mul_le : (f * g).sup_degree ≤ f.sup_degree + g.sup_degree :=
sup_support_mul_le (λ a b, (with_bot.coe_add _ _).le) f g

end sup_degree

section inf_degree

variables [semilattice_inf A]

/--  Let `R` be a semiring, let `A` be a `semilattice_inf`, and let `f : R[A]` be an
an element of `add_monoid_algebra R A`.  The inf-degree of `f` takes values in `with_top A`
and it is the infimum of the support of `f` or `⊤`, depending on whether `f` is non-zero or not.
If `A` has a linear order, then this notion coincides with the usual one, using the minimum of
the exponents. -/
@[reducible] def inf_degree (f : add_monoid_algebra R A) : with_top A :=
f.support.inf coe

lemma le_inf_degree_add (f g : add_monoid_algebra R A) :
  f.inf_degree ⊓ g.inf_degree ≤ (f + g).inf_degree :=
sup_support_add_le (coe : Aᵒᵈ → with_bot Aᵒᵈ) f g

variables [add_monoid A] [covariant_class A A (+) (≤)] [covariant_class A A (function.swap (+)) (≤)]
  (f g : add_monoid_algebra R A)

lemma le_inf_degree_mul : f.inf_degree + g.inf_degree ≤ (f * g).inf_degree :=
sup_support_mul_le (λ a b : Aᵒᵈ, (with_bot.coe_add _ _).le) _ _

end inf_degree

section max_degree

variables [add_zero_class A] [linear_ordered_add_comm_monoid B] [order_bot B] (D : A →+ B)

/--  Let `R` be a semiring, let `A` be a `semilattice_sup`, and let `f : R[A]` be an
an element of `add_monoid_algebra R A`.  The max-degree of `f` takes values in `with_bot A`
and it is the supremum of the support of `f` or `⊥`, depending on whether `f` is non-zero or not.
If `A` has a linear order, then this notion coincides with the usual one, using the maximum of
the exponents. -/
@[reducible] def max_degree (f : add_monoid_algebra R A) : B :=
f.support.sup D

lemma max_degree_add_le (f g : add_monoid_algebra R A) :
  (f + g).max_degree D ≤ max (f.max_degree D) (g.max_degree D) :=
sup_support_add_le D f g

lemma max_degree_mul_le (f g : add_monoid_algebra R A) :
  (f * g).max_degree D ≤ f.max_degree D + g.max_degree D :=
sup_support_mul_le (λ a b, (add_monoid_hom.map_add D _ _).le) f g

end max_degree

section min_degree

variables [add_zero_class A] [linear_ordered_add_comm_monoid T] [order_top T] (D : A →+ T)

/--  Let `R` be a semiring, let `A` be a `semilattice_inf`, and let `f : R[A]` be an
an element of `add_monoid_algebra R A`.  The min-degree of `f` takes values in `with_top A`
and it is the infimum of the support of `f` or `⊤`, depending on whether `f` is non-zero or not.
If `A` has a linear order, then this notion coincides with the usual one, using the minimum of
the exponents. -/
@[reducible] def min_degree (f : add_monoid_algebra R A) : T :=
f.support.inf D

lemma le_min_degree_add (f g : add_monoid_algebra R A) :
  min (f.min_degree D) (g.min_degree D) ≤ (f + g).min_degree D :=
le_inf_support_add D f g

lemma le_min_degree_mul (f g : add_monoid_algebra R A) :
  f.min_degree D + g.min_degree D ≤ (f * g).min_degree D :=
le_inf_support_mul (λ a b : A, (add_monoid_hom.map_add D _ _).ge) _ _

end min_degree

end degrees

end add_monoid_algebra
