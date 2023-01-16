/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.monoid_algebra.support

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

/-! ### Results about the `finset.sup` and `finset.inf` of `finsupp.support` -/

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
  rw [← list.prod_replicate, ←list.sum_replicate],
  refine (sup_support_list_prod_le degb0 degbm _).trans_eq _,
  rw list.map_replicate,
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

end add_monoid_algebra
