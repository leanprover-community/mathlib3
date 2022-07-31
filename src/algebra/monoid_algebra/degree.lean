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

/-! ### Results about the `finset.sup` and `finset.inf` of `finsupp.support` -/

section general_results_assuming_semilattice_sup
variables [semilattice_sup B] [order_bot B] [semilattice_inf T] [order_top T]

section semiring
variables [semiring R]

section explicit_Ds
variables (DB : A → B) (DT : A → T) (f g : add_monoid_algebra R A)

lemma sup_support_add_le : (f + g).support.sup DB ≤ (f.support.sup DB) ⊔ (g.support.sup DB) :=
(finset.sup_mono finsupp.support_add).trans_eq finset.sup_union

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
  refine (finset.sup_mono $ support_mul _ _).trans _,
  simp_rw [finset.sup_bUnion, finset.sup_singleton],
  refine (finset.sup_le $ λ fd fds, finset.sup_le $ λ gd gds, DBm.trans $ add_le_add _ _);
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

lemma le_inf_support_list_prod (DT0 : 0 ≤ DT 0) (DTm : ∀ a b, DT a + DT b ≤ DT (a + b))
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
  (m : multiset (add_monoid_algebra R A)) :
  (m.map (λ f : add_monoid_algebra R A, f.support.inf DT)).sum ≤ m.prod.support.inf DT :=
order_dual.of_dual_le_of_dual.mpr $
  sup_support_multiset_prod_le (order_dual.of_dual_le_of_dual.mp DT0)
    (λ a b, order_dual.of_dual_le_of_dual.mp (DTm _ _)) m

lemma sup_support_finset_prod_le
  (DB0 : DB 0 ≤ 0) (DBm : ∀ a b, DB (a + b) ≤ DB a + DB b)
  (s : finset ι) (f : ι → add_monoid_algebra R A):
  (∏ i in s, f i).support.sup DB ≤ ∑ i in s, (f i).support.sup DB :=
(sup_support_multiset_prod_le DB0 DBm _).trans_eq $ congr_arg _ $ multiset.map_map _ _ _

lemma le_inf_support_finset_prod
  (DT0 : 0 ≤ DT 0) (DTm : ∀ a b, DT a + DT b ≤ DT (a + b))
  (s : finset ι) (f : ι → add_monoid_algebra R A):
  ∑ i in s, (f i).support.inf DT ≤ (∏ i in s, f i).support.inf DT :=
order_dual.of_dual_le_of_dual.mpr $
  sup_support_finset_prod_le (order_dual.of_dual_le_of_dual.mp DT0)
    (λ a b, order_dual.of_dual_le_of_dual.mp (DTm _ _)) s f

end commutative_lemmas

end general_results_assuming_semilattice_sup

end add_monoid_algebra
