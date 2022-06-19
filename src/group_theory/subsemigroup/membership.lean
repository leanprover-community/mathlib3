import group_theory.subsemigroup.operations
import algebra.big_operators.basic

open_locale big_operators

variables {ι S M : Type*} [set_like S M]

lemma list.coe_foldl_mul [mul_one_class M] [mul_mem_class S M] {s : S} (a : s)
  (l : list s) :
  ↑(l.foldl (*) a) = (((a :: l).map coe).prod : M) :=
begin
  rw [list.map_cons, list.prod, list.foldl_cons, one_mul, list.foldl_map, ← list.foldl_hom l coe],
  exact λ _ _, rfl
end

lemma list_prod_mem_of_ne_nil [mul_one_class M] [mul_mem_class S M] {l : list M} {s : S}
  (hl : l ≠ []) (hs : ∀ x ∈ l, x ∈ s) : l.prod ∈ s :=
begin
  lift l to list s using hs,
  cases l with a l ihl, { exact (hl rfl).elim },
  rw [← list.coe_foldl_mul],
  exact (l.foldl (*) a).2
end

variables [comm_monoid M] [mul_mem_class S M] {s : S}

lemma multiset_prod_mem_of_ne_zero {m : multiset M} (hm : m ≠ 0) (hs : ∀ x ∈ m, x ∈ s) :
  m.prod ∈ s :=
begin
  induction m using quotient.induction_on,
  rw [multiset.quot_mk_to_coe, multiset.coe_prod],
  exact list_prod_mem_of_ne_nil (mt (multiset.coe_eq_zero _).2 hm) hs
end

lemma prod_mem_of_nonempty {I : finset ι} {f : ι → M} (hi : I.nonempty) (hs : ∀ i ∈ I, f i ∈ s) :
  (∏ i in I, f i) ∈ s :=
begin
  rcases I with ⟨m, hm⟩,
  rw [finset.nonempty_mk] at hi,
  exact multiset_prod_mem_of_ne_zero (mt multiset.map_eq_zero.1 hi)
    (multiset.forall_mem_map_iff.2 hs)
end

lemma fintype.prod_mem_of_nonempty [fintype ι] [nonempty ι] {f : ι → M} (hs : ∀ i, f i ∈ s) :
  (∏ i, f i) ∈ s :=
prod_mem_of_nonempty finset.univ_nonempty (λ i hi, hs i)
