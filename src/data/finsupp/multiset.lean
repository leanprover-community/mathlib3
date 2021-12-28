import data.finsupp.basic

/-! ### Declarations relating `finsupp` to `multiset` -/

open finset
open_locale big_operators classical
noncomputable theory

variables {α β γ ι M M' N P G H R S : Type*}

namespace finsupp

/-- Given `f : α →₀ ℕ`, `f.to_multiset` is the multiset with multiplicities given by the values of
`f` on the elements of `α`. We define this function as an `add_equiv`. -/
def to_multiset : (α →₀ ℕ) ≃+ multiset α :=
{ to_fun := λ f, f.sum (λa n, n • {a}),
  inv_fun := λ s, ⟨s.to_finset, λ a, s.count a, λ a, by simp⟩,
  left_inv := λ f, ext $ λ a, by
    { simp only [sum, multiset.count_sum', multiset.count_singleton, mul_boole, coe_mk,
        multiset.mem_to_finset, iff_self, not_not, mem_support_iff, ite_eq_left_iff, ne.def,
        multiset.count_eq_zero, multiset.count_nsmul, finset.sum_ite_eq, ite_not],
      exact eq.symm },
  right_inv := λ s, by simp only [sum, coe_mk, multiset.to_finset_sum_count_nsmul_eq],
  map_add' := λ f g, sum_add_index (λ a, zero_nsmul _) (λ a, add_nsmul _) }

lemma to_multiset_zero : (0 : α →₀ ℕ).to_multiset = 0 :=
rfl

lemma to_multiset_add (m n : α →₀ ℕ) :
  (m + n).to_multiset = m.to_multiset + n.to_multiset :=
to_multiset.map_add m n

lemma to_multiset_apply (f : α →₀ ℕ) : f.to_multiset = f.sum (λ a n, n • {a}) := rfl

@[simp]
lemma to_multiset_symm_apply [decidable_eq α] (s : multiset α) (x : α) :
  finsupp.to_multiset.symm s x = s.count x :=
by convert rfl

@[simp] lemma to_multiset_single (a : α) (n : ℕ) : to_multiset (single a n) = n • {a} :=
by rw [to_multiset_apply, sum_single_index]; apply zero_nsmul

lemma to_multiset_sum {ι : Type*} {f : ι → α →₀ ℕ} (s : finset ι) :
  finsupp.to_multiset (∑ i in s, f i) = ∑ i in s, finsupp.to_multiset (f i) :=
add_equiv.map_sum _ _ _

lemma to_multiset_sum_single {ι : Type*} (s : finset ι) (n : ℕ) :
  finsupp.to_multiset (∑ i in s, single i n) = n • s.val :=
by simp_rw [to_multiset_sum, finsupp.to_multiset_single, sum_nsmul, sum_multiset_singleton]

lemma card_to_multiset (f : α →₀ ℕ) : f.to_multiset.card = f.sum (λa, id) :=
by simp [to_multiset_apply, add_monoid_hom.map_finsupp_sum, function.id_def]

lemma to_multiset_map (f : α →₀ ℕ) (g : α → β) :
  f.to_multiset.map g = (f.map_domain g).to_multiset :=
begin
  refine f.induction _ _,
  { rw [to_multiset_zero, multiset.map_zero, map_domain_zero, to_multiset_zero] },
  { assume a n f _ _ ih,
    rw [to_multiset_add, multiset.map_add, ih, map_domain_add, map_domain_single,
        to_multiset_single, to_multiset_add, to_multiset_single,
        ← multiset.coe_map_add_monoid_hom, (multiset.map_add_monoid_hom g).map_nsmul],
    refl }
end

@[simp] lemma prod_to_multiset [comm_monoid M] (f : M →₀ ℕ) :
  f.to_multiset.prod = f.prod (λa n, a ^ n) :=
begin
  refine f.induction _ _,
  { rw [to_multiset_zero, multiset.prod_zero, finsupp.prod_zero_index] },
  { assume a n f _ _ ih,
    rw [to_multiset_add, multiset.prod_add, ih, to_multiset_single, finsupp.prod_add_index,
      finsupp.prod_single_index, multiset.prod_nsmul, multiset.prod_singleton],
    { exact pow_zero a },
    { exact pow_zero },
    { exact pow_add } }
end

@[simp] lemma to_finset_to_multiset [decidable_eq α] (f : α →₀ ℕ) :
  f.to_multiset.to_finset = f.support :=
begin
  refine f.induction _ _,
  { rw [to_multiset_zero, multiset.to_finset_zero, support_zero] },
  { assume a n f ha hn ih,
    rw [to_multiset_add, multiset.to_finset_add, ih, to_multiset_single, support_add_eq,
      support_single_ne_zero hn, multiset.to_finset_nsmul _ _ hn, multiset.to_finset_singleton],
    refine disjoint.mono_left support_single_subset _,
    rwa [finset.disjoint_singleton_left] }
end

@[simp] lemma count_to_multiset [decidable_eq α] (f : α →₀ ℕ) (a : α) :
  f.to_multiset.count a = f a :=
calc f.to_multiset.count a = f.sum (λx n, (n • {x} : multiset α).count a) :
  (multiset.count_add_monoid_hom a).map_sum _ f.support
  ... = f.sum (λx n, n * ({x} : multiset α).count a) : by simp only [multiset.count_nsmul]
  ... = f a * ({a} : multiset α).count a : sum_eq_single _
    (λ a' _ H, by simp only [multiset.count_singleton, if_false, H.symm, mul_zero])
    (λ H, by simp only [not_mem_support_iff.1 H, zero_mul])
  ... = f a : by rw [multiset.count_singleton_self, mul_one]

@[simp] lemma mem_to_multiset (f : α →₀ ℕ) (i : α) :
  i ∈ f.to_multiset ↔ i ∈ f.support :=
by rw [← multiset.count_ne_zero, finsupp.count_to_multiset, finsupp.mem_support_iff]

end finsupp

/-! ### Declarations relating `multiset` to `finsupp` -/

namespace multiset

/-- Given a multiset `s`, `s.to_finsupp` returns the finitely supported function on `ℕ` given by
the multiplicities of the elements of `s`. -/
def to_finsupp : multiset α ≃+ (α →₀ ℕ) := finsupp.to_multiset.symm

@[simp] lemma to_finsupp_support [D : decidable_eq α] (s : multiset α) :
  s.to_finsupp.support = s.to_finset :=
by rw subsingleton.elim D; refl

@[simp] lemma to_finsupp_apply [D : decidable_eq α] (s : multiset α) (a : α) :
  to_finsupp s a = s.count a :=
by rw subsingleton.elim D; refl

lemma to_finsupp_zero : to_finsupp (0 : multiset α) = 0 := add_equiv.map_zero _

lemma to_finsupp_add (s t : multiset α) :
  to_finsupp (s + t) = to_finsupp s + to_finsupp t :=
to_finsupp.map_add s t

@[simp] lemma to_finsupp_singleton (a : α) : to_finsupp ({a} : multiset α) = finsupp.single a 1 :=
finsupp.to_multiset.symm_apply_eq.2 $ by simp

@[simp] lemma to_finsupp_to_multiset (s : multiset α) :
  s.to_finsupp.to_multiset = s :=
finsupp.to_multiset.apply_symm_apply s

lemma to_finsupp_eq_iff {s : multiset α} {f : α →₀ ℕ} : s.to_finsupp = f ↔ s = f.to_multiset :=
finsupp.to_multiset.symm_apply_eq

end multiset

@[simp] lemma finsupp.to_multiset_to_finsupp (f : α →₀ ℕ) :
  f.to_multiset.to_finsupp = f :=
finsupp.to_multiset.symm_apply_apply f
