import ring_theory.polynomial.symmetric
import ring_theory.polynomial.homogeneous
import data.mv_polynomial.basic
import data.multiset.basic

noncomputable theory

open finset
open_locale classical big_operators

variables {α : Type*} {M : Type*} [decidable_eq α] [comm_semiring M] [nontrivial M]

namespace finset

def indicator (s : finset α) := s.piecewise (1 : α → M) (0 : α → M)

lemma mem_indicator (s : finset α) :
  ∀ (a : α), s.indicator a ≠ (0:M) → a ∈ s :=
begin
  intros a ha,
  simp only [indicator, piecewise, exists_prop, and_true, pi.zero_apply, pi.one_apply,
    ite_eq_right_iff, ne.def, not_false_iff, one_ne_zero, not_forall] at ha,
  exact ha,
end

end finset

namespace mv_polynomial
variables {σ : Type*} [fintype σ] {R : Type*} [comm_semiring R]

#reduce mv_polynomial σ R

--def esymm' (n : ℕ) [decidable_eq σ] : mv_polynomial σ R :=
--{ support := (powerset_len n univ).image (λ t, ∑ i in t, finsupp.single i 1),
--  to_fun := λ d, _,
--  mem_support_to_fun := _ }

@[simp] lemma finsupp.coe_sum
  {α : Type*} {ι : Type*} [decidable_eq ι] {M : Type*} [add_comm_monoid M]
  {f : ι → α →₀ M} (s : finset ι) : ⇑(∑ i in s, f i) = ∑ i in s, f i :=
begin
  let p := λ t : finset ι, ⇑∑ (i : ι) in t, f i = ∑ (i : ι) in t, (f i),
  have h : p = λ t : finset ι, ⇑∑ (i : ι) in t, f i = ∑ (i : ι) in t, (f i) := rfl,
  apply @finset.induction_on _ p _ s _ _,
  { rw h,
    clear h p,
    simp only [finsupp.coe_zero, sum_empty],
    ext,
    simp, },
  intros a s ha hp,
  rw h,
  rw h at hp,
  rw sum_insert ha,
  rw sum_insert ha,
  rw ← hp,
  exact finsupp.coe_add (f a) _,
end

lemma finsupp.sum_single {f : α → R}
  (s : finset α) (hf : ∀ a, f a ≠ 0 → a ∈ s) :
  ∑ i in s, finsupp.single i (f i) = finsupp.on_finset s f hf :=
begin
  ext,
  simp only [finsupp.on_finset_apply, finsupp.coe_sum, sum_apply],
  convert sum_apply a s (λ i, finsupp.single i (f i)),
  simp only [sum_apply],
  simp only [finsupp.single_apply, sum_ite_eq'],
  split_ifs, refl,
  have := mt (hf a) h,
  simp only [not_not] at this,
  assumption,
end

variables {f : α → M} {s : finset α}
variables (t : finset (σ →₀ M)) [decidable_eq M]

lemma finsupp.sum_single_one {f : α → M} (s : finset α) [nontrivial R] :
  ∑ i in s, finsupp.single (f i) (1:R) =
  (finsupp.on_finset (s.image f) (s.image f).indicator (s.image f).mem_indicator : M →₀ R) :=
begin
  sorry
end

lemma support_sum_eq {α : Type*} {ι : Type*} {M : Type*} [add_comm_monoid M]
  {g : ι → α →₀ M} (s : finset ι) (h : ∀ i₁ i₂, i₁ ≠ i₂ → disjoint (g i₁).support (g i₂).support) :
  (∑ i in s, g i).support = s.bUnion (λ i, (g i).support) :=
begin
  sorry
end

theorem finsupp.support_single {α : Type*} {M : Type*} [has_zero M] (a : α) (b : M) :
b ≠ 0 → (finsupp.single a b).support = {a} :=
begin
  intro hb,
  ext a',
  sorry
end

lemma support_esymm'' (n : ℕ) [decidable_eq σ] [nontrivial R] :
  (esymm σ R n).support = (powerset_len n (univ : finset σ)).bUnion (λ t, (finsupp.single (∑ (i : σ) in t, finsupp.single i 1) (1:R)).support) :=
begin
  rw esymm_eq_sum_monomial,
  simp only [monomial],
  convert support_sum_eq (powerset_len n (univ : finset σ)) _,
  intros i j hij d,
  simp only [finsupp.support_single _ (1:R) one_ne_zero],
  simp only [and_imp, inf_eq_inter, mem_inter, mem_singleton],
  have : 1 ≠ 0, { simp only [ne.def, not_false_iff, one_ne_zero] },
  intros h1 h2,
  have hi : (∑ (i : σ) in i, finsupp.single i 1).support = i,
  { rw support_sum_eq i _,
    simp [finsupp.support_single _ 1 this],
    intros i j hij,
    simp [finsupp.support_single _ 1 this],
    rw ← ne.def,
    exact hij.symm, },
  have hj : (∑ (i : σ) in j, finsupp.single i 1).support = j,
  { rw support_sum_eq j _,
    simp [finsupp.support_single _ 1 this],
    intros i j hij,
    simp [finsupp.support_single _ 1 this],
    rw ← ne.def,
    exact hij.symm},
  apply_fun finsupp.support at h1,
  apply_fun finsupp.support at h2,
  rw hi at h1,
  rw hj at h2,
  rw h1 at h2,
  contradiction,
end

lemma support_esymm' (n : ℕ) [decidable_eq σ] [nontrivial R] :
  (esymm σ R n).support = (powerset_len n (univ : finset σ)).bUnion (λ t, {∑ (i : σ) in t, finsupp.single i 1}) :=
begin
  rw support_esymm'',
  congr,
  funext,
  exact finsupp.support_single _ 1 one_ne_zero,
end

lemma support_esymm [decidable_eq σ] [nontrivial R] (n : ℕ) :
  (esymm σ R n).support =
  (powerset_len n (univ : finset σ)).image (λ t, ∑ (i : σ) in t, finsupp.single i 1) :=
begin
  rw support_esymm',
  exact bUnion_singleton,
end


lemma sup_finset_image' {α : Type*} {β : Type*} {γ : Type*}
  [decidable_eq α] [semilattice_sup_bot β] {f : γ → α} {g : α → β} (s : finset γ) :
  s.sup (g ∘ f) = (s.image f).sup g :=
begin
  apply finset.induction_on s,
  { simp },
  intros a s' ha ih,
  rw sup_insert,
  rw image_insert,
  rw sup_insert,
  rw ih,
end

#check finsupp.to_multiset ∘ λ (t : finset σ), ∑ (i : σ) in t, finsupp.single i 1

lemma to_multiset_sum {ι : Type*} {f : ι → σ →₀ ℕ} (s : finset ι) :
finsupp.to_multiset (∑ i in s, f i) = ∑ i in s, finsupp.to_multiset (f i) :=
by sorry

lemma single_to_multiset :
  (finsupp.to_multiset ∘ λ (t : finset σ), ∑ (i : σ) in t, finsupp.single i 1) = λ t, t.val :=
begin
  funext,
  simp only [function.comp_app],
  rw to_multiset_sum,
  simp only [finsupp.to_multiset_single, one_nsmul], sorry
end

lemma degrees_esymm (n : ℕ) [decidable_eq σ] [nontrivial R] :
  (esymm σ R n).degrees = (univ : finset σ).val :=
begin
  rw degrees,
  rw support_esymm,
  rw (sup_finset_image' (powerset_len n univ)).symm,
  simp [single_to_multiset],
  sorry
end

instance [nontrivial R] : nontrivial (mv_polynomial σ R) := add_monoid_algebra.nontrivial

lemma support_zero : (0 : mv_polynomial σ R).support = ∅ := rfl

lemma powerset_len_empty_iff {α : Type*} {s : finset α} (n : ℕ) :
  powerset_len n s = ∅ ↔ s.card < n :=
begin
  refine ⟨_, powerset_len_empty n⟩,
  contrapose!,
  intro h,
  apply nonempty.ne_empty,
  rw ← card_pos,
  rw card_powerset_len,
  exact nat.choose_pos h,
end

lemma esymm_ne_zero (k : ℕ) (h : k ≤ fintype.card σ) [nontrivial R] : esymm σ R k ≠ 0 :=
begin
  by_cases h : (nonempty σ),
  { have a := classical.choice h,
    have hmem := @mem_degrees R σ _ (esymm σ R k) a,
    rw degrees_esymm at hmem,
    rcases hmem.mp (mem_univ a) with ⟨d, hd, ha⟩,
    clear hmem,
    rw ne_zero_iff,
    exact ⟨d, hd⟩ },
  revert h,
  contrapose!,
  intro he,
  apply_fun support at he,
  rw support_esymm k at he,
  { have h1 :
      image (λ (t : finset σ), ∑ (i : σ) in t, finsupp.single i 1) (powerset_len k univ) = ∅,
    rw he,
    rw support_zero,
    clear he,
    simp at h1,
    rw powerset_len_empty_iff at h1,
    rw fintype.card at h,
    exfalso,
    exact not_lt_of_le h h1 },
  apply_instance,
end

end mv_polynomial
