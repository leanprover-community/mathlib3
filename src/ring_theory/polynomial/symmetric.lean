/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import data.fintype.card
import ring_theory.polynomial.homogeneous

open equiv (perm)
open_locale big_operators

-- move this
def equiv.finset {α : Type*} {β : Type*} (e : α ≃ β) :
  finset α ≃ finset β :=
{ to_fun := finset.map e.to_embedding,
  inv_fun := finset.map e.symm.to_embedding,
  left_inv := λ s, by simp [finset.map_map, finset.map_refl],
  right_inv := λ s, by simp [finset.map_map, finset.map_refl] }

-- move this
noncomputable def equiv.finsupp {α : Type*} {β : Type*} {A : Type*} [add_comm_monoid A] (e : α ≃ β) :
  (α →₀ A) ≃ (β →₀ A) :=
{ to_fun := finsupp.emb_domain e.to_embedding,
  inv_fun := finsupp.emb_domain e.symm.to_embedding,
  left_inv := λ f, by { ext a,
    erw [← e.symm_apply_apply a, finsupp.emb_domain_apply,
        finsupp.emb_domain_apply, e.symm_apply_apply], },
  right_inv := λ f, by { ext b,
    erw [← e.apply_symm_apply b, finsupp.emb_domain_apply,
        finsupp.emb_domain_apply, e.apply_symm_apply] } }

-- move this
lemma list.sorted_repeat {α : Type*} (r : α → α → Prop) [is_refl _ r] (a : α) :
  ∀ k, list.sorted r (list.repeat a k)
| 0     := list.sorted_nil
| (k+1) :=
begin
  rw [list.repeat_succ, list.sorted_cons],
  split,
  { intros b hb, rw list.eq_of_mem_repeat hb, exact is_refl.refl a },
  { apply list.sorted_repeat }
end

namespace finsupp
noncomputable theory
open_locale classical
variables {α : Type*} {β : Type*} [has_zero β]

def indicator (s : finset α) (f : α → β) :
  α →₀ β :=
{ support := s.filter (λ a, f a ≠ 0),
  to_fun  := λ a, if a ∈ s then f a else 0,
  mem_support_to_fun :=
  begin
    intros i, rw [finset.mem_filter],
    split_ifs; simp only [h, true_and, eq_self_iff_true, not_true, ne.def, false_and]
  end }

lemma indicator_support (s : finset α) (f : α → β) :
  (indicator s f).support = s.filter (λ a, f a ≠ 0) := rfl

@[simp] lemma indicator_apply_of_mem (s : finset α) (f : α → β) (a : α) (ha : a ∈ s) :
  indicator s f a = f a := if_pos ha

@[simp] lemma indicator_apply_of_not_mem (s : finset α) (f : α → β) (a : α) (ha : a ∉ s) :
  indicator s f a = 0 := if_neg ha

lemma sum_eq_sum_univ {A : Type*} {B : Type*} [fintype α] [has_zero A] [add_comm_monoid B]
  (f : α →₀ A) (g : α → A → B) (h : ∀ a, g a 0 = 0) :
  f.sum g = ∑ i, g i (f i) :=
begin
  rw [finsupp.sum, ← fintype.sum_extend_by_zero, fintype.sum_congr],
  intro a,
  split_ifs with H,
  { refl },
  { rw not_mem_support_iff at H, rw [H, h] }
end

end finsupp

namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {R : Type*} {S : Type*}

/-- A symmetric polynomial is a polynomial that is invariant under
arbitrary permutations of the polynomial variables. -/
def is_symmetric [comm_semiring R] (φ : mv_polynomial σ R) : Prop :=
∀ ⦃e : perm σ⦄, φ.rename e = φ

namespace is_symmetric
variables [comm_semiring R] [comm_semiring S] {φ ψ : mv_polynomial σ R}

@[simp]
lemma C (r : R) : is_symmetric (C r : mv_polynomial σ R) :=
λ e, rename_C e r

@[simp]
lemma zero : is_symmetric (0 : mv_polynomial σ R) :=
by { rw [← C_0], exact is_symmetric.C 0 }

@[simp]
lemma one : is_symmetric (1 : mv_polynomial σ R) :=
by { rw [← C_1], exact is_symmetric.C 1 }

@[simp]
lemma add (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ + ψ) :=
λ e, by rw [rename_add, hφ, hψ]

@[simp]
lemma mul (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ * ψ) :=
λ e, by rw [rename_mul, hφ, hψ]

@[simp]
lemma map (hφ : is_symmetric φ) (f : R →+* S) : is_symmetric (map f φ) :=
λ e, by rw [← map_rename, hφ]

end is_symmetric

namespace is_symmetric
variables [comm_ring R] (φ ψ : mv_polynomial σ R)

@[simp]
lemma neg (hφ : is_symmetric φ) : is_symmetric (-φ) :=
λ e, by rw [rename_neg, hφ]

@[simp]
lemma sub (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ - ψ) :=
λ e, by rw [rename_sub, hφ, hψ]

end is_symmetric

section
/-!
## Elementary symmetric polynomials
-/
variables (σ R) [fintype σ] [fintype τ] [comm_semiring R] [comm_semiring S]

/-- `elementary_symmetric σ R n` is the `n`th elementary symmetric polynomial
with variables indexed by `σ` and coefficients in `R`.
It is defined as the sum of all products of `n` distinct variables. -/
noncomputable def elementary_symmetric (n : ℕ) : mv_polynomial σ R :=
∑ t : {s : finset σ // s.card = n},
  ∏ i in (t : finset σ), X i

@[simp] lemma elementary_symmetric_zero :
  elementary_symmetric σ R 0 = 1 :=
begin
  letI : unique ({s : finset σ // s.card = 0}) :=
  { default := ⟨∅, finset.card_empty⟩,
    uniq := by { rintro ⟨s, hs⟩, rw subtype.ext, rwa finset.card_eq_zero at hs, } },
  simp only [elementary_symmetric, univ_unique, finset.sum_singleton],
  exact finset.prod_empty,
end

lemma elementary_symmetric_eq_sum_monomial (n : ℕ) :
  elementary_symmetric σ R n =
  ∑ t : {s : finset σ // s.card = n}, monomial (finsupp.indicator ↑t (λ _, 1)) 1 :=
begin
  apply finset.sum_congr rfl,
  rintro ⟨s, hs⟩ hsu,
  simp only [monomial_eq, C_1, one_mul, finsupp.prod, finsupp.indicator_support, ne.def,
    finset.filter_true, not_false_iff, one_ne_zero, finset.filter_congr_decidable, subtype.coe_mk],
  apply finset.prod_congr rfl,
  intros i hi,
  rw [finsupp.indicator_apply_of_mem _ _ _ hi, pow_one]
end

variables {σ R}

lemma map_elementary_symmetric (n : ℕ) (f : R →+* S) :
  map f (elementary_symmetric σ R n) = elementary_symmetric σ S n :=
begin
  let F : mv_polynomial σ R →+* mv_polynomial σ S := ring_hom.of (map f),
  show F (elementary_symmetric σ R n) = elementary_symmetric σ S n,
  rw [elementary_symmetric, F.map_sum],
  apply fintype.sum_congr,
  intros t,
  calc _ = _ : F.map_prod _ _
     ... = _ : _,
  apply finset.prod_congr rfl,
  simp only [eq_self_iff_true, map_X, ring_hom.coe_of, forall_true_iff],
end

lemma rename_elementary_symmetric (n : ℕ) (e : σ ≃ τ) :
  rename e (elementary_symmetric σ R n) = elementary_symmetric τ R n :=
begin
  let F : mv_polynomial σ R →+* mv_polynomial τ R := ring_hom.of (rename e),
  show F (elementary_symmetric σ R n) = elementary_symmetric τ R n,
  rw [elementary_symmetric, F.map_sum],
  let e' : {s : finset σ // s.card = n} ≃ {s : finset τ // s.card = n} :=
    e.finset.subtype_congr
      (by { intro, simp only [equiv.finset, equiv.coe_fn_mk, finset.card_map] }),
  rw ← finset.sum_equiv e'.symm,
  apply fintype.sum_congr,
  intro s,
  show F (∏ i in (e'.symm s : finset σ), X i) = ∏ i in (s : finset τ), X i,
  calc _ = _ : F.map_prod _ _
     ... = _ : finset.prod_map (s : finset τ) _ _
     ... = _ : _,
  apply finset.prod_congr rfl,
  intros,
  simp only [rename_X, equiv.apply_symm_apply, ring_hom.coe_of, equiv.to_embedding_coe_fn],
end

lemma elementary_symmetric_is_symmetric (n : ℕ) :
  is_symmetric (elementary_symmetric σ R n) :=
rename_elementary_symmetric n

lemma elementary_symmetric_is_homogeneous (n : ℕ) :
  is_homogeneous (elementary_symmetric σ R n) n :=
begin
  apply is_homogeneous.sum,
  rintro ⟨s, hs⟩ h,
  have hn : n = ∑ i in s, 1, by rw [← hs, finset.card_eq_sum_ones],
  subst hn,
  apply is_homogeneous.prod,
  intros,
  exact is_homogeneous_X _ i
end

lemma coeff_elementary_symmetric (d : σ →₀ ℕ) (n : ℕ) :
  coeff d (elementary_symmetric σ R n) = if ∑ i, d i = n ∧ ∀ i, d i ≤ 1 then 1 else 0 :=
begin
  classical,
  simp only [elementary_symmetric_eq_sum_monomial, coeff_sum, coeff_monomial, finset.sum_boole],
  split_ifs with H,
  { cases H with H1 H2,
    have H3 : ∀ i ∈ d.support, d i = 1,
    { intros i hi,
      rw finsupp.mem_support_iff at hi,
      specialize H2 i, revert H2 hi, generalize : (d i) = k, clear_except, omega },
    have hd : d.support.card = n,
    { subst H1,
      have : ∑ i in d.support, d i = ∑ i, d i := d.sum_eq_sum_univ (λ _, id) (λ _, rfl),
      show d.support.card = ∑ i, d i,
      rw [finset.card_eq_sum_ones, ← this],
      apply finset.sum_congr rfl,
      intros i hi, rw H3 i hi },
    let t : {s : finset σ // s.card = n} := ⟨d.support, hd⟩,
    convert nat.cast_one, convert finset.card_singleton t,
    ext ⟨s, hs⟩,
    simp only [finset.mem_singleton, finset.mem_filter, true_and, finset.mem_univ,
      subtype.mk_eq_mk, subtype.coe_mk],
    split; rintro rfl,
    { simp only [finsupp.indicator_support, finset.filter_true, ne.def, not_false_iff, one_ne_zero] },
    { ext i,
      by_cases hi : i ∈ d.support,
      { rw [finsupp.indicator_apply_of_mem _ _ _ hi, H3 i hi] },
      { rw finsupp.indicator_apply_of_not_mem _ _ _ hi,
        rw finsupp.not_mem_support_iff at hi,
        exact hi.symm } } },
  { suffices : (λ (x : {s : finset σ // s.card = n}), finsupp.indicator ↑x (λ _, 1) = d) = λ _, false,
    { simp only [this, finset.card_empty, nat.cast_zero, finset.filter_false], },
    ext ⟨s, hs⟩,
    simp only [subtype.coe_mk, iff_false],
    contrapose! H,
    rw [← H, ← hs],
    split,
    { conv_rhs { rw [finset.card_eq_sum_ones, ← fintype.sum_extend_by_zero], },
      apply fintype.sum_congr,
      intro i, split_ifs; refl },
    { intro i,
      by_cases hi : i ∈ s,
      { rw finsupp.indicator_apply_of_mem _ _ _ hi },
      { rw finsupp.indicator_apply_of_not_mem _ _ _ hi,
        apply nat.zero_le _ } } }
end

end

section
variables [fintype σ] [comm_ring R]

lemma aeval_elementary_symmetric_is_symmetric (φ : mv_polynomial ℕ R) :
  is_symmetric (aeval _ _ (elementary_symmetric σ R) φ) :=
begin
  apply mv_polynomial.induction_on φ,
  { intro r, rw aeval_C, apply is_symmetric.C },
  { intros φ ψ h₁ h₂, rw alg_hom.map_add, exact h₁.add h₂ },
  { intros φ n h, rw [alg_hom.map_mul, aeval_X], exact h.mul (elementary_symmetric_is_symmetric n) }
end

end

namespace monomial_symmetric
/-!
## Monomial symmetric polynomials
-/
open fintype
variables {σ R} [fintype σ] [fintype τ] [comm_semiring R] [comm_semiring S]

/-- `signature n` is an auxilliary type
introduced for reasoning about monomials occuring in symmetric polynomials.
It registers the degree of such a monomial, after sorting the individual exponents.
Such `signature`s are sorted, first by sum (total degree) and then by lexicographic ordering. -/
structure signature (n : ℕ) :=
(coeffs : list ℕ)
(sorted : coeffs.sorted (≥))
(length : coeffs.length = n)

namespace signature
variables {n : ℕ}

@[ext]
lemma ext {l₁ l₂ : signature n} (h : l₁.coeffs ~ l₂.coeffs) : l₁ = l₂ :=
begin
  cases l₁ with l₁ s₁ n₁,
  cases l₂ with l₂ s₂ n₂,
  congr,
  apply list.eq_of_sorted_of_perm h s₁ s₂
end

lemma ext_iff {l₁ l₂ : signature n} : l₁ = l₂ ↔ l₁.coeffs ~ l₂.coeffs :=
⟨by { rintro rfl, refl }, ext⟩

instance (n : ℕ) : partial_order (signature n) :=
{ le := λ l₁ l₂, l₁.coeffs.sum < l₂.coeffs.sum ∨ (l₁.coeffs.sum = l₂.coeffs.sum ∧ l₁.coeffs ≤ l₂.coeffs),
  le_refl := by { intro l, right, split; refl },
  le_trans :=
  begin
    rintro l₁ l₂ l₃ (h₁₂|⟨h₁₂, h₁₂'⟩) (h₂₃|⟨h₂₃, h₂₃'⟩),
    { left, exact lt_trans h₁₂ h₂₃ },
    { left, rwa ← h₂₃ },
    { left, rwa h₁₂ },
    { right, exact ⟨h₂₃ ▸ h₁₂, le_trans h₁₂' h₂₃'⟩ }
  end,
  le_antisymm :=
  begin
    rintro l₁ l₂ (h₁₂|⟨h₁₂, h₁₂'⟩) (h₂₁|⟨h₂₁, h₂₁'⟩),
    { exfalso, exact lt_irrefl _ (lt_trans h₁₂ h₂₁) },
    { exfalso, rw h₂₁ at h₁₂, exact lt_irrefl _ h₁₂ },
    { exfalso, rw h₁₂ at h₂₁, exact lt_irrefl _ h₂₁ },
    { apply ext, rw le_antisymm h₁₂' h₂₁' }
  end }

instance (n : ℕ) : has_zero (signature n) :=
⟨{ coeffs := list.repeat 0 n, sorted := list.sorted_repeat _ _ _, length := list.length_repeat _ _ }⟩

@[simp] lemma coeffs_zero : (0 : signature n).coeffs = list.repeat 0 n := rfl

-- lemma zero_le (l : signature n) : 0 ≤ l :=
-- begin
--   by_cases H : (0 : signature n).coeffs.sum = l.coeffs.sum,
--   { right, refine ⟨H, _⟩, sorry },
--   { left, contrapose! H,
--     have aux : (0 : signature n).coeffs.sum = 0,
--     { show (list.repeat 0 n).sum = 0, rw [list.sum_repeat, nsmul_zero] },
--     rw aux at H ⊢, rw nat.le_zero_iff at H, exact H.symm }
-- end

def single : Π (n k : ℕ), signature n
| 0     _ := ⟨[], list.sorted_nil, rfl⟩
| (n+1) k :=
  { coeffs := (k :: list.repeat 0 n),
    sorted :=
    begin
      rw [list.sorted_cons],
      split,
      { intros i hi, rw list.eq_of_mem_repeat hi, exact nat.zero_le _ },
      { exact list.sorted_repeat _ _ _ }
    end,
    length := by rw [list.length_cons, list.length_repeat] }

@[simp] lemma single_zero_right : ∀ (n : ℕ), single n 0 = 0
| 0     := rfl
| (n+1) := rfl

@[simp] lemma sum_coeffs_single (n k : ℕ) (h : 0 < n) :
  (single n k).coeffs.sum = k :=
begin
  cases n,
  { exfalso, exact lt_irrefl 0 h },
  { show list.sum (k :: list.repeat 0 n) = k,
    rw [list.sum_cons, list.sum_repeat, nsmul_zero, add_zero] }
end

end signature

/-- The signature associated with `d : σ →₀ ℕ` is the sorted list of function values of `d`. -/
def to_signature (d : σ →₀ ℕ) : signature (card σ) :=
{ coeffs := multiset.sort (≥) (multiset.map d (elems σ).1),
  sorted := multiset.sort_sorted _ _,
  length := by { simp only [multiset.length_sort, multiset.card_map], refl } }

lemma coeffs_to_signature (d : σ →₀ ℕ) :
  (to_signature d).coeffs = multiset.sort (≥) (multiset.map d (elems σ).1) := rfl

@[simp] lemma sum_coeffs_to_signature (d : σ →₀ ℕ) :
  (to_signature d).coeffs.sum = ∑ i, d i :=
by { rw [coeffs_to_signature, ← multiset.coe_sum, multiset.sort_eq], refl }

@[simp] lemma to_signature_zero :
  to_signature (0 : σ →₀ ℕ) = 0 :=
begin
  ext,
  rw [coeffs_to_signature, ← multiset.coe_eq_coe, multiset.sort_eq, signature.coeffs_zero],
  apply multiset.eq_repeat.mpr,
  refine ⟨multiset.card_map _ _, _⟩,
  intros k hk,
  rw multiset.mem_map at hk,
  rcases hk with ⟨i, hi, rfl⟩,
  refl
end

lemma count_zero_coeffs_to_signature (d : σ →₀ ℕ) :
  multiset.count 0 (to_signature d).coeffs = fintype.card σ - d.support.card :=
begin
  apply finsupp.induction d,
  { simp only [to_signature_zero, finset.card_empty, nat.sub_zero, list.count_repeat,
     finsupp.support_zero, signature.coeffs_zero, multiset.coe_count] },
  { intros i k d hi hk IH, sorry }
end

lemma count_coeffs_to_signature_single (i : σ) (n k : ℕ) :
  multiset.count n (to_signature (finsupp.single i k)).coeffs =
  if k = 0 then
    if n = 0 then fintype.card σ else 0
  else
    if n = 0 then fintype.card σ - 1 else
      if n = k then 1 else 0 :=
begin
  classical,
  split_ifs with hk hn hn hnk,
  { subst hk, subst hn,
    rw [count_zero_coeffs_to_signature, finsupp.single_zero, finsupp.support_zero,
        finset.card_empty, nat.sub_zero] },
  { subst hk, rw [finsupp.single_zero, to_signature_zero],
    apply multiset.count_eq_zero_of_not_mem,
    contrapose! hn, exact multiset.eq_of_mem_repeat hn, },
  { subst hn,
    rw [count_zero_coeffs_to_signature, finsupp.support_single_ne_zero hk, finset.card_singleton] },
  { subst hnk,
    rw [coeffs_to_signature, multiset.sort_eq],
    rw [multiset.count, multiset.countp_eq_card_filter],
    rw [multiset.card_eq_one],
    use n,
   sorry },
  { apply multiset.count_eq_zero_of_not_mem,
    rw [coeffs_to_signature, multiset.sort_eq],
    contrapose! hn,
    obtain ⟨j, hj, rfl⟩ := multiset.mem_map.mp hn,
    rw finsupp.single_apply,
    split_ifs, swap, refl,
    subst h, exfalso, apply hnk, exact finsupp.single_eq_same, }
end

lemma count_coeffs_signature_single (n m k : ℕ) :
  multiset.count n ((signature.single m k).coeffs) =
  if m = 0 then 0 else
  if k = 0 then
    if n = 0 then m else 0
  else
    if n = 0 then m - 1 else
      if n = k then 1 else 0 :=
begin
  classical,
  split_ifs with hm hk hn hn hnk,
  { subst m, rw [multiset.count_eq_zero],
    simp only [signature.single, multiset.coe_nil_eq_zero, not_false_iff, multiset.not_mem_zero] },
  { subst hk, subst hn, rw [signature.single_zero_right], apply multiset.count_repeat },
  { subst hk, rw [signature.single_zero_right],
    apply multiset.count_eq_zero_of_not_mem,
    contrapose! hn, exact multiset.eq_of_mem_repeat hn },
  { subst hn,
    cases m, { rw [nat.zero_sub, multiset.count_eq_zero], apply multiset.not_mem_zero, },
    { simp only [nat.succ_sub_succ_eq_sub, nat.sub_zero, multiset.coe_count],
      erw [list.count_cons_of_ne, list.count_repeat], symmetry, exact hk, } },
  { subst hnk, cases m, { contradiction },
    simp only [signature.single, list.count_cons_self, multiset.coe_count],
    congr' 1,
    rw list.count_eq_zero_of_not_mem,
    contrapose! hn,
    exact list.eq_of_mem_repeat hn, },
  { rw [multiset.count_eq_zero],
    cases m,
    { simp only [signature.single, multiset.coe_nil_eq_zero, not_false_iff, multiset.not_mem_zero] },
    simp only [signature.single, list.mem_cons_iff, multiset.mem_coe],
    push_neg,
    refine ⟨hnk, _⟩,
    contrapose! hn,
    exact list.eq_of_mem_repeat hn }
end

@[simp] lemma to_signature_single (i : σ) (k : ℕ) :
  to_signature (finsupp.single i k) = signature.single _ k :=
begin
  have : ¬ card σ = 0,
  { apply nat.pos_iff_ne_zero.mp,
    exact card_pos_iff.mpr ⟨i⟩, },
  ext1, rw [← multiset.coe_eq_coe, multiset.ext],
  intro n,
  rw [count_coeffs_to_signature_single, count_coeffs_signature_single, if_neg this],
end

end monomial_symmetric

section
open fintype monomial_symmetric
variables (σ R) [fintype σ] [fintype τ] [comm_semiring R] [comm_semiring S]

noncomputable def monomial_symmetric.support_fintype (l : signature (card σ)) :
  fintype {d // to_signature d = l} :=
set.finite.fintype $
begin
  let f : σ →₀ ℕ := finsupp.equiv_fun_on_fintype.symm (λ _, l.coeffs.sum),
  apply set.finite_subset (finsupp.finite_le_nat f),
  intros d hd i,
  change to_signature d = l at hd,
  show d i ≤ l.coeffs.sum,
  rw [← hd, sum_coeffs_to_signature],
  exact finset.single_le_sum (λ _ _, nat.zero_le _) (finset.mem_univ _),
end

local attribute [instance] monomial_symmetric.support_fintype

/-- `monomial_symmetric σ R (l : signature (card σ))` is the symmetric polynomial
with variables indexed by `σ` and coefficients in `R`
whose monomials have signature `l`.
For example, if `l = [2,2,1]`, then `monomial _ ℤ l` is
`(X^2 * Y^2 * Z) + (X^2 * Y * Z^2) + (X * Y^2 * Z^2)`. -/
noncomputable def monomial_symmetric (l : signature (card σ)) : mv_polynomial σ R :=
∑ d : {d // to_signature d = l}, monomial d 1

end

section
/-!
## Complete homogeneous symmetric polynomials
-/
variables (σ R) [fintype σ] [fintype τ] [comm_semiring R] [comm_semiring S]

noncomputable def complete_homogeneous.support_fintype (n : ℕ) :
  fintype {d : σ →₀ ℕ // ∑ i, d i = n} :=
set.finite.fintype $
begin
  let f : σ →₀ ℕ := finsupp.equiv_fun_on_fintype.symm (λ _, n),
  apply set.finite_subset (finsupp.finite_le_nat f),
  intros d hd i,
  calc d i ≤ ∑ i, d i : finset.single_le_sum (λ _ _, nat.zero_le _) (finset.mem_univ _)
       ... = n        : hd
       ... = f i      : rfl
end

local attribute [instance] complete_homogeneous.support_fintype

/-- `complete_homogeneous σ R n` is the `n`th complete homogeneous symmetric polynomial
with variables indexed by `σ` and coefficients in `R`.
It is defined as the sum of all monomials of degree `n`. -/
noncomputable def complete_homogeneous (n : ℕ) : mv_polynomial σ R :=
∑ d : {d : σ →₀ ℕ // ∑ i, d i = n}, monomial d 1

@[simp] lemma complete_homogeneous_zero :
  complete_homogeneous σ R 0 = 1 :=
begin
  letI : unique {d : σ →₀ ℕ // ∑ i, d i = 0} :=
  { default := ⟨0, by simp only [finsupp.zero_apply, finset.sum_const_zero]⟩,
    uniq := by { rintro ⟨d, hd⟩, rw subtype.ext, ext i,
                 rw [finset.sum_eq_zero_iff] at hd,
                 exact hd _ (finset.mem_univ _) } },
  simp only [complete_homogeneous, univ_unique, finset.sum_singleton],
  refl
end

lemma complete_homogeneous_is_homogeneous (n : ℕ) :
  (complete_homogeneous σ R n).is_homogeneous n :=
begin
  apply is_homogeneous.sum,
  rintro ⟨i, hi⟩ H,
  apply is_homogeneous_monomial,
  convert hi using 1,
  exact i.sum_eq_sum_univ (λ _, id) (λ _, rfl),
end

variables {σ R}

lemma coeff_complete_homogeneous (n : ℕ) (d : σ →₀ ℕ) :
  coeff d (complete_homogeneous σ R n) = if ∑ i, d i = n then 1 else 0 :=
begin
  classical,
  split_ifs with h,
  { let t : {d : σ →₀ ℕ // ∑ i, d i = n} := ⟨d, h⟩,
    simp only [complete_homogeneous, coeff_sum, coeff_monomial],
    rw [finset.sum_eq_single t],
    { simp only [if_true, eq_self_iff_true, subtype.coe_mk] },
    { intros t' ht' H, apply if_neg, rwa [ne.def, subtype.ext] at H, },
  { intro H, exfalso, exact H (finset.mem_univ _) } },
  { apply (complete_homogeneous_is_homogeneous σ R n).coeff_eq_zero,
    contrapose! h,
    simpa only [finsupp.sum, h, id.def] using (d.sum_eq_sum_univ (λ _, id) (λ _, rfl)).symm, }
end

lemma map_complete_homogeneous (n : ℕ) (f : R →+* S) :
  map f (complete_homogeneous σ R n) = complete_homogeneous σ S n :=
begin
  let F : mv_polynomial σ R →+* mv_polynomial σ S := ring_hom.of (map f),
  show F (complete_homogeneous σ R n) = complete_homogeneous σ S n,
  rw [complete_homogeneous, F.map_sum],
  apply fintype.sum_congr,
  intro,
  rw [ring_hom.coe_of, map_monomial, f.map_one],
end

lemma rename_complete_homogeneous (n : ℕ) (e : σ ≃ τ) :
  rename e (complete_homogeneous σ R n) = complete_homogeneous τ R n :=
begin
  let F : mv_polynomial σ R →+* mv_polynomial τ R := ring_hom.of (rename e),
  show F (complete_homogeneous σ R n) = complete_homogeneous τ R n,
  rw [complete_homogeneous, F.map_sum],
  let e' : {d : σ →₀ ℕ // ∑ i, d i = n} ≃ {d : τ →₀ ℕ // ∑ i, d i = n} :=
    e.finsupp.subtype_congr
      (by { intro d,
            rw ← finset.sum_equiv e,
            show (∑ i, d i = n) ↔ (∑ i, (d.emb_domain e.to_embedding) (e.to_embedding i)) = n,
            simp only [finsupp.emb_domain_apply], }),
  rw ← finset.sum_equiv e'.symm,
  apply fintype.sum_congr,
  intro d,
  show F (monomial (e'.symm d) 1) = monomial d 1,
  rw [ring_hom.coe_of, rename_monomial],
  congr,
  ext i,
  simp only [finsupp.map_domain, finsupp.sum_apply, finsupp.single_apply],
  rw [finsupp.sum, finset.sum_eq_single (e.symm i)],
  { simpa only [e', equiv.finsupp, equiv.subtype_congr, if_true, equiv.coe_fn_symm_mk,
      eq_self_iff_true, equiv.apply_symm_apply, subtype.coe_mk]
      using finsupp.emb_domain_apply e.symm.to_embedding _ _ },
  { rintro j h hj, rw if_neg, rintro rfl, simpa using hj },
  { simp only [finsupp.not_mem_support_iff, imp_self, if_true,
      eq_self_iff_true, equiv.apply_symm_apply], }
end

lemma complete_homogeneous_is_symmetric (n : ℕ) :
  is_symmetric (complete_homogeneous σ R n) :=
rename_complete_homogeneous n

end

section
variables (σ R) [fintype σ] [comm_ring R]

lemma alternating_sum_elementary_symmetric_mul_complete_homogeneous (n : ℕ) :
  ∑ ij in (finset.nat.antidiagonal n),
    C (-1)^ij.1 * elementary_symmetric σ R ij.1 * complete_homogeneous σ R ij.2 = 0 :=
begin
  rw mv_polynomial.ext_iff,
  intro d,
  rw [coeff_sum, coeff_zero],
  conv_lhs { apply_congr, skip, rw [mul_assoc, ← C_pow, coeff_C_mul, coeff_mul, finset.mul_sum] },
  rw finset.sum_comm,
  let L := d.antidiagonal.support.filter (λ p : (σ →₀ ℕ) × (σ →₀ ℕ), p.1.sum (λ _, id) % 2 = 0),
  let R := d.antidiagonal.support.filter (λ p : (σ →₀ ℕ) × (σ →₀ ℕ), p.1.sum (λ _, id) % 2 = 1),
  classical,
  have hLR : d.antidiagonal.support = L ∪ R,
  { ext p,
    simp only [finsupp.mem_antidiagonal_support, finset.mem_union, finset.mem_filter],
    have := nat.mod_two_eq_zero_or_one (p.1.sum (λ _, id)),
    rw classical.or_iff_not_imp_left at this,
    tauto },
  have LR_disjoint : disjoint L R,
  { rw finset.disjoint_filter, intros p hp h0, rw h0, exact zero_ne_one },
  rw [hLR, finset.sum_union LR_disjoint],
end

end

end mv_polynomial

#lint




#exit

section
/-!
## Power-sum symmetric polynomials
-/
variables (σ R) [fintype σ] [fintype τ] [comm_semiring R] [comm_semiring S]

/-- `powersum_symmetric σ R n` is the `n`th power-sum symmetric polynomial
with variables indexed by `σ` and coefficients in `R`.
It is defined as the sum of all `n`th powers of all variables. -/
noncomputable def powersum_symmetric (n : ℕ) : mv_polynomial σ R :=
∑ i : σ, (X i)^n

variables {σ R}

lemma map_powersum_symmetric (n : ℕ) (f : R →+* S) :
  map f (powersum_symmetric σ R n) = powersum_symmetric σ S n :=
begin
  let F : mv_polynomial σ R →+* mv_polynomial σ S := ring_hom.of (map f),
  show F (powersum_symmetric σ R n) = powersum_symmetric σ S n,
  rw [powersum_symmetric, F.map_sum],
  apply fintype.sum_congr,
  intro,
  rw [F.map_pow, ring_hom.coe_of, map_X],
end

lemma rename_powersum_symmetric (n : ℕ) (e : σ ≃ τ) :
  rename e (powersum_symmetric σ R n) = powersum_symmetric τ R n :=
begin
  let F : mv_polynomial σ R →+* mv_polynomial τ R := ring_hom.of (rename e),
  show F (powersum_symmetric σ R n) = powersum_symmetric τ R n,
  rw [powersum_symmetric, F.map_sum],
  rw ← finset.sum_equiv e.symm,
  apply fintype.sum_congr,
  intro s,
  show F (X ((e.symm) s) ^ n) = X s ^ n,
  rw [F.map_pow, ring_hom.coe_of, rename_X, equiv.apply_symm_apply],
end

lemma powersum_symmetric_is_symmetric (n : ℕ) :
  is_symmetric (powersum_symmetric σ R n) :=
rename_powersum_symmetric n

open monomial_symmetric monomial_symmetric.signature
local attribute [instance] support_fintype

lemma powersum_symmetric_eq_monomial_symmetric [nonempty σ] (n : ℕ) (h : 0 < n) :
  powersum_symmetric σ R n = monomial_symmetric σ R (single _ n) :=
begin
  let f : σ → {d // to_signature d = single (fintype.card σ) n} :=
  λ i,⟨finsupp.single i n, to_signature_single _ _⟩,
  have hf : function.bijective f,
  { split,
    { intros i j hij, rwa [subtype.ext, finsupp.single_left_inj (ne_of_gt h)] at hij, },
    { rintro ⟨d, hd⟩,
      obtain ⟨i, hi⟩ : d.support.nonempty,
      { contrapose! h,
        simp only [finset.nonempty, classical.not_exists_not, finsupp.mem_support_iff] at h,
        replace hd := congr_arg (λ l, list.sum (signature.coeffs l)) hd,
        have hσ : 0 < fintype.card σ,
        { exact fintype.card_pos_iff.mpr ‹_› },
        simp only [sum_coeffs_to_signature, sum_coeffs_single _ _ hσ, fintype.sum_eq_zero _ h] at hd,
        rw [hd] },
      use i,
      simp only [f],
      ext j,
      rw finsupp.single_apply,
      classical, split_ifs with hij,
      sorry, sorry } },
  let e : σ ≃ {d // to_signature d = single (fintype.card σ) n} :=
  equiv.of_bijective f hf,
  { rw [powersum_symmetric, monomial_symmetric, ← finset.sum_equiv e],
    apply fintype.sum_congr,
    intro i,
    dsimp,
    rw [monomial_eq, C_1, one_mul, finsupp.prod_single_index],
    exact pow_zero _ },
end

end
