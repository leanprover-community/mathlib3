/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/
import data.finsupp.interval
import data.fintype.card
import data.list.nat_antidiagonal
import ring_theory.mv_polynomial.homogeneous
import ring_theory.mv_polynomial.symmetric

open equiv (perm)
open_locale big_operators

/-! ### TO MOVE -/

namespace fin
variables {n : ℕ}

lemma cast_succ_ne_last (a : fin n) : cast_succ a ≠ last n := a.cast_succ_lt_last.ne

end fin

namespace list
variables {α : Type*} [linear_order α]

lemma le_of_forall_nth_le_le : Π {n : ℕ} (l₁ l₂ : list α) (h₁ : l₁.length = n) (h₂ : l₂.length = n)
  (H : ∀ (i : ℕ) (hi₁ : i < l₁.length) (hi₂ : i < l₂.length), l₁.nth_le i hi₁ ≤ l₂.nth_le i hi₂),
  l₁ ≤ l₂
| 0       []         []         rfl rfl H := le_rfl
| (n + 1) (a₁ :: l₁) (a₂ :: l₂) h₁  h₂  H :=
begin
  contrapose! H,
  cases H with H_h H_h,
  { change l₂ < l₁ at H_h,
    contrapose! H_h,
    simp only [add_left_inj, length] at h₁ h₂,
    apply le_of_forall_nth_le_le _ _ h₁ h₂,
    intros i hi₁ hi₂,
    specialize H_h (i + 1) (nat.add_lt_add_right hi₁ 1),
    rw [not_exists] at H_h,
    specialize H_h (nat.add_lt_add_right hi₂ 1),
    rwa not_lt at H_h },
  { exact ⟨0, nat.zero_lt_succ _, nat.zero_lt_succ _, H_h⟩ }
end

-- are these even true??
@[simp] lemma nth_le_cons_cast_succ {α : Type*} (a : α) (l : list α) (i : fin l.length) :
  (a :: l : list α).nth_le i i.cast_succ.2 = l.nth_le i i.2 :=
sorry

@[simp] lemma nth_le_cons_length' {α : Type*} (a : α) (l : list α) (h) :
  (a :: l : list α).nth_le l.length h = a :=
sorry

lemma nth_le_le_sum (L : list ℕ) {i : ℕ} {h : i < L.length} : L.nth_le i h ≤ L.sum :=
begin
  revert i, induction L, simp,
  intros, cases i, simp, transitivity L_tl.sum, apply L_ih, simp
end

end list

namespace multiset
variables {σ : Type*}

-- move this
lemma ugly (l : list σ) :
  multiset.map (λ (i : fin l.length), l.nth_le i i.2) finset.univ.val = (l : multiset σ) :=
begin
  induction l with a l ih,
  { refl },
  have h₁ : (finset.map fin.cast_succ.to_embedding (@finset.univ (fin l.length) _)).1 =
      finset.univ.1.map fin.cast_succ,
    from finset.map_val _ _,
  have h₂ : fin.last l.length ∉ finset.image fin.cast_succ finset.univ,
  { rw [finset.mem_image], simp [fin.cast_succ_ne_last] },
  rw [fin.univ_cast_succ, finset.cons_val, multiset.map_cons, h₁, multiset.map_map],
  simp [function.comp, list.nth_le_cons_cast_succ, ih],
  sorry,
  apply_instance,
end

end multiset

section wf

variables {α : Type*} (r : α → α → Prop) [is_trans α r] [is_irrefl α r]

lemma well_founded_of_finite (h : ∀ a₀, set.finite {a | r a a₀}) :
  well_founded r :=
⟨λ a₀, acc.intro _ (λ b hb, begin
  refine @well_founded.fix {a | r a a₀} (λ b, acc r b) (λ x y : {a | r a a₀}, r x y)
    (@finite.well_founded_of_trans_of_irrefl _ (h a₀).to_subtype
      (λ x y : {a | r a a₀}, r x y) ⟨λ x y z h₁ h₂, trans h₁ h₂⟩
      ⟨λ x, irrefl x⟩) _ ⟨b, hb⟩,
  rintro ⟨b, hb⟩ ih,
  exact acc.intro _ (λ y hy, ih ⟨y, trans hy hb⟩ hy)
end)⟩

end wf

namespace finsupp
noncomputable theory
open_locale classical
variables {ι α β : Type*} [has_zero β]

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

variables [has_zero α] [decidable_eq α]

lemma support_indicator (s : finset ι) (f : ι → α) :
  (indicator s $ λ i _, f i).support = s.filter (λ i, f i ≠ 0) :=
by { ext, simp }

end finsupp

/-! ### Proper start of the file -/

noncomputable theory
open_locale classical

namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {R : Type*} {S : Type*}

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
    uniq := by { rintro ⟨s, hs⟩, refine subtype.ext _, rwa finset.card_eq_zero at hs } },
  simp only [elementary_symmetric, finset.univ_unique, finset.sum_singleton],
  exact finset.prod_empty,
end

lemma elementary_symmetric_eq_sum_monomial (n : ℕ) :
  elementary_symmetric σ R n =
    ∑ t : {s : finset σ // s.card = n}, monomial (finsupp.indicator ↑t (λ _ _, 1)) 1 :=
by simp [elementary_symmetric, monomial_eq, C_1, finsupp.prod, finsupp.support_indicator]

variables {σ R}

@[simp] lemma map_elementary_symmetric (n : ℕ) (f : R →+* S) :
  map f (elementary_symmetric σ R n) = elementary_symmetric σ S n :=
by simp [elementary_symmetric, map_sum, map_prod]

lemma rename_elementary_symmetric (n : ℕ) (e : σ ≃ τ) :
  rename e (elementary_symmetric σ R n) = elementary_symmetric τ R n :=
begin
  simp only [elementary_symmetric, map_sum],
  refine fintype.sum_equiv (e.finset_congr.subtype_equiv $ λ s,
      by simp only [equiv.finset_congr, equiv.coe_fn_mk, finset.card_map]) _ _ _,
  simp [map_prod],
end

lemma elementary_symmetric_is_symmetric (n : ℕ) : is_symmetric (elementary_symmetric σ R n) :=
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
      obtain hd | hd := order.le_succ_iff_eq_or_le.1 (H2 i),
      { exact hd },
      { rw le_zero_iff at hd,
        cases finsupp.mem_support_iff.1 hi hd } },
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
    { simp only [finsupp.support_indicator, finset.filter_true, ne.def, not_false_iff, one_ne_zero,
        subtype.coe_mk]},
    { ext i,
      by_cases hi : i ∈ d.support,
      { simp only [H3 i hi, finsupp.indicator_apply, subtype.coe_mk, finsupp.mem_support_iff,
          ne.def, nat.one_ne_zero, not_false_iff, dite_eq_ite, if_true] },
      { rw finsupp.not_mem_support_iff at hi,
        simp only [hi, finsupp.indicator_apply, subtype.coe_mk, finsupp.mem_support_iff, ne.def,
          eq_self_iff_true, not_true, dite_eq_ite, if_false] } } },
  { suffices : (λ (x : {s : finset σ // s.card = n}), finsupp.indicator ↑x (λ _ _, 1) = d) =
      λ _, false,
    { simp only [this, finset.card_empty, nat.cast_zero, finset.filter_false] },
    ext ⟨s, hs⟩,
    simp only [subtype.coe_mk, iff_false],
    contrapose! H,
    rw [← H, ← hs],
    split,
    { conv_rhs { rw [finset.card_eq_sum_ones, ← fintype.sum_extend_by_zero] },
      apply fintype.sum_congr,
      intro i, split_ifs; refl },
    { intro i,
      by_cases hi : i ∈ s,
      { rw finsupp.indicator_of_mem _ _ _ hi },
      { rw finsupp.indicator_of_not_mem _ _ _ hi,
        apply nat.zero_le _ } } }
end

end

section
variables [fintype σ] [comm_ring R]

lemma aeval_elementary_symmetric_is_symmetric (φ : mv_polynomial ℕ R) :
  is_symmetric (aeval (elementary_symmetric σ R) φ) :=
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

lemma coeffs_injective : function.injective (coeffs : signature n → list ℕ) :=
by { rintro ⟨l₁, _, _⟩ ⟨l₂, _, _⟩ h, congr, exact h }

@[ext]
lemma ext {l₁ l₂ : signature n} (h : l₁.coeffs = l₂.coeffs) : l₁ = l₂ :=
coeffs_injective h

lemma ext' {l₁ l₂ : signature n} (h : l₁.coeffs ~ l₂.coeffs) : l₁ = l₂ :=
ext $ list.eq_of_perm_of_sorted h l₁.sorted l₂.sorted

lemma ext_iff {l₁ l₂ : signature n} : l₁ = l₂ ↔ l₁.coeffs = l₂.coeffs :=
⟨congr_arg _, ext⟩

lemma ext_iff' {l₁ l₂ : signature n} : l₁ = l₂ ↔ l₁.coeffs ~ l₂.coeffs :=
⟨by { rintro rfl, refl }, ext'⟩

-- instance (n : ℕ) : partial_order (signature n) :=
-- { le := λ l₁ l₂, l₁.coeffs.sum < l₂.coeffs.sum ∨ (l₁.coeffs.sum = l₂.coeffs.sum ∧ l₁.coeffs ≤ l₂.coeffs),
--   le_refl := by { intro l, right, split; refl },
--   le_trans :=
--   begin
--     rintro l₁ l₂ l₃ (h₁₂|⟨h₁₂, h₁₂'⟩) (h₂₃|⟨h₂₃, h₂₃'⟩),
--     { left, exact lt_trans h₁₂ h₂₃ },
--     { left, rwa ← h₂₃ },
--     { left, rwa h₁₂ },
--     { right, exact ⟨h₂₃ ▸ h₁₂, le_trans h₁₂' h₂₃'⟩ }
--   end,
--   le_antisymm :=
--   begin
--     rintro l₁ l₂ (h₁₂|⟨h₁₂, h₁₂'⟩) (h₂₁|⟨h₂₁, h₂₁'⟩),
--     { exfalso, exact lt_irrefl _ (lt_trans h₁₂ h₂₁) },
--     { exfalso, rw h₂₁ at h₁₂, exact lt_irrefl _ h₁₂ },
--     { exfalso, rw h₁₂ at h₂₁, exact lt_irrefl _ h₂₁ },
--     { apply ext, rw le_antisymm h₁₂' h₂₁' }
--   end }

instance (n : ℕ) : linear_order (signature n) :=
linear_order.lift' signature.coeffs coeffs_injective

instance : unique (signature 0) :=
{ default := ⟨[], list.sorted_nil, rfl⟩,
  uniq    := by { intro l, ext1, rw list.eq_nil_of_length_eq_zero l.length } }

lemma lt_iff : ∀ {n : ℕ} {l₁ l₂ : signature n},
  l₁ < l₂ ↔ l₁.coeffs.head < l₂.coeffs.head ∨
            (l₁.coeffs.head = l₂.coeffs.head ∧ l₁.coeffs.tail < l₂.coeffs.tail)
| 0 ⟨[], s₁, h₁⟩ ⟨[], s₂, h₂⟩ :=
begin
  show list.nil < [] ↔ 0 < 0 ∨ 0 = 0 ∧ [] < [],
  simp only [true_and, eq_self_iff_true, lt_irrefl 0, false_or],
end
| (n+1) ⟨(n₁ :: l₁), s₁, h₁⟩ ⟨(n₂ :: l₂), s₂, h₂⟩ :=
begin
  show (list.cons n₁ l₁) < n₂ :: l₂ ↔ n₁ < n₂ ∨ n₁ = n₂ ∧ l₁ < l₂,
  split,
  { rintro (_ | _ | _),
    { right, exact ⟨rfl, ‹_›⟩ },
    { left, assumption } },
  { rintro (H | ⟨rfl, H⟩),
    { exact list.lex.rel H },
    { exact list.lex.cons H } }
end

lemma le_iff : ∀ {n : ℕ} {l₁ l₂ : signature n},
  l₁ ≤ l₂ ↔ l₁.coeffs.head ≤ l₂.coeffs.head ∧
            (l₁.coeffs.head = l₂.coeffs.head → l₁.coeffs.tail ≤ l₂.coeffs.tail)
| 0 ⟨[], s₁, h₁⟩ ⟨[], s₂, h₂⟩ :=
begin
  show list.nil ≤ [] ↔ 0 ≤ 0 ∧ (0 = 0 → [] ≤ []),
  simp only [true_and, eq_self_iff_true, le_refl 0, true_implies_iff],
end
| (n+1) ⟨(n₁ :: l₁), s₁, h₁⟩ ⟨(n₂ :: l₂), s₂, h₂⟩ :=
begin
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, lt_iff, or_assoc, ext_iff],
  show n₁ < n₂ ∨ n₁ = n₂ ∧ l₁ < l₂ ∨ list.cons n₁ l₁ = n₂ :: l₂ ↔
    (n₁ < n₂ ∨ n₁ = n₂) ∧ (n₁ = n₂ → l₁ ≤ l₂),
  simp only [le_iff_lt_or_eq],
  split,
  { rintro (H|⟨rfl, H⟩|⟨rfl,rfl⟩),
    { refine ⟨or.inl H, _⟩, rintro rfl, exfalso, exact lt_irrefl _ H },
    { exact ⟨or.inr rfl, λ _, or.inl H⟩ },
    { exact ⟨or.inr rfl, λ _, or.inr rfl⟩ } },
  { rintro ⟨H|rfl, H'⟩,
    { exact or.inl H },
    { rcases H' rfl with H|rfl,
      { right, left, exact ⟨rfl, H⟩ },
      { right, right, exact ⟨rfl, rfl⟩ } } }
end

lemma le_of_forall_nth_le_le {n : ℕ} {l₁ l₂ : signature n}
  (h : ∀ (i : ℕ) (hi : i < n),
    l₁.coeffs.nth_le i (l₁.length.symm ▸ hi) ≤ l₂.coeffs.nth_le i (l₂.length.symm ▸ hi)) :
  l₁ ≤ l₂ :=
begin
  apply list.le_of_forall_nth_le_le _ _ l₁.length l₂.length,
  intros i hi₁ hi₂,
  apply h,
  rwa l₁.length at hi₁,
end

lemma lt_wf (n : ℕ) : well_founded (@has_lt.lt (signature n) _) :=
begin
  apply well_founded_of_finite,
  intro l₀,
  let k := l₀.coeffs.sum + 1,
  have hk : ∀ i : fin n, l₀.coeffs.nth_le i (l₀.length.symm ▸ i.2) < k, ---sorry was here
  { intro, rw nat.lt_add_one_iff, apply list.nth_le_le_sum },
  constructor,
  have aux : ∀ (l : {l : signature n // l < l₀}) (i : ℕ) (hi : i < (l : signature n).coeffs.length),
    (l : signature n).coeffs.nth_le i hi < k,
  { rintro ⟨l,hl⟩ i hi,
    have h : l.coeffs.head < k,
    { calc l.coeffs.head ≤ l₀.coeffs.head : _
                     ... < k              : _,
      { rw lt_iff at hl, rw le_iff_eq_or_lt, tauto },
      { rw nat.lt_add_one_iff, apply list.head_le_sum } },
    cases n,
    { simpa [l.length, nat.nat_zero_eq_zero, subtype.coe_mk] using hi },
    cases i, rw list.nth_le_zero, apply h,
    have H := l.sorted,
    rw [list.sorted, list.pairwise_iff_nth_le] at H,
    apply lt_of_le_of_lt (H 0 _ _ _), rw list.nth_le_zero, apply h,
    apply nat.succ_pos },
  let f : {l : signature n // l < l₀} → (fin n → fin k) :=
  λ l i, ⟨(l : signature n).coeffs.nth_le i ((l : signature n).length.symm ▸ i.2), aux l _ _⟩,
  refine fintype.of_injective f (λ l₁ l₂ h, subtype.ext $ signature.ext $ list.ext_le _ $
    λ i hi₁ hi₂, _),
  { rw [signature.length, signature.length] },
  { rw signature.length at hi₁,
    rw [function.funext_iff] at h,
    specialize h ⟨i, hi₁⟩,
    rwa [fin.ext_iff] at h }
end

instance (n : ℕ) : has_zero (signature n) :=
⟨{ coeffs := list.replicate n 0,
   sorted := list.pairwise_replicate le_rfl _,
   length := list.length_replicate _ _ }⟩

@[simp] lemma coeffs_zero : (0 : signature n).coeffs = list.replicate n 0 := rfl

lemma zero_le (l : signature n) : 0 ≤ l :=
le_of_forall_nth_le_le $ λ i hi, by simp only [coeffs_zero, list.nth_le_replicate, zero_le]

def single : Π (n k : ℕ), signature n
| 0     _ := ⟨[], list.sorted_nil, rfl⟩
| (n+1) k :=
  { coeffs := k :: list.replicate n 0,
    sorted := list.sorted_cons.2 ⟨λ i hi, (list.eq_of_mem_replicate hi).trans_le $ nat.zero_le _,
      list.pairwise_replicate le_rfl _⟩,
    length := by rw [list.length_cons, list.length_replicate] }

@[simp] lemma single_zero_right : ∀ (n : ℕ), single n 0 = 0
| 0     := rfl
| (n+1) := rfl

@[simp] lemma sum_coeffs_single (n k : ℕ) (h : 0 < n) :
  (single n k).coeffs.sum = k :=
begin
  cases n,
  { exfalso, exact lt_irrefl 0 h },
  { show list.sum (k :: list.replicate n 0) = k,
    rw [list.sum_cons, list.sum_replicate, nsmul_zero, add_zero] }
end

end signature

/-- The signature associated with `d : σ →₀ ℕ` is the sorted list of function values of `d`. -/
def to_signature (d : σ →₀ ℕ) : signature (card σ) :=
{ coeffs := multiset.sort (≥) (multiset.map d (finset.univ : finset σ).1),
  sorted := multiset.sort_sorted _ _,
  length := by { simp only [multiset.length_sort, multiset.card_map], refl } }

lemma coeffs_to_signature (d : σ →₀ ℕ) :
  (to_signature d).coeffs = multiset.sort (≥) (multiset.map d (finset.univ).1) := rfl

@[simp] lemma sum_coeffs_to_signature (d : σ →₀ ℕ) :
  (to_signature d).coeffs.sum = ∑ i, d i :=
by { rw [coeffs_to_signature, ← multiset.coe_sum, multiset.sort_eq], refl }

@[simp] lemma to_signature_zero : to_signature (0 : σ →₀ ℕ) = 0 :=
begin
  apply signature.ext',
  rw [coeffs_to_signature, ← multiset.coe_eq_coe, multiset.sort_eq, signature.coeffs_zero],
  apply multiset.eq_replicate.mpr,
  refine ⟨multiset.card_map _ _, λ k hk, _⟩,
  obtain ⟨i, hi, rfl⟩ := multiset.mem_map.1 hk,
  refl,
end

lemma count_zero_coeffs_to_signature (d : σ →₀ ℕ) :
  multiset.count 0 (to_signature d).coeffs = fintype.card σ - d.support.card :=
begin
  classical,
  rw [multiset.count, coeffs_to_signature, multiset.sort_eq, multiset.countp_map],
  show finset.card (finset.filter _ _) = _,
  rw [← finset.card_univ, ← finset.card_sdiff (finset.subset_univ d.support)],
  congr' 1,
  ext i,
  simp only [eq_comm, finsupp.mem_support_iff, finset.mem_sdiff, finset.mem_filter, classical.not_not]
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
    contrapose! hn, exact multiset.eq_of_mem_replicate hn },
  { subst hn,
    rw [count_zero_coeffs_to_signature, finsupp.support_single_ne_zero hk, finset.card_singleton] },
  { subst hnk,
    rw [coeffs_to_signature, multiset.sort_eq, multiset.count, multiset.countp_map],
    show finset.card (finset.filter _ _) = 1,
    convert finset.card_singleton i,
    ext j,
    simp only [true_and, finset.mem_univ, finset.mem_singleton, finset.mem_filter, finsupp.single_apply],
    split_ifs with h,
    { simp only [h, eq_self_iff_true] },
    { simp only [h, hn, eq_comm] } },
  { apply multiset.count_eq_zero_of_not_mem,
    rw [coeffs_to_signature, multiset.sort_eq],
    contrapose! hn,
    obtain ⟨j, hj, rfl⟩ := multiset.mem_map.mp hn,
    rw finsupp.single_apply,
    split_ifs, swap, refl,
    subst h, exfalso, apply hnk, exact finsupp.single_eq_same }
end

lemma count_coeffs_signature_single (n m k : ℕ) :
  multiset.count n (signature.single m k).coeffs =
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
    simp only [signature.single, multiset.coe_nil, not_false_iff, multiset.not_mem_zero] },
  { subst hk, subst hn, rw [signature.single_zero_right], apply multiset.count_replicate },
  { subst hk, rw [signature.single_zero_right],
    apply multiset.count_eq_zero_of_not_mem,
    contrapose! hn, exact multiset.eq_of_mem_replicate hn },
  { subst hn,
    cases m, { rw [nat.zero_sub, multiset.count_eq_zero], apply multiset.not_mem_zero },
    { simp only [nat.succ_sub_succ_eq_sub, nat.sub_zero, multiset.coe_count],
      erw [list.count_cons_of_ne, list.count_replicate_self], symmetry, exact hk } },
  { subst hnk, cases m, { contradiction },
    simp only [signature.single, list.count_cons_self, multiset.coe_count],
    rw [list.count_replicate, if_neg hn] },
  { rw [multiset.count_eq_zero],
    cases m,
    { simp only [signature.single, multiset.coe_nil, not_false_iff, multiset.not_mem_zero] },
    simp only [signature.single, list.mem_cons_iff, multiset.mem_coe],
    push_neg,
    refine ⟨hnk, _⟩,
    contrapose! hn,
    exact list.eq_of_mem_replicate hn }
end

@[simp] lemma to_signature_single (i : σ) (k : ℕ) :
  to_signature (finsupp.single i k) = signature.single _ k :=
begin
  have : card σ ≠ 0 := pos_iff_ne_zero.1 (card_pos_iff.mpr ⟨i⟩),
  apply signature.ext',
  rw [← multiset.coe_eq_coe, multiset.ext],
  intro n,
  rw [count_coeffs_to_signature_single, count_coeffs_signature_single, if_neg this],
end

@[simp] lemma coeffs_to_signature_map_domain_of_equiv (d : σ →₀ ℕ) (e : σ ≃ τ) :
  (to_signature (d.map_domain e)).coeffs = (to_signature d).coeffs :=
begin
  apply list.eq_of_perm_of_sorted _ (signature.sorted _) (signature.sorted _),
  simp only [coeffs_to_signature, ← multiset.coe_eq_coe, multiset.sort_eq],
  ext1 i,
  simp only [multiset.count, multiset.countp_map],
  show finset.card (finset.filter _ _) = finset.card (finset.filter _ _),
  suffices : (finset.filter (λ (a : τ), i = (finsupp.map_domain e d) a) finset.univ) =
    finset.map e.to_embedding (finset.filter (λ (a : σ), i = d a) finset.univ),
  { rw [this, finset.card_map] },
  ext b,
  simp only [true_and, exists_prop, finset.mem_univ, finset.mem_map, finset.mem_filter,
    equiv.coe_to_embedding],
  rw [←e.apply_symm_apply b, finsupp.map_domain_apply e.injective, equiv.apply_symm_apply],
  split,
  { rintro rfl, use e.symm b, simp only [eq_self_iff_true, equiv.apply_symm_apply, and_self] },
  { rintro ⟨a, rfl, rfl⟩, simp only [equiv.symm_apply_apply] }
end

end monomial_symmetric

section
open fintype monomial_symmetric
variables (σ R) [fintype σ] [fintype τ] [comm_semiring R] [comm_semiring S]

noncomputable def monomial_symmetric.support_fintype (l : signature (card σ)) :
  fintype {d // to_signature d = l} :=
set.finite.fintype $
begin
  let f : σ →₀ ℕ := finsupp.equiv_fun_on_finite.symm (λ _, l.coeffs.sum),
  refine (set.finite_Iic f).subset _,
  rintro d hd i,
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
def monomial_symmetric (l : signature (card σ)) : mv_polynomial σ R :=
∑ d : {d // to_signature d = l}, monomial ↑d 1

@[simp] lemma monomial_symmetric_zero :
  monomial_symmetric σ R 0 = 1 :=
begin
  letI : unique {d : σ →₀ ℕ // to_signature d = 0} :=
  { default := ⟨0, to_signature_zero⟩,
    uniq := begin
      rintro ⟨d, hd⟩, ext i,
      have h := congr_arg ((coe : list ℕ → multiset ℕ) ∘ signature.coeffs) hd,
      simp only [coeffs_to_signature, function.comp_app, signature.coeffs_zero, multiset.sort_eq]
        at h,
      suffices : d i ∈ multiset.map d finset.univ.val,
      { rw h at this, apply multiset.eq_of_mem_replicate this },
      rw multiset.mem_map,
      exact ⟨i, finset.mem_univ i, rfl⟩
    end },
  simp only [monomial_symmetric, finset.univ_unique, finset.sum_singleton],
  refl,
end

variables {σ τ R}

lemma monomial_symmetric_is_homogeneous (l : signature (card σ)) (n : ℕ) (hn : l.coeffs.sum = n) :
  (monomial_symmetric σ R l).is_homogeneous n :=
begin
  apply is_homogeneous.sum,
  rintro ⟨d, rfl⟩ H,
  apply is_homogeneous_monomial,
  convert hn using 1,
  simp only [sum_coeffs_to_signature, subtype.coe_mk],
  exact d.sum_eq_sum_univ (λ _, id) (λ _, rfl),
end

lemma coeff_monomial_symmetric (l : signature (card σ)) (d : σ →₀ ℕ) :
  coeff d (monomial_symmetric σ R l) = if to_signature d = l then 1 else 0 :=
begin
  simp only [monomial_symmetric, coeff_sum, coeff_monomial],
  split_ifs with h,
  { let d' : {d // to_signature d = l} := ⟨d, h⟩,
    rw [finset.sum_eq_single d', subtype.coe_mk, if_pos rfl],
    { rintro ⟨i, hi⟩ H hid,
      exact if_neg (subtype.coe_injective.ne hid) },
    { intro H, exfalso, exact H (finset.mem_univ _) } },
  { rw fintype.sum_eq_zero,
    rintro ⟨i, hi⟩,
    apply if_neg,
    rintro rfl,
    exact h hi }
end

lemma map_monomial_symmetric (l : signature (card σ)) (f : R →+* S) :
  map f (monomial_symmetric σ R l) = monomial_symmetric σ S l :=
begin
  rw [monomial_symmetric, map_sum],
  simp only [map_monomial, ring_hom.map_one, monomial_symmetric],
end

lemma rename_monomial_symmetric (l : signature (card σ)) (l' : signature (card τ))
  (h : l.coeffs = l'.coeffs) (e : σ ≃ τ) :
  rename e (monomial_symmetric σ R l) = monomial_symmetric τ R l' :=
begin
  rw [monomial_symmetric, map_sum],
  refine fintype.sum_equiv ((finsupp.equiv_congr_left e).subtype_equiv _) _ _ _,
  { sorry },
  { rintro ⟨d, hd⟩,
    simp only [rename_monomial, subtype.coe_mk, finsupp.equiv_congr_left_apply,
      equiv.subtype_equiv_apply, finsupp.equiv_map_domain_eq_map_domain] }
end

lemma monomial_symmetric_is_symmetric (l : signature (card σ)) :
  is_symmetric (monomial_symmetric σ R l) :=
rename_monomial_symmetric l l rfl

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
  let f : σ →₀ ℕ := finsupp.equiv_fun_on_finite.symm (λ _, n),
  refine (set.finite_Iic f).subset _,
  rintro d (rfl : _ = n) i,
  exact finset.single_le_sum (λ _ _, nat.zero_le _) (finset.mem_univ _),
end

local attribute [instance] complete_homogeneous.support_fintype

/-- `complete_homogeneous σ R n` is the `n`th complete homogeneous symmetric polynomial
with variables indexed by `σ` and coefficients in `R`.
It is defined as the sum of all monomials of degree `n`. -/
noncomputable def complete_homogeneous (n : ℕ) : mv_polynomial σ R :=
∑ d : {d : σ →₀ ℕ // ∑ i, d i = n}, monomial ↑d 1

@[simp] lemma complete_homogeneous_zero : complete_homogeneous σ R 0 = 1 :=
begin
  letI : unique {d : σ →₀ ℕ // ∑ i, d i = 0} :=
  { default := ⟨0, by simp only [finsupp.zero_apply, finset.sum_const_zero]⟩,
    uniq := begin
      rintro ⟨d, hd⟩,
      ext i,
      rw [finset.sum_eq_zero_iff] at hd,
      exact hd _ (finset.mem_univ _)
    end },
  simp only [complete_homogeneous, finset.univ_unique, finset.sum_singleton],
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
    { exact λ t' ht' H, if_neg (subtype.coe_injective.ne H) },
  { intro H, exfalso, exact H (finset.mem_univ _) } },
  { apply (complete_homogeneous_is_homogeneous σ R n).coeff_eq_zero,
    contrapose! h,
    simpa only [finsupp.sum, h, id.def] using (d.sum_eq_sum_univ (λ _, id) (λ _, rfl)).symm }
end

lemma map_complete_homogeneous (n : ℕ) (f : R →+* S) :
  map f (complete_homogeneous σ R n) = complete_homogeneous σ S n :=
begin
  rw [complete_homogeneous, map_sum],
  refine fintype.sum_congr _ _ (λ a, _),
  rw [map_monomial, f.map_one],
end

lemma rename_complete_homogeneous (n : ℕ) (e : σ ≃ τ) :
  rename e (complete_homogeneous σ R n) = complete_homogeneous τ R n :=
begin
  rw [complete_homogeneous, map_sum],
  refine fintype.sum_equiv ((finsupp.equiv_congr_left e).subtype_equiv $ λ d, _) _ _ (λ a, _),
  { rw fintype.sum_equiv e,
    simp },
  { simp [rename_monomial, finsupp.equiv_map_domain_eq_map_domain] }
end

lemma complete_homogeneous_is_symmetric (n : ℕ) : is_symmetric (complete_homogeneous σ R n) :=
rename_complete_homogeneous n

end

section
open monomial_symmetric fintype
variables [fintype σ] [comm_semiring R]

lemma to_signature_surjective : function.surjective (@to_signature σ _) :=
begin
  intro l,
  obtain ⟨e⟩ := fintype.equiv_fin σ,
  let f : fin (card σ) → fin l.coeffs.length := fin.cast l.length.symm,
  let g : fin l.coeffs.length → ℕ := λ i, l.coeffs.nth_le i i.2,
  let d : σ →₀ ℕ := finsupp.equiv_fun_on_finite.symm (g ∘ f ∘ e),
  use d,
  apply signature.ext',
  rw [coeffs_to_signature, ← multiset.coe_eq_coe, multiset.sort_eq],
  simp only [d, f, g, list.length, list.nth_le],
  show multiset.map (g ∘ f ∘ e) finset.univ.val = l.coeffs,
  rw [← multiset.map_map],
  have : multiset.map (f ∘ e) finset.univ.val = finset.univ.val,
  { ext i,
    rw [multiset.count, multiset.countp_map, multiset.countp_eq_card_filter],
    show (finset.univ.filter (λ s : σ, i = f (e s))).card = (finset.univ.filter (eq i)).card,
    have inj : function.injective (fin.cast l.length),
    { intros x y H, rwa fin.ext_iff at H ⊢ },
    suffices : finset.univ.filter (λ s : σ, i = f (e s)) =
      finset.map (function.embedding.trans ⟨fin.cast l.length, inj⟩ e.symm.to_embedding)
        (finset.univ.filter (eq i)),
    { rw [this, finset.card_map] },
    ext x,
    simp only [true_and, exists_prop, finset.mem_univ, function.embedding.trans_apply,
      finset.mem_map, function.embedding.coe_fn_mk, finset.mem_filter,
      equiv.to_embedding_coe_fn, exists_eq_left'],
    split; rintro rfl,
    { rw [equiv.symm_apply_eq, fin.ext_iff], refl },
    { rw [fin.ext_iff, equiv.apply_symm_apply], refl } },
  rw this,
  dsimp [g],
  clear_except,
  apply multiset.ugly
end

def to_signature_section : signature (card σ) → (σ →₀ ℕ) :=
classical.some (classical.axiom_of_choice (to_signature_surjective))

lemma to_signature_to_signature_section (l : signature (card σ)) :
  to_signature (to_signature_section l) = l :=
classical.some_spec (classical.axiom_of_choice (to_signature_surjective)) l

def signature_coefficient (φ : mv_polynomial σ R) (l : signature (card σ)) : R :=
coeff (to_signature_section l) φ

/--This should probably be proven by induction -/
lemma exists_perm_of_rel_univ (r : σ → σ → Prop):
  multiset.rel r (finset.univ : finset σ).1 (finset.univ : finset σ).1 →
  ∃ e : perm σ, ∀ i : σ, r i (e i) :=
begin
  sorry
end

lemma exists_perm_of_to_signature_eq_to_signature {d₁ d₂ : σ →₀ ℕ} :
  to_signature d₁ = to_signature d₂ →
  ∃ e : perm σ, d₂ = finsupp.map_domain e d₁ :=
begin
  intro h, --unfold to_signature at h,
  have h' :  (to_signature d₁).coeffs = (to_signature d₂).coeffs, rw h,
  have j : multiset.map d₁ (finset.univ : finset σ).1 = multiset.map d₂ (finset.univ : finset σ).1,
  { rw ← multiset.sort_eq ge (multiset.map ⇑d₁ finset.univ.val),
    rw ← multiset.sort_eq ge (multiset.map ⇑d₂ finset.univ.val),
    unfold to_signature at h', dsimp at h', rw h' },
  rw ← multiset.rel_eq at j, rw multiset.rel_map_left at j, rw multiset.rel_map_right at j,
  cases exists_perm_of_rel_univ _ j with e he, existsi e, ext,
  conv_rhs { rw ←  equiv.apply_symm_apply e a },
  rw [finsupp.map_domain_apply e.injective _ _, he (e.symm a)], simp
end

lemma is_symmetric.coeff_eq_coeff
  {φ : mv_polynomial σ R} (h : is_symmetric φ)
  (d₁ d₂ : σ →₀ ℕ) (hd : to_signature d₁ = to_signature d₂) :
  coeff d₁ φ = coeff d₂ φ :=
begin
  unfold coeff,
  unfold mv_polynomial.is_symmetric at h,
  simp [mv_polynomial.rename_eq] at h,
  cases exists_perm_of_to_signature_eq_to_signature hd with e he, rw he,
  rw [← finsupp.map_domain_apply (finsupp.map_domain_injective e.injective) φ d₁, @h e]
end

lemma is_symmetric.coeff_to_signature_section
  {φ : mv_polynomial σ R} (h : is_symmetric φ) (d : σ →₀ ℕ) :
  coeff d φ = coeff (to_signature_section (to_signature d)) φ :=
by { apply h.coeff_eq_coeff, rw to_signature_to_signature_section }

lemma sum_signature_coefficient_mul_monomial_symmetric (φ : mv_polynomial σ R) (h : φ.is_symmetric) :
  ∑ l in finset.image (to_signature) φ.support,
    C (signature_coefficient φ l) * monomial_symmetric σ R l = φ :=
begin
  rw [φ.as_sum, finset.sum_subtype _ (λ _, iff.rfl)],
  swap, { apply_instance },
  sorry
  -- have := finset.sum_fiberwise φ.support _ (λ d, monomial d (coeff d φ)),
end

variables (R)

def monomial_symmetric_as_polynomial_elementary_symmetric :
  Π (l : signature (card σ)), mv_polynomial ℕ R
| l := sorry
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨_, signature.lt_wf (card σ)⟩],
  dec_tac := tactic.assumption }

end

section
open fintype monomial_symmetric
variables [fintype σ] [comm_ring R]

lemma aeval_monomial_symmetric_as_polynomial_elementary_symmetric (l : signature (card σ)) :
  aeval (elementary_symmetric σ R) (monomial_symmetric_as_polynomial_elementary_symmetric R l) =
    monomial_symmetric σ R l :=
begin
  sorry
end

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
  let L := d.antidiagonal'.support.filter (λ p : (σ →₀ ℕ) × (σ →₀ ℕ), p.1.sum (λ _, id) % 2 = 0),
  let R := d.antidiagonal'.support.filter (λ p : (σ →₀ ℕ) × (σ →₀ ℕ), p.1.sum (λ _, id) % 2 = 1),
  classical,
  have hLR : d.antidiagonal'.support = L ∪ R,
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
    { intros i j hij, rwa [subtype.ext, finsupp.single_left_inj (ne_of_gt h)] at hij },
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
