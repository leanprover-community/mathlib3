/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import data.fintype.card
import ring_theory.polynomial.homogeneous
import data.list.antidiagonal
import tactic

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

-- move this
namespace multiset
lemma countp_map {α : Type*} {β : Type*}
  (f : α → β) (s : multiset α) (p : β → Prop) [decidable_pred p] :
  countp p (map f s) = (s.filter (λ a, p (f a))).card :=
begin
  apply multiset.induction_on s,
  { simp only [countp_zero, filter_zero, card_zero, map_zero] },
  { intros a t IH,
    by_cases h : p (f a),
    { simp only [IH, h, card_cons, countp_cons_of_pos, filter_cons_of_pos, map_cons] },
    { simp only [IH, h, countp_cons_of_neg, filter_cons_of_neg, not_false_iff, map_cons] } }
end

end multiset

-- move this
namespace list
variables {α : Type*} [linear_order α]

lemma le_of_forall_nth_le_le : Π {n : ℕ} (l₁ l₂ : list α) (h₁ : l₁.length = n) (h₂ : l₂.length = n)
  (H : ∀ (i : ℕ) (hi₁ : i < l₁.length) (hi₂ : i < l₂.length), l₁.nth_le i hi₁ ≤ l₂.nth_le i hi₂),
  l₁ ≤ l₂
| 0     []         []         rfl rfl H := le_refl _
| (n+1) (a₁ :: l₁) (a₂ :: l₂) h₁  h₂  H :=
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
  { exact ⟨0, nat.zero_lt_succ _, nat.zero_lt_succ _, H_h⟩, }
end

end list

-- move this
section wf

variables {α : Type*} (r : α → α → Prop) [is_trans α r] [is_irrefl α r]

lemma well_founded_of_finite (h : ∀ a₀, set.finite {a | r a a₀}) :
  well_founded r :=
⟨λ a₀, acc.intro _ (λ b hb, begin
  cases h a₀ with fint,
  refine @well_founded.fix {a | r a a₀} (λ b, acc r b) (λ x y : {a | r a a₀}, r x y)
    (@fintype.well_founded_of_trans_of_irrefl _ fint
      (λ x y : {a | r a a₀}, r x y) ⟨λ x y z h₁ h₂, trans h₁ h₂⟩
      ⟨λ x, irrefl x⟩) _ ⟨b, hb⟩,
  rintros ⟨b, hb⟩ ih,
  exact acc.intro _ (λ y hy, ih ⟨y, trans hy hb⟩ hy)
end)⟩

end wf

-- move this
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

/-
##############
Proper start of the file
##############
-/

noncomputable theory
open_locale classical

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

lemma coeffs_injective : function.injective (coeffs : signature n → list ℕ) :=
by { rintros ⟨l₁, _, _⟩ ⟨l₂, _, _⟩ h, congr, exact h }

@[ext]
lemma ext {l₁ l₂ : signature n} (h : l₁.coeffs = l₂.coeffs) : l₁ = l₂ :=
coeffs_injective h

lemma ext' {l₁ l₂ : signature n} (h : l₁.coeffs ~ l₂.coeffs) : l₁ = l₂ :=
ext $ list.eq_of_sorted_of_perm h l₁.sorted l₂.sorted

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
linear_order.lift signature.coeffs coeffs_injective (by apply_instance)

instance : unique (signature 0) :=
{ default := ⟨[], list.sorted_nil, rfl⟩,
  uniq    := by { intro l, ext1, rw list.eq_nil_of_length_eq_zero l.length, } }

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
  have hk : ∀ i : fin n, l₀.coeffs.nth_le i (l₀.length.symm ▸ i.2) < k,
  { sorry },
  constructor,
  have aux : ∀ (l : {l : signature n // l < l₀}) (i : ℕ) (hi : i < (l : signature n).coeffs.length),
    (l : signature n).coeffs.nth_le i hi < k,
  { rintros ⟨l,hl⟩ i hi,
    cases n,
    { simp only [l.length, nat.nat_zero_eq_zero, subtype.coe_mk] at hi, exact fin.elim0 ⟨i, hi⟩ },
    cases i,
    { rw list.nth_le_zero,
      calc l.coeffs.head ≤ l₀.coeffs.head : _
                     ... < k              : _,
      {  },
      {  } },
    have H := l.sorted,
    rw [list.sorted, list.pairwise_iff_nth_le] at H,
    apply lt_of_le_of_lt (H 0 i _ _), },
  let f : {l : signature n // l < l₀} → (fin n → fin k) :=
  λ l i, ⟨(l : signature n).coeffs.nth_le i ((l : signature n).length.symm ▸ i.2), aux l _ _⟩,
  apply fintype.of_injective f,
  intros l₁ l₂ h,
  rw [subtype.ext, signature.ext_iff],
  apply list.ext_le,
  { rw [l₁.val.length, l₂.val.length] },
  { intros i hi₁ hi₂,
    rw [l₁.val.length] at hi₁,
    rw [function.funext_iff] at h,
    specialize h ⟨i, hi₁⟩,
    rwa [fin.ext_iff] at h }
end

instance (n : ℕ) : has_zero (signature n) :=
⟨{ coeffs := list.repeat 0 n, sorted := list.sorted_repeat _ _ _, length := list.length_repeat _ _ }⟩

@[simp] lemma coeffs_zero : (0 : signature n).coeffs = list.repeat 0 n := rfl

lemma zero_le (l : signature n) : 0 ≤ l :=
begin
  apply le_of_forall_nth_le_le,
  intros i hi,
  simp only [coeffs_zero, list.nth_le_repeat, zero_le],
end

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
{ coeffs := multiset.sort (≥) (multiset.map d (finset.univ : finset σ).1),
  sorted := multiset.sort_sorted _ _,
  length := by { simp only [multiset.length_sort, multiset.card_map], refl } }

lemma coeffs_to_signature (d : σ →₀ ℕ) :
  (to_signature d).coeffs = multiset.sort (≥) (multiset.map d (finset.univ).1) := rfl

@[simp] lemma sum_coeffs_to_signature (d : σ →₀ ℕ) :
  (to_signature d).coeffs.sum = ∑ i, d i :=
by { rw [coeffs_to_signature, ← multiset.coe_sum, multiset.sort_eq], refl }

@[simp] lemma to_signature_zero :
  to_signature (0 : σ →₀ ℕ) = 0 :=
begin
  apply signature.ext',
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
    contrapose! hn, exact multiset.eq_of_mem_repeat hn, },
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
  apply signature.ext',
  rw [← multiset.coe_eq_coe, multiset.ext],
  intro n,
  rw [count_coeffs_to_signature_single, count_coeffs_signature_single, if_neg this],
end

@[simp] lemma coeffs_to_signature_map_domain_of_equiv (d : σ →₀ ℕ) (e : σ ≃ τ) :
  (to_signature (d.map_domain e)).coeffs = (to_signature d).coeffs :=
begin
  apply list.eq_of_sorted_of_perm _ (signature.sorted _) (signature.sorted _),
  simp only [coeffs_to_signature, ← multiset.coe_eq_coe, multiset.sort_eq],
  ext1 i,
  simp only [multiset.count, multiset.countp_map],
  show finset.card (finset.filter _ _) = finset.card (finset.filter _ _),
  suffices : (finset.filter (λ (a : τ), i = (finsupp.map_domain e d) a) finset.univ) =
    finset.map e.to_embedding (finset.filter (λ (a : σ), i = d a) finset.univ),
  { rw [this, finset.card_map], },
  ext b,
  simp only [true_and, exists_prop, finset.mem_univ, finset.mem_map, finset.mem_filter,
    equiv.to_embedding_coe_fn],
  have : b = e (e.symm b) := (e.apply_symm_apply b).symm,
  rw this,
  rw [finsupp.map_domain_apply e.injective],
  rw [equiv.apply_symm_apply],
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
def monomial_symmetric (l : signature (card σ)) : mv_polynomial σ R :=
∑ d : {d // to_signature d = l}, monomial d 1

@[simp] lemma monomial_symmetric_zero :
  monomial_symmetric σ R 0 = 1 :=
begin
  letI : unique {d : σ →₀ ℕ // to_signature d = 0} :=
  { default := ⟨0, to_signature_zero⟩,
    uniq := by { rintro ⟨d, hd⟩, rw subtype.ext, ext i,
                 have h := congr_arg ((coe : list ℕ → multiset ℕ) ∘ signature.coeffs) hd,
                 simp only [coeffs_to_signature, function.comp_app,
                    signature.coeffs_zero, multiset.sort_eq] at h,
                 suffices : d i ∈ multiset.map d finset.univ.val,
                 { rw h at this, apply multiset.eq_of_mem_repeat this },
                 rw multiset.mem_map,
                 exact ⟨i, finset.mem_univ i, rfl⟩ } },
  simp only [monomial_symmetric, univ_unique, finset.sum_singleton],
  refl
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
    { rintro ⟨i, hi⟩ H hid, apply if_neg, rwa [ne.def, subtype.ext] at hid },
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
  let F : mv_polynomial σ R →+* mv_polynomial σ S := ring_hom.of (map f),
  show F (monomial_symmetric σ R l) = monomial_symmetric σ S l,
  rw [monomial_symmetric, F.map_sum],
  simp only [map_monomial, ring_hom.coe_of, ring_hom.map_one, monomial_symmetric],
end

lemma rename_monomial_symmetric (l : signature (card σ)) (l' : signature (card τ))
  (h : l.coeffs = l'.coeffs) (e : σ ≃ τ) :
  rename e (monomial_symmetric σ R l) = monomial_symmetric τ R l' :=
begin
  let F : mv_polynomial σ R →+* mv_polynomial τ R := ring_hom.of (rename e),
  show F (monomial_symmetric σ R l) = monomial_symmetric τ R l',
  rw [monomial_symmetric, F.map_sum],
  let e' : {d // to_signature d = l} ≃ {d // to_signature d = l'} :=
  { to_fun := λ d, ⟨finsupp.map_domain e d, _⟩,
    inv_fun := λ d, ⟨finsupp.map_domain e.symm d, _⟩,
    left_inv := _,
    right_inv := _ },
  { rw ← finset.sum_equiv e'.symm,
    apply fintype.sum_congr,
    rintro ⟨d, hd⟩,
    simp only [rename_monomial, equiv.coe_fn_symm_mk, ring_hom.coe_of, subtype.coe_mk],
    congr' 1,
    ext i,
    simp only [finsupp.map_domain, finsupp.sum_apply, finsupp.single_apply],
    rw [finsupp.sum, finset.sum_eq_single (e.symm i)],
    { simp only [equiv.finsupp, equiv.subtype_congr, if_true, equiv.coe_fn_symm_mk,
        eq_self_iff_true, equiv.apply_symm_apply, subtype.coe_mk, finsupp.sum_apply],
      simp only [finsupp.sum_eq_sum_univ, eq_self_iff_true,
        finsupp.single_zero, finsupp.zero_apply, forall_true_iff],
      rw finset.sum_eq_single i,
      { apply finsupp.single_eq_same },
      { intros j hju hj, apply finsupp.single_eq_of_ne,
        simp only [hj, equiv.apply_eq_iff_eq, ne.def, not_false_iff], },
      { intro h, exfalso, exact h (finset.mem_univ _) } },
    { rintro j h hj, rw if_neg, rintro rfl, simpa using hj },
    { simp only [finsupp.not_mem_support_iff, imp_self, if_true,
        eq_self_iff_true, equiv.apply_symm_apply], } },
  { apply signature.ext, rcases d with ⟨d, rfl⟩,
    rwa [coeffs_to_signature_map_domain_of_equiv], },
  { apply signature.ext, rcases d with ⟨d, rfl⟩,
    rw [coeffs_to_signature_map_domain_of_equiv], exact h.symm },
  { rintro ⟨d, rfl⟩,
    rw subtype.ext,
    show finsupp.map_domain e.symm (finsupp.map_domain e d) = d,
    rw ← finsupp.map_domain_comp,
    simp only [finsupp.map_domain_id, equiv.symm_comp_self], },
  { rintro ⟨d, rfl⟩,
    rw subtype.ext,
    show finsupp.map_domain e (finsupp.map_domain e.symm d) = d,
    rw ← finsupp.map_domain_comp,
    simp only [finsupp.map_domain_id, equiv.self_comp_symm], }
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
open monomial_symmetric fintype
variables [fintype σ] [comm_semiring R]

-- are these even true??
@[simp] lemma list.nth_le_cons_cast_succ {α : Type*} (a : α) (l : list α) (i : fin l.length) :
  (a :: l : list α).nth_le i.cast_succ i.cast_succ.2 = l.nth_le i i.2 :=
sorry

@[simp] lemma list.nth_le_cons_length {α : Type*} (a : α) (l : list α) (h):
  (a :: l : list α).nth_le l.length h = a :=
sorry

-- move this
lemma ugly {σ : Type*} (l : list σ) :
  multiset.map (λ (i : fin l.length), l.nth_le i i.2) finset.univ.val = (l : multiset σ) :=
begin
  induction l with a l ih,
  { refl },
  { have h₁ : (finset.image fin.cast_succ (@finset.univ (fin l.length) _)).1 =
        (@finset.univ (fin l.length) _).1.map fin.cast_succ,
      from finset.image_val_of_inj_on (by simp),
    have h₂ : fin.last l.length ∉ finset.image fin.cast_succ finset.univ,
    { rw [finset.mem_image], simp [fin.cast_succ_ne_last] },
    rw [fin.univ_cast_succ, finset.insert_val, multiset.ndinsert_of_not_mem h₂,
      multiset.map_cons, h₁, multiset.map_map],
    simp [function.comp, list.nth_le_cons_cast_succ, ih] }
end

lemma to_signature_surjective : function.surjective (@to_signature σ _) :=
begin
  intro l,
  obtain ⟨e⟩ := fintype.equiv_fin σ,
  let f : fin (card σ) → fin l.coeffs.length := fin.cast l.length.symm,
  let g : fin l.coeffs.length → ℕ := λ i, l.coeffs.nth_le i i.2,
  let d : σ →₀ ℕ := finsupp.equiv_fun_on_fintype.symm (g ∘ f ∘ e),
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
    { intros x y H, rwa fin.ext_iff at H ⊢, },
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
    { rw [fin.ext_iff, equiv.apply_symm_apply], refl }, },
  rw this,
  dsimp [g],
  clear_except,
  apply ugly
end

def to_signature_section : signature (card σ) → (σ →₀ ℕ) :=
classical.some (classical.axiom_of_choice (to_signature_surjective))

lemma to_signature_to_signature_section (l : signature (card σ)) :
  to_signature (to_signature_section l) = l :=
classical.some_spec (classical.axiom_of_choice (to_signature_surjective)) l

def signature_coefficient (φ : mv_polynomial σ R) (l : signature (card σ)) : R :=
coeff (to_signature_section l) φ

lemma is_symmetric.coeff_eq_coeff
  {φ : mv_polynomial σ R} (h : is_symmetric φ)
  (d₁ d₂ : σ →₀ ℕ) (hd : to_signature d₁ = to_signature d₂) :
  coeff d₁ φ = coeff d₂ φ :=
begin
  sorry
end

lemma is_symmetric.coeff_to_signature_section
  {φ : mv_polynomial σ R} (h : is_symmetric φ) (d : σ →₀ ℕ) :
  coeff d φ = coeff (to_signature_section (to_signature d)) φ :=
by { apply h.coeff_eq_coeff, rw to_signature_to_signature_section }

lemma sum_signature_coefficient_mul_monomial_symmetric (φ : mv_polynomial σ R) (h : φ.is_symmetric) :
  ∑ l in finset.image (to_signature) φ.support,
    C (signature_coefficient φ l) * monomial_symmetric σ R l = φ :=
begin
  -- show ∑ l : {l : signature (card σ) // l ∈ finset.image (to_signature) φ.support}, _ = _,
  rw φ.as_sum,
  rw finset.sum_subtype (λ _, iff.rfl),
  swap, { apply_instance },
  sorry
  -- have := finset.sum_fiberwise φ.support _ (λ d, monomial d (coeff d φ)),
end

variables (R)

lemma induction_step (l : signature (card σ)) :


def monomial_symmetric_as_polynomial_elementary_symmetric :
  Π (l : signature (card σ)), mv_polynomial ℕ R
| l := _
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨_, signature.lt_wf (card σ)⟩],
  dec_tac := tactic.assumption }

end

section
open fintype monomial_symmetric
variables [fintype σ] [comm_ring R]

lemma aeval_monomial_symmetric_as_polynomial_elementary_symmetric (l : signature (card σ)) :
  aeval _ _ (elementary_symmetric σ R) (monomial_symmetric_as_polynomial_elementary_symmetric R l) =
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
