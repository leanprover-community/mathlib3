import algebra.algebra.subalgebra
import ring_theory.polynomial.symmetric
import data.mv_polynomial.basic
import analysis.lindemann.test2

open equiv fintype function
open_locale big_operators classical
noncomputable theory

universes u

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

section list

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

lemma get_eq_nth_le : ∀ (l : list ℕ) (n : ℕ) (h : n < l.length),
  list.func.get n l = list.nth_le l n h
| []       n     h := by { simp only [nat.not_lt_zero, list.length] at h, exfalso, exact h }
| (a :: l) 0     h := by { simp }
| (a :: l) (n+1) h :=
begin
  simp only [list.nth_le, list.func.get],
  simp only [list.length, add_lt_add_iff_right] at h,
  exact get_eq_nth_le l n h,
end

end list

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


lemma map_sum {α : Type*} {β : Type*} {ι : Type*}
  (s : finset ι) (f : α → β) (s : ι → multiset α) : 0 = 0 :=
begin

  sorry
end

end multiset

namespace mv_polynomial

section definitions
variables (σ : Type*) (R : Type*) [comm_ring R]

def symm_polynomial : subalgebra R (mv_polynomial σ R) :=
{ carrier := {φ | is_symmetric φ},
  one_mem' := by simp only [is_symmetric.one, set.mem_set_of_eq],
  mul_mem' := λ φ ψ hφ hψ, by { simp only [set.mem_set_of_eq, is_symmetric.mul hφ hψ] at * },
  zero_mem' := by simp,
  add_mem' := λ φ ψ hφ hψ, by { simp only [set.mem_set_of_eq, is_symmetric.add hφ hψ] at * },
  algebra_map_mem' := λ r, by simp [algebra_map_eq] }

instance : algebra R (symm_polynomial σ R) := by tactic.apply_instance

def f [fintype σ] : mv_polynomial (fin (card σ)) R →ₐ[R] mv_polynomial σ R :=
aeval (λ i, esymm σ R i)

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
ext $ list.eq_of_perm_of_sorted h l₁.sorted l₂.sorted

lemma ext_iff {l₁ l₂ : signature n} : l₁ = l₂ ↔ l₁.coeffs = l₂.coeffs :=
⟨congr_arg _, ext⟩

lemma ext_iff' {l₁ l₂ : signature n} : l₁ = l₂ ↔ l₁.coeffs ~ l₂.coeffs :=
⟨by { rintro rfl, refl }, ext'⟩

instance (n : ℕ) : linear_order (signature n) :=
linear_order.lift signature.coeffs coeffs_injective

instance : unique (signature 0) :=
{ default := ⟨[], list.sorted_nil, rfl⟩,
  uniq    := by { intro l, ext1, rw list.eq_nil_of_length_eq_zero l.length, } }

#reduce list.nth_le [0, 1] 0 _

def add : signature n → signature n → signature n :=
λ l₁ l₂, {
  coeffs := list.func.add l₁.coeffs l₂.coeffs,
  sorted :=
  begin
    unfold list.sorted,
    rw list.pairwise_iff_nth_le,
    intros,
    have hl : (list.func.add l₁.coeffs l₂.coeffs).length = n, sorry,
    rw hl at h₁,
    rw [← get_eq_nth_le, ← get_eq_nth_le, list.func.get_add, list.func.get_add],
    apply add_le_add,
    { rw [get_eq_nth_le l₁.coeffs j (l₁.length.symm ▸ h₁),
        get_eq_nth_le l₁.coeffs i (h₂.trans (l₁.length.symm ▸ h₁))],
      exact (list.pairwise_iff_nth_le.mp l₁.sorted i j (l₁.length.symm ▸ h₁) h₂).le, },
    rw [get_eq_nth_le l₂.coeffs j (l₂.length.symm ▸ h₁),
        get_eq_nth_le l₂.coeffs i (h₂.trans (l₂.length.symm ▸ h₁))],
    exact (list.pairwise_iff_nth_le.mp l₂.sorted i j (l₂.length.symm ▸ h₁) h₂).le,
  end,
  length := by { rw list.func.length_add, rw l₁.length, rw l₂.length, exact max_self n } }

instance : has_add (signature n) := ⟨add⟩

@[simp] lemma coeffs_add (l₁ l₂ : signature n) : (l₁ + l₂).coeffs = list.func.add l₁.coeffs l₂.coeffs := rfl

@[simp] lemma length_add_left (l₁ l₂ : signature n) : (l₁ + l₂).coeffs.length = l₁.coeffs.length :=
by { rw [coeffs_add, list.func.length_add, l₁.length, l₂.length], exact max_self n }

@[simp] lemma length_add_right (l₁ l₂ : signature n) : (l₁ + l₂).coeffs.length = l₂.coeffs.length :=
by { rw [coeffs_add, list.func.length_add, l₁.length, l₂.length], exact max_self n }

lemma add_assoc : ∀ (l₁ l₂ l₃ : signature n), l₁ + l₂ + l₃ = l₁ + (l₂ + l₃) :=
λ l₁ l₂ l₃,
begin
  rw ext_iff,
  apply list.ext_le,
  simp only [l₁.length, l₂.length, l₃.length, max_eq_right, list.func.length_add, coeffs_add],
  intros n ha hb,
  simp [← get_eq_nth_le, list.func.get_add, add_assoc],
end

lemma add_comm : ∀ (l₁ l₂ : signature n), l₁ + l₂ = l₂ + l₁ :=
λ l₁ l₂,
begin
  rw ext_iff,
  apply list.ext_le,
  simp only [l₁.length, l₂.length, max_eq_right, list.func.length_add, coeffs_add],
  intros n ha hb,
  simp [← get_eq_nth_le, list.func.get_add, add_comm],
end

def zero : signature n :=
{ coeffs := list.repeat 0 n,
  sorted := by { simp [list.sorted_repeat] },
  length := by { simp, } }

instance : has_zero (signature n) := ⟨zero⟩

@[simp] lemma coeffs_zero : (0 : signature n).coeffs = list.repeat 0 n := rfl

@[simp] lemma length_zero : (0 : signature n).coeffs.length = n := (0 : signature n).length

@[simp] lemma get_zero {k : ℕ}: list.func.get k (0 : signature n).coeffs = 0 :=
by { rw coeffs_zero, sorry }

lemma add_zero : ∀ (l : signature n), l + 0 = l :=
λ l,
begin
  rw ext_iff,
  apply list.ext_le,
  simp only [l.length, max_eq_right, list.func.length_add, coeffs_add, length_zero],
  intros n ha hb,
  simp only [← get_eq_nth_le, list.func.get_add, add_right_eq_self, coeffs_add],
  exact get_zero,
end

lemma zero_add : ∀ (l : signature n), 0 + l = l := λ l, (add_comm l 0) ▸ add_zero l

instance : add_comm_monoid (signature n) :=
{ add := add,
  add_assoc := add_assoc,
  zero := zero,
  zero_add := zero_add,
  add_zero := add_zero,
  add_comm := add_comm }

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
  sorry
end

lemma list.nth_le_le_sum (L : list ℕ) {i : ℕ} {h : i < L.length}:
  L.nth_le i h ≤ L.sum :=
begin
  revert i, induction L, simp,
  intros, cases i, simp, transitivity L_tl.sum, apply L_ih, simp
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
  { rintros ⟨l,hl⟩ i hi,
    have h : l.coeffs.head < k,
    { calc l.coeffs.head ≤ l₀.coeffs.head : _
                     ... < k              : _,
      { rw lt_iff at hl, rw le_iff_eq_or_lt, tauto },
      { rw nat.lt_add_one_iff, apply list.head_le_sum } },
    cases n,
    { simp only [l.length, subtype.coe_mk, nat.not_lt_zero] at hi, exfalso, exact hi },
    cases i, rw list.nth_le_zero, apply h,
    have H := l.sorted,
    rw [list.sorted, list.pairwise_iff_nth_le] at H,
    apply lt_of_le_of_lt (H 0 _ _ _), rw list.nth_le_zero, apply h,
    apply nat.succ_pos },
  let f : {l : signature n // l < l₀} → (fin n → fin k) :=
  λ l i, ⟨(l : signature n).coeffs.nth_le i ((l : signature n).length.symm ▸ i.2), aux l _ _⟩,
  apply fintype.of_injective f,
  intros l₁ l₂ h,
  apply subtype.ext,
  rw [signature.ext_iff],
  apply list.ext_le,
  { rw [(l₁ : signature n).length, (l₂ : signature n).length] },
  { intros i hi₁ hi₂,
    rw [(l₁ : signature n).length] at hi₁,
    rw [function.funext_iff] at h,
    specialize h ⟨i, hi₁⟩,
    rwa [fin.ext_iff] at h }
end

lemma zero_le (l : signature n) : 0 ≤ l :=
begin
  apply le_of_forall_nth_le_le,
  intros i hi,
  simp only [coeffs_zero, list.nth_le_repeat, zero_le],
end

#reduce (list.repeat 0 4)

example (n k : ℕ) (h : k ≤ n) : k + (n - k) = n := nat.add_sub_of_le h

-- the list `[k] * n ++ [0] * m`, i.e. `n` `k`'s followed by `m` zeros
def step (n k : ℕ) (h : k ≤ n) : signature n :=
{ coeffs := list.repeat 1 k ++ list.repeat 0 (n - k),
  sorted :=
  begin
    induction k with k ih generalizing n, simp [list.sorted_repeat],
    simp,
    split,
    intros,
    cases H with h1 h2,
    exact (list.eq_of_mem_repeat h1).le,
    rw list.eq_of_mem_repeat h2,
    simp only [nat.zero_le],
    have : k.succ ≤ n ↔ k ≤ n - 1, sorry,
    specialize ih (n - 1) (this.mp h),
    convert ih using 3,
    omega,
  end,
  length := by simp [nat.add_sub_of_le h] }

def single : Π (n k : ℕ), signature n
| 0     _ := ⟨[], list.sorted_nil, rfl⟩
| (n + 1) k :=
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
    rw [list.sum_cons, list.sum_repeat, nsmul_zero, nat.add_zero] }
end

end signature

end definitions

section main

variables {σ : Type*} [fintype σ] {R : Type*} [comm_ring R]

@[simp] lemma X_apply_f (i : fin (card σ)) : f σ R (X i) = esymm σ R i :=
by simp [f, aeval_X]

lemma is_symmetric_apply_f_coeff (d : fin (card σ) →₀ ℕ) (r : R) :
  is_symmetric (f σ R (monomial d r)) :=
begin
  rw f,
  rw aeval_monomial,
  simp only [one_mul, ring_hom.map_one, finsupp.prod_pow],
  intro e,
  rw alg_hom.map_mul,
  rw alg_hom.map_prod,
  simp [alg_hom.map_pow, rename_esymm],
end

lemma is_symmetric_apply_f (φ : mv_polynomial (fin (card σ)) R) : is_symmetric (f σ R φ) :=
begin
  rw f,
  rw as_sum φ,
  rw alg_hom.map_sum,
  intro e,
  rw alg_hom.map_sum,
  refine finset.sum_congr rfl (λ d hd, _),
  have := is_symmetric_apply_f_coeff d (coeff d φ) e,
  rwa ← f,
end

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
  multiset.count 0 ((to_signature d).coeffs : multiset ℕ) = fintype.card σ - d.support.card :=
begin
  classical,
  rw [multiset.count, coeffs_to_signature, multiset.sort_eq, multiset.countp_map],
  show finset.card (finset.filter _ _) = _,
  rw [← finset.card_univ, ← finset.card_sdiff (finset.subset_univ d.support)],
  congr' 1,
  ext,
  simp [eq_comm, finset.mem_filter, finset.mem_sdiff],
end

def psignature (φ : mv_polynomial σ R) : option (signature (card σ)) :=
finset.max (finset.image (λ d, to_signature d) φ.support)

def psignature' (φ : mv_polynomial σ R) (h : φ ≠ 0): signature (card σ) :=
finset.max' (finset.image to_signature φ.support)
begin
  rw finset.nonempty.image_iff, rcases (exists_coeff_ne_zero h) with ⟨d, hd⟩,
  rw ← mv_polynomial.mem_support_iff at hd,
  exact ⟨d, hd⟩,
end

lemma X_ne_zero [nontrivial R] (i : σ) : (X i : mv_polynomial σ R) ≠ 0 :=
begin
  rw X,
  rw ne_zero_iff,
  use finsupp.single i 1,
  simp only [if_true, eq_self_iff_true, coeff_monomial],
  exact one_ne_zero,
end

lemma nat.eq_zero_one_or_ge_two (n : ℕ) : n = 0 ∨ n = 1 ∨ 2 ≤ n :=
begin
  by_cases h0 : n = 0,
  left, exact h0,
  by_cases h1 : n = 1,
  right, left, exact h1,
  right, right, sorry
end

lemma psignature_X [nontrivial R] (i : σ) : psignature' (X i : mv_polynomial σ R) (X_ne_zero i) =
  signature.single (card σ) 1 :=
begin
  simp only [X, psignature', support_monomial, to_signature, signature.ext_iff,
    finset.image_singleton, if_false, one_ne_zero, finset.max'_singleton],

  have : 1 ::ₘ multiset.repeat 0 (card σ - 1) = multiset.map (finsupp.single i 1) finset.univ.val,
  { ext,
    rcases nat.eq_zero_one_or_ge_two a with h0 | h1 | h2,
    simp only [h0, multiset.count_cons_of_ne, multiset.count_repeat_self, ne.def,
      not_false_iff, zero_ne_one],
   },
  sorry
end

#check (to_signature ∘ (λ (t : finset σ), ∑ (i : σ) in t, finsupp.single i 1))
#check λ (t : finset σ), signature.step (card σ) t.card t.card_le_univ
#check λ t, multiset.map (∑ (i : σ) in t, finsupp.single i 1) finset.univ.val
lemma map_sum_single (t : finset σ) :
  (multiset.map (∑ (i : σ) in t, finsupp.single i 1) finset.univ.val : multiset ℕ) :=
begin

end

lemma monomial_psignature :
  (to_signature ∘ (λ (t : finset σ), ∑ (i : σ) in t, finsupp.single i 1)) =
  λ t, signature.step (card σ) t.card t.card_le_univ :=
begin
  funext,
  simp only [comp_app],
  rw to_signature,
  rw signature.ext_iff,
  simp only [option.mem_def],
  apply list.ext_le,
  rw multiset.length_sort,
  rw multiset.card_map,
  rw (signature.step (card σ) x.card _).length,
  rw fintype.card,
  convert (multiset.to_finset_card_of_nodup finset.univ.nodup).symm,
  exact finset.univ.val_to_finset.symm,
  intros,
  sorry
end

lemma esymm_psignature' [decidable_eq σ] [nontrivial R] (n : ℕ) (h : n ≤ card σ) :
  finset.image to_signature (esymm σ R n).support = {signature.step (card σ) n h} :=
begin
  ext,
  rw support_esymm n,
  rw finset.image_image,
  simp [monomial_psignature],
  { refine ⟨λ ha, _, λ ha, _⟩,
    rcases ha with ⟨t, ht, ha⟩,
    rw finset.mem_powerset_len at ht,
    simp_rw ht.2 at ha,
    exact ha.symm,
    sorry,
     },
  apply_instance,
  apply_instance,
end

lemma esymm_psignature [nontrivial R] (n : ℕ) (h : n ≤ card σ) :
  (esymm σ R n).psignature' (esymm_ne_zero n h) = signature.step (card σ) n h :=
begin
  rw psignature',
  simp [esymm_psignature' n h],
end

lemma psignature_mul_of_esymm [nontrivial R] (n m : ℕ) (hn : n ≤ card σ) (hm : m ≤ card σ) :
  (esymm σ R n * esymm σ R m).psignature' (by sorry) =
  (esymm σ R n).psignature' (esymm_ne_zero n hn) + (esymm σ R m).psignature' (esymm_ne_zero m hm) :=
begin
  sorry
end

lemma f_inj : injective (f σ R) :=
begin
  rw alg_hom.injective_iff,
  intros φ hφ,
  have := is_symmetric_apply_f φ,
  rw eq_zero_iff,
  rw eq_zero_iff at hφ,
  intro h,
  sorry
end

lemma fundemental_theorem' (l : signature (card σ)) (φ : mv_polynomial σ R)  (h : φ ≠ 0) :
  φ.psignature' h = l → is_symmetric φ → ∃ ψ, f σ R ψ = φ :=
begin
  revert h φ,
  refine well_founded.induction (signature.lt_wf (card σ)) l _,
  intros l' ih φ h hφl' hφ,
  sorry
end

theorem fundemental_theorem : mv_polynomial (fin (card σ)) R ≃ₐ[R] symm_polynomial σ R :=
sorry

end main

end mv_polynomial
