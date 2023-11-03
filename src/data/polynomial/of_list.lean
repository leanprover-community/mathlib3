/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.list.of_fn
import data.list.rdrop
import data.list.to_finsupp
import data.polynomial.degree

/-!

# Lists as polynomials

Constructing polynomials by providing an explicit list of coefficients.

## Main definitions

- `of_list l`: a `l : list R` defines a `polynomial R` by setting the coefficients, from least to
  greatest
- `to_list p`: a `p : polynomial R` defines a `list R` as its coefficients, from least to greatest,
  up to and including its `p.nat_degree`
- `embed_list`: all lists that do not terminate in a `0 : R` can be embedded into `polynomial R`
  via `of_list`

## Main theorems

- `of_list_to_list`: constructing a polynomial from a polynomial's coefficients is the identity
- `to_list_of_list`: lists that do not terminate in a `0 : R` can be reconstructed from the
  polynomials they induce
- `surjective_of_list`: every `p : polynomial R` has at least one `list R` such that
  the list can form the polynomial, and the list's length is the `p.nat_degree - 1`.

-/

namespace list

variables {α : Type*}

lemma nthd_of_fn (d : α) {n : ℕ} (f : fin n → α) (i : ℕ) :
  nthd d (of_fn f) i = if hi : i < n then f ⟨i, hi⟩ else d :=
begin
  split_ifs,
  { rw [nthd_eq_nth_le, nth_le_of_fn'],
    simpa using h },
  { rw [nthd_eq_default],
    simpa using h }
end

end list
namespace polynomial

variables {R S : Type*} [semiring R] (l : list R)

section

variables [decidable_pred (λ (i : ℕ), list.nthd 0 l i ≠ 0)]

/-- A `l : list R` over a `semiring R` defines a polynomial with the elements as coefficients.
A generalization of `polynomial.of_list_lt`. -/
def of_list : polynomial R :=
of_finsupp l.to_finsupp

@[simp] lemma coeff_of_list : (of_list l).coeff = l.nthd 0 := rfl

@[simp] lemma of_list_nil [decidable_pred (λ (i : ℕ), list.nthd 0 ([] : list R) i ≠ 0)] :
  of_list ([] : list R) = 0 := rfl

@[simp] lemma of_list_cons (x : R) (xs : list R)
  [decidable_pred (λ (i : ℕ), list.nthd 0 (x :: xs) i ≠ 0)]
  [decidable_pred (λ (i : ℕ), list.nthd 0 xs i ≠ 0)] :
  of_list (x :: xs) = C x + X * of_list xs :=
by { ext (_|i); simp [coeff_C] }

@[simp] lemma of_list_concat (x : R) (xs : list R)
  [decidable_pred (λ (i : ℕ), list.nthd 0 (xs ++ [x]) i ≠ 0)]
  [decidable_pred (λ (i : ℕ), list.nthd 0 xs i ≠ 0)] :
  of_list (xs ++ [x]) = of_list xs + monomial xs.length x :=
begin
  unfreezingI { induction xs with y xs IH generalizing x },
  { classical,
    rw add_comm,
    convert of_list_cons x [] using 2,
    simp },
  { simp [IH, mul_add, add_assoc] }
end

@[simp] lemma of_list_append (xs ys : list R)
  [decidable_pred (λ (i : ℕ), list.nthd 0 (xs ++ ys) i ≠ 0)]
  [decidable_pred (λ (i : ℕ), list.nthd 0 xs i ≠ 0)]
  [decidable_pred (λ (i : ℕ), list.nthd 0 ys i ≠ 0)] :
  of_list (xs ++ ys) = of_list xs + X ^ xs.length * of_list ys :=
begin
  unfreezingI { induction ys using list.reverse_rec_on with ys y IH generalizing xs },
  { simp },
  { classical,
    simp [←list.append_assoc, IH, add_assoc, mul_add, add_comm] }
end

-- decidable_eq here is too powerful, we don't have a pfilter
@[simp] lemma support_of_list {R} [semiring R] [decidable_eq R] (l : list R) :
  (of_list l).support =
  (l.enum.to_finset.filter (λ (p : ℕ × R), p.2 ≠ 0)).image prod.fst :=
begin
  ext i,
  simp only [list.mem_iff_nth_le, mem_support_iff, coeff_of_list, ne.def, finset.mem_image,
             finset.mem_filter, list.mem_to_finset, exists_prop, prod.exists,
             exists_and_distrib_right, exists_eq_right],
  split,
  { intro h,
    have hi : i < l.length,
    { contrapose! h,
      exact list.nthd_eq_default _ _ h },
    refine ⟨l.nth_le i hi, ⟨⟨i, _, _⟩, _⟩⟩,
    { simpa [list.length_enum] using hi },
    { exact list.nth_le_enum _ _ _ },
    { rwa ←list.nthd_eq_nth_le _ 0 hi } },
  { rintro ⟨x, ⟨⟨n, hn, h⟩, hx⟩⟩,
    rw [list.nth_le_enum, prod.mk.inj_iff] at h,
    rcases h with ⟨rfl, h⟩,
    rw [list.length_enum] at hn,
    rwa [list.nthd_eq_nth_le _ 0 hn, h] }
end

lemma of_list_eq_sum_map_monomial_enum :
  of_list l = ((l.enum).map (λ (p : ℕ × R), monomial p.1 p.2)).sum :=
begin
  unfreezingI { induction l using list.reverse_rec_on with xs x IH },
  { simp },
  { classical,
    simp [list.enum_append, list.enum_from_cons, IH, monomial_eq_C_mul_X] }
end

lemma of_list_eq_zero_iff {l : list R}
  [decidable_pred (λ (i : ℕ), list.nthd 0 l i ≠ 0)] :
  of_list l = 0 ↔ ∀ (x : R), x ∈ l → x = 0 :=
begin
  simp_rw [list.mem_iff_nth_le],
  split,
  { simp [←l.nthd_eq_nth_le 0, ←coeff_of_list] {contextual := tt} },
  { intro h,
    ext n,
    cases le_or_lt l.length n with hn hn,
    { simp [l.nthd_eq_default _ hn] },
    { rw [coeff_of_list, l.nthd_eq_nth_le _ hn, coeff_zero, h (l.nth_le n hn)],
      exact ⟨_, _, rfl⟩ } }
end

lemma nat_degree_of_list_le : nat_degree (of_list l) ≤ l.length :=
begin
  unfreezingI { induction l using list.reverse_rec_on with xs x IH },
  { simp, },
  classical,
  simp only [of_list_append, of_list_cons, of_list_nil, mul_zero, add_zero, X_pow_mul_C,
             list.length_append, list.length_singleton],
  refine (nat_degree_add_le _ _).trans _,
  rw [max_le_iff],
  exact ⟨nat.le_succ_of_le IH, nat.le_succ_of_le (nat_degree_C_mul_X_pow_le _ _)⟩
end

lemma nat_degree_of_list_lt (h : l ≠ []) : nat_degree (of_list l) < l.length :=
begin
  unfreezingI { induction l using list.reverse_rec_on with xs x IH },
  { exact absurd rfl h, },
  classical,
  simp only [of_list_append, of_list_cons, of_list_nil, mul_zero, add_zero, X_pow_mul_C,
             list.length_append, list.length_singleton],
  refine (nat_degree_add_le _ _).trans_lt _,
  rw [max_lt_iff],
  refine ⟨_, nat.lt_succ_of_le (nat_degree_C_mul_X_pow_le _ _)⟩,
  unfreezingI { cases xs },
  { simp },
  { exact nat.lt_succ_of_lt (IH (list.cons_ne_nil _ _)) }
end

lemma degree_of_list_lt : degree (of_list l) < l.length :=
begin
  by_cases h : of_list l = 0,
  { simpa [h] using with_bot.bot_lt_coe _ },
  { rw ←nat_degree_lt_iff_degree_lt h,
    refine nat_degree_of_list_lt _ _,
    contrapose! h,
    simp [of_list_eq_zero_iff, h] }
end

lemma nat_degree_of_list_of_last_ne_zero (h : ∀ (hl : l ≠ []), l.last hl ≠ 0) :
  nat_degree (of_list l) = l.length - 1 :=
begin
  unfreezingI { induction l using list.reverse_rec_on with xs x IH },
  { simp },
  classical,
  specialize h _,
  { rw ←list.concat_eq_append,
    exact list.concat_ne_nil _ _ },
  unfreezingI { cases xs },
  { simp },
  have hx : x ≠ 0,
  { simpa using h },
  simp only [of_list_append, of_list_cons x, of_list_nil, mul_zero, add_zero, X_pow_mul_C,
             list.length_append, list.length_singleton, nat.add_succ_sub_one],
  rw [nat_degree_add_eq_right_of_nat_degree_lt];
  rw [nat_degree_C_mul_X_pow _ _ hx],
  exact nat_degree_of_list_lt _ (list.cons_ne_nil _ _)
end

lemma nat_degree_of_list_of_nthd_length_sub_one_ne_zero (h : l.nthd 0 (l.length - 1) ≠ 0) :
  nat_degree (of_list l) = l.length - 1 :=
begin
  refine nat_degree_of_list_of_last_ne_zero _ _,
  intro hl,
  rwa [list.last_eq_nth_le, ←list.nthd_eq_nth_le _ (0 : R)]
end

lemma of_list_inj_on (l' : list R) [decidable_pred (λ (i : ℕ), list.nthd 0 l' i ≠ 0)]
  (hl : l.nthd 0 (l.length - 1) ≠ 0) (hl' : l'.nthd 0 (l'.length - 1) ≠ 0)
  (h : of_list l = of_list l') :
  l = l' :=
begin
  refine list.ext_le _ _,
  { unfreezingI { cases l with hd tl },
    { simpa using hl },
    unfreezingI { cases l' with hd' tl' },
    { simpa using hl' },
    suffices : (hd :: tl).length - 1 = (hd' :: tl').length - 1,
    { refine nat.pred_inj _ _ this;
      simp },
    rw [←nat_degree_of_list_of_last_ne_zero, ←nat_degree_of_list_of_last_ne_zero, h],
    { intro,
      rwa [list.last_eq_nth_le, ←list.nthd_eq_nth_le (hd' :: tl') 0] },
    { intro,
      rwa [list.last_eq_nth_le, ←list.nthd_eq_nth_le (hd :: tl) 0] } },
  { intros n hn hn',
    rw [←list.nthd_eq_nth_le l 0, ←list.nthd_eq_nth_le l' 0, ←coeff_of_list, ←coeff_of_list, h] }
end

end

/-- Auxiliary construction of lists that do not have `0` as the last element, which are arguments
to `polynomial.embed_list`. -/
def _root_.list.drop_terminal_zeros [decidable_pred (λ (x : R), x = 0)] (l : list R) :
  {l : list R // l = [] ∨ l.nthd 0 (l.length - 1) ≠ 0} :=
⟨l.rdrop_while (= 0), begin
  induction l using list.reverse_rec_on with xs x IH,
  { simp },
  { simp only [list.rdrop_while_concat],
    split_ifs,
    { simp [-list.rdrop_while_eq_nil_iff, IH] },
    { rw [list.nthd_eq_nth_le, list.nth_le_append_right];
      simp [h] } }
end⟩

/-- The list of coefficients of `p : polynomial R`, from least to greatest power.
The zero polynomial produces `[]`.  -/
def to_list (p : polynomial R) : list R := list.of_fn (λ (i : fin (p.nat_degree + 1)), p.coeff i)

@[simp] lemma to_list_zero : to_list (0 : polynomial R) = [0] := rfl
@[simp] lemma length_to_list (p : polynomial R) : (to_list p).length = p.nat_degree + 1 :=
list.length_of_fn _
lemma to_list_ne_nil (p : polynomial R) : to_list p ≠ [] :=
list.ne_nil_of_length_eq_succ (length_to_list _)
lemma nthd_to_list (p : polynomial R) (d : R) (n : ℕ) :
  (to_list p).nthd d n = if n ≤ p.nat_degree then p.coeff n else d :=
begin
  simp only [to_list, list.of_fn_succ, fin.coe_zero, fin.coe_succ],
  cases n,
  { simp },
  split_ifs with hn hn,
  { rw [list.nthd_cons_succ, list.nthd_eq_nth_le];
    simp [nat.lt_of_succ_le hn] },
  { rw [list.nthd_cons_succ, list.nthd_eq_default],
    simpa [nat.lt_succ_iff] using hn }
end
@[simp] lemma last_to_list (p : polynomial R) (hp : to_list p ≠ [] := to_list_ne_nil p) :
  list.last (to_list p) hp = p.leading_coeff :=
begin
  rw [list.last_eq_nth_le, ←list.nthd_eq_nth_le _ (0 : R), nthd_to_list],
  simp
end

variables [decidable_pred (λ (x : R), x ≠ 0)]

/-- `of_list` is the left inverse to `to_list`. -/
lemma of_list_to_list (p : polynomial R) : of_list (to_list p) = p :=
begin
  ext,
  simp [nthd_to_list, coeff_eq_zero_of_nat_degree_lt] {contextual := tt}
end

lemma left_inverse_of_list_to_list : function.left_inverse (λ (l : list R), of_list l) (to_list) :=
of_list_to_list

/-- `to_list` is the partial left inverse to `of_list`. -/
lemma to_list_of_list (l : list R) (hl : l.nthd 0 (l.length - 1) ≠ 0) : to_list (of_list l) = l :=
begin
  refine of_list_inj_on _ _ _ hl (of_list_to_list _),
  have : 1 ≤ l.length,
  { cases l,
    { simpa using hl },
    { simp } },
  rw nthd_to_list,
  simp [nat_degree_of_list_of_nthd_length_sub_one_ne_zero _ hl, hl, tsub_add_cancel_of_le this]
end

lemma surjective_of_list (p : polynomial R) :
  ∃ (l : list R), p = of_list l ∧ p.nat_degree = l.length - 1 :=
⟨to_list p, (of_list_to_list _).symm, by simp⟩

/-- The lists over `semiring R` that do not have `0` as the last element embed into `R[X]`. -/
def embed_list : {l : list R // l = [] ∨ l.nthd 0 (l.length - 1) ≠ 0} ↪ polynomial R :=
{ to_fun := λ l, of_list l,
  inj' := begin
    rintro ⟨l, rfl|hl⟩ ⟨l', rfl|hl'⟩ h;
    simp only at *,
    { by_cases H : l' = [],
      { exact H.symm },
      simp only [of_list_eq_zero_iff, @eq_comm _ _ (of_list _), subtype.coe_mk, of_list_nil] at h,
      rw [list.nthd_eq_nth_le, ←list.last_eq_nth_le _ H] at hl',
      { exact absurd (h _ (list.last_mem _)) hl' } },
    { by_cases H : l = [],
      { exact H },
      simp only [of_list_eq_zero_iff, @eq_comm _ _ (of_list _), subtype.coe_mk, of_list_nil] at h,
      rw [list.nthd_eq_nth_le, ←list.last_eq_nth_le _ H] at hl,
      { exact absurd (h _ (list.last_mem _)) hl } },
    { exact of_list_inj_on _ _ hl hl' h }
    end }

end polynomial
