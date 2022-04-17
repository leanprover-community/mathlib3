/-
Copyright (c) 2020 Yury Kudryashov, Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anne Baanen
-/
import algebra.big_operators.basic
import data.fintype.fin
import data.fintype.card
/-!
# Big operators and `fin`

Some results about products and sums over the type `fin`.

The most important results are the induction formulas `fin.prod_univ_cast_succ`
and `fin.prod_univ_succ`, and the formula `fin.prod_const` for the product of a
constant function. These results have variants for sums instead of products.

-/

open_locale big_operators

open finset

variables {α : Type*} {β : Type*}

namespace finset

@[to_additive]
theorem prod_range [comm_monoid β] {n : ℕ} (f : ℕ → β) :
  ∏ i in finset.range n, f i = ∏ i : fin n, f i :=
begin
  fapply @finset.prod_bij' _ _ _ _ _ _,
  exact λ k w, ⟨k, (by simpa using w)⟩,
  swap 3,
  exact λ a m, a,
  swap 3,
  exact λ a m, by simpa using a.2,
  all_goals { tidy, },
end

end finset

namespace fin

@[to_additive]
theorem prod_univ_def [comm_monoid β] {n : ℕ} (f : fin n → β) :
  ∏ i, f i = ((list.fin_range n).map f).prod :=
by simp [univ_def, finset.fin_range]

@[to_additive]
theorem prod_of_fn [comm_monoid β] {n : ℕ} (f : fin n → β) :
  (list.of_fn f).prod = ∏ i, f i :=
by rw [list.of_fn_eq_map, prod_univ_def]

/-- A product of a function `f : fin 0 → β` is `1` because `fin 0` is empty -/
@[to_additive "A sum of a function `f : fin 0 → β` is `0` because `fin 0` is empty"]
theorem prod_univ_zero [comm_monoid β] (f : fin 0 → β) : ∏ i, f i = 1 := rfl

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f x`, for some `x : fin (n + 1)` times the remaining product -/
@[to_additive
/- A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the sum of `f x`, for some `x : fin (n + 1)` plus the remaining product -/]
theorem prod_univ_succ_above [comm_monoid β] {n : ℕ} (f : fin (n + 1) → β)
  (x : fin (n + 1)) :
  ∏ i, f i = f x * ∏ i : fin n, f (x.succ_above i) :=
begin
  rw [fintype.prod_eq_mul_prod_compl x, ← image_succ_above_univ, prod_image],
  exact λ _ _ _ _ h, x.succ_above.injective h
end

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f 0` plus the remaining product -/
@[to_additive
/- A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the sum of `f 0` plus the remaining product -/]
theorem prod_univ_succ [comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) :
  ∏ i, f i = f 0 * ∏ i : fin n, f i.succ :=
prod_univ_succ_above f 0

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f (fin.last n)` plus the remaining product -/
@[to_additive
/- A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the sum of `f (fin.last n)` plus the remaining sum -/]
theorem prod_univ_cast_succ [comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) :
  ∏ i, f i = (∏ i : fin n, f i.cast_succ) * f (last n) :=
by simpa [mul_comm] using prod_univ_succ_above f (last n)

@[to_additive sum_univ_one] theorem prod_univ_one [comm_monoid β] (f : fin 1 → β) :
  ∏ i, f i = f 0 :=
by simp

@[to_additive] theorem prod_univ_two [comm_monoid β] (f : fin 2 → β) :
  ∏ i, f i = f 0 * f 1 :=
by simp [prod_univ_succ]

lemma sum_pow_mul_eq_add_pow {n : ℕ} {R : Type*} [comm_semiring R] (a b : R) :
  ∑ s : finset (fin n), a ^ s.card * b ^ (n - s.card) = (a + b) ^ n :=
by simpa using fintype.sum_pow_mul_eq_add_pow (fin n) a b

lemma prod_const [comm_monoid α] (n : ℕ) (x : α) : ∏ i : fin n, x = x ^ n := by simp

lemma sum_const [add_comm_monoid α] (n : ℕ) (x : α) : ∑ i : fin n, x = n • x := by simp

@[to_additive]
lemma prod_filter_zero_lt {M : Type*} [comm_monoid M] {n : ℕ} {v : fin n.succ → M} :
  ∏ i in univ.filter (λ (i : fin n.succ), 0 < i), v i = ∏ (j : fin n), v j.succ :=
by rw [univ_filter_zero_lt, finset.prod_map, rel_embedding.coe_fn_to_embedding, coe_succ_embedding]

@[to_additive]
lemma prod_filter_succ_lt {M : Type*} [comm_monoid M] {n : ℕ} (j : fin n) (v : fin n.succ → M) :
  ∏ i in univ.filter (λ i, j.succ < i), v i =
    ∏ j in univ.filter (λ i, j < i), v j.succ :=
by rw [univ_filter_succ_lt, finset.prod_map, rel_embedding.coe_fn_to_embedding, coe_succ_embedding]

end fin

namespace list

@[to_additive]
lemma prod_take_of_fn [comm_monoid α] {n : ℕ} (f : fin n → α) (i : ℕ) :
  ((of_fn f).take i).prod = ∏ j in finset.univ.filter (λ (j : fin n), j.val < i), f j :=
begin
  have A : ∀ (j : fin n), ¬ ((j : ℕ) < 0) := λ j, not_lt_bot,
  induction i with i IH, { simp [A] },
  by_cases h : i < n,
  { have : i < length (of_fn f), by rwa [length_of_fn f],
    rw prod_take_succ _ _ this,
    have A : ((finset.univ : finset (fin n)).filter (λ j, j.val < i + 1))
      = ((finset.univ : finset (fin n)).filter (λ j, j.val < i)) ∪ {(⟨i, h⟩ : fin n)},
        by { ext j, simp [nat.lt_succ_iff_lt_or_eq, fin.ext_iff, - add_comm] },
    have B : _root_.disjoint (finset.filter (λ (j : fin n), j.val < i) finset.univ)
      (singleton (⟨i, h⟩ : fin n)), by simp,
    rw [A, finset.prod_union B, IH],
    simp },
  { have A : (of_fn f).take i = (of_fn f).take i.succ,
    { rw ← length_of_fn f at h,
      have : length (of_fn f) ≤ i := not_lt.mp h,
      rw [take_all_of_le this, take_all_of_le (le_trans this (nat.le_succ _))] },
    have B : ∀ (j : fin n), ((j : ℕ) < i.succ) = ((j : ℕ) < i),
    { assume j,
      have : (j : ℕ) < i := lt_of_lt_of_le j.2 (not_lt.mp h),
      simp [this, lt_trans this (nat.lt_succ_self _)] },
    simp [← A, B, IH] }
end

@[to_additive]
lemma prod_of_fn [comm_monoid α] {n : ℕ} {f : fin n → α} :
  (of_fn f).prod = ∏ i, f i :=
begin
  convert prod_take_of_fn f n,
  { rw [take_all_of_le (le_of_eq (length_of_fn f))] },
  { have : ∀ (j : fin n), (j : ℕ) < n := λ j, j.is_lt,
    simp [this] }
end

lemma alternating_sum_eq_finset_sum {G : Type*} [add_comm_group G] :
  ∀ (L : list G), alternating_sum L = ∑ i : fin L.length, (-1 : ℤ) ^ (i : ℕ) • L.nth_le i i.is_lt
| [] := by { rw [alternating_sum, finset.sum_eq_zero], rintro ⟨i, ⟨⟩⟩ }
| (g :: []) :=
begin
  show g = ∑ i : fin 1, (-1 : ℤ) ^ (i : ℕ) • [g].nth_le i i.2,
  rw [fin.sum_univ_succ], simp,
end
| (g :: h :: L) :=
calc g + -h + L.alternating_sum
    = g + -h + ∑ i : fin L.length, (-1 : ℤ) ^ (i : ℕ) • L.nth_le i i.2 :
      congr_arg _ (alternating_sum_eq_finset_sum _)
... = ∑ i : fin (L.length + 2), (-1 : ℤ) ^ (i : ℕ) • list.nth_le (g :: h :: L) i _ :
begin
  rw [fin.sum_univ_succ, fin.sum_univ_succ, add_assoc],
  unfold_coes,
  simp [nat.succ_eq_add_one, pow_add],
  refl,
end

@[to_additive]
lemma alternating_prod_eq_finset_prod {G : Type*} [comm_group G] :
  ∀ (L : list G), alternating_prod L = ∏ i : fin L.length, (L.nth_le i i.2) ^ ((-1 : ℤ) ^ (i : ℕ))
| [] := by { rw [alternating_prod, finset.prod_eq_one], rintro ⟨i, ⟨⟩⟩ }
| (g :: []) :=
begin
  show g = ∏ i : fin 1, [g].nth_le i i.2 ^ (-1 : ℤ) ^ (i : ℕ),
  rw [fin.prod_univ_succ], simp,
end
| (g :: h :: L) :=
calc g * h⁻¹ * L.alternating_prod
    = g * h⁻¹ * ∏ i : fin L.length, L.nth_le i i.2 ^ (-1 : ℤ) ^ (i : ℕ) :
      congr_arg _ (alternating_prod_eq_finset_prod _)
... = ∏ i : fin (L.length + 2), list.nth_le (g :: h :: L) i _ ^ (-1 : ℤ) ^ (i : ℕ) :
begin
  rw [fin.prod_univ_succ, fin.prod_univ_succ, mul_assoc],
  unfold_coes,
  simp [nat.succ_eq_add_one, pow_add],
  refl,
end

end list
