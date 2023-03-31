/-
Copyright (c) 2020 Yury Kudryashov, Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anne Baanen
-/
import data.fintype.big_operators
import data.fintype.fin
import data.list.fin_range
import logic.equiv.fin

/-!
# Big operators and `fin`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
prod_bij'
  (λ k w, ⟨k, mem_range.mp w⟩)
  (λ a ha, mem_univ _)
  (λ a ha, congr_arg _ (fin.coe_mk _).symm)
  (λ a m, a)
  (λ a m, mem_range.mpr a.prop)
  (λ a ha, fin.coe_mk _)
  (λ a ha, fin.eta _ _)

end finset

namespace fin

@[to_additive]
theorem prod_univ_def [comm_monoid β] {n : ℕ} (f : fin n → β) :
  ∏ i, f i = ((list.fin_range n).map f).prod :=
by simp [univ_def]

@[to_additive]
theorem prod_of_fn [comm_monoid β] {n : ℕ} (f : fin n → β) :
  (list.of_fn f).prod = ∏ i, f i :=
by rw [list.of_fn_eq_map, prod_univ_def]

/-- A product of a function `f : fin 0 → β` is `1` because `fin 0` is empty -/
@[to_additive "A sum of a function `f : fin 0 → β` is `0` because `fin 0` is empty"]
theorem prod_univ_zero [comm_monoid β] (f : fin 0 → β) : ∏ i, f i = 1 := rfl

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f x`, for some `x : fin (n + 1)` times the remaining product -/
@[to_additive "A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)` is the sum of `f x`,
for some `x : fin (n + 1)` plus the remaining product"]
theorem prod_univ_succ_above [comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) (x : fin (n + 1)) :
  ∏ i, f i = f x * ∏ i : fin n, f (x.succ_above i) :=
by rw [univ_succ_above, prod_cons, finset.prod_map, rel_embedding.coe_fn_to_embedding]

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f 0` plus the remaining product -/
@[to_additive "A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)` is the sum of `f 0`
plus the remaining product"]
theorem prod_univ_succ [comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) :
  ∏ i, f i = f 0 * ∏ i : fin n, f i.succ :=
prod_univ_succ_above f 0

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f (fin.last n)` plus the remaining product -/
@[to_additive "A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)` is the sum of
`f (fin.last n)` plus the remaining sum"]
theorem prod_univ_cast_succ [comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) :
  ∏ i, f i = (∏ i : fin n, f i.cast_succ) * f (last n) :=
by simpa [mul_comm] using prod_univ_succ_above f (last n)

@[to_additive] lemma prod_cons [comm_monoid β] {n : ℕ} (x : β) (f : fin n → β) :
  ∏ i : fin n.succ, (cons x f : fin n.succ → β) i = x * ∏ i : fin n, f i :=
by simp_rw [prod_univ_succ, cons_zero, cons_succ]

@[to_additive sum_univ_one] theorem prod_univ_one [comm_monoid β] (f : fin 1 → β) :
  ∏ i, f i = f 0 :=
by simp

@[simp, to_additive] theorem prod_univ_two [comm_monoid β] (f : fin 2 → β) :
  ∏ i, f i = f 0 * f 1 :=
by simp [prod_univ_succ]

@[to_additive] theorem prod_univ_three [comm_monoid β] (f : fin 3 → β) :
  ∏ i, f i = f 0 * f 1 * f 2 :=
by { rw [prod_univ_cast_succ, prod_univ_two], refl }

@[to_additive] theorem prod_univ_four [comm_monoid β] (f : fin 4 → β) :
  ∏ i, f i = f 0 * f 1 * f 2 * f 3 :=
by { rw [prod_univ_cast_succ, prod_univ_three], refl }

@[to_additive] theorem prod_univ_five [comm_monoid β] (f : fin 5 → β) :
  ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 :=
by { rw [prod_univ_cast_succ, prod_univ_four], refl }

@[to_additive] theorem prod_univ_six [comm_monoid β] (f : fin 6 → β) :
  ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 :=
by { rw [prod_univ_cast_succ, prod_univ_five], refl }

@[to_additive] theorem prod_univ_seven [comm_monoid β] (f : fin 7 → β) :
  ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 :=
by { rw [prod_univ_cast_succ, prod_univ_six], refl }

@[to_additive] theorem prod_univ_eight [comm_monoid β] (f : fin 8 → β) :
  ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 :=
by { rw [prod_univ_cast_succ, prod_univ_seven], refl }

lemma sum_pow_mul_eq_add_pow {n : ℕ} {R : Type*} [comm_semiring R] (a b : R) :
  ∑ s : finset (fin n), a ^ s.card * b ^ (n - s.card) = (a + b) ^ n :=
by simpa using fintype.sum_pow_mul_eq_add_pow (fin n) a b

lemma prod_const [comm_monoid α] (n : ℕ) (x : α) : ∏ i : fin n, x = x ^ n := by simp

lemma sum_const [add_comm_monoid α] (n : ℕ) (x : α) : ∑ i : fin n, x = n • x := by simp

@[to_additive] lemma prod_Ioi_zero {M : Type*} [comm_monoid M] {n : ℕ} {v : fin n.succ → M} :
  ∏ i in Ioi 0, v i = ∏ j : fin n, v j.succ :=
by rw [Ioi_zero_eq_map, finset.prod_map, rel_embedding.coe_fn_to_embedding, coe_succ_embedding]

@[to_additive]
lemma prod_Ioi_succ {M : Type*} [comm_monoid M] {n : ℕ} (i : fin n) (v : fin n.succ → M) :
  ∏ j in Ioi i.succ, v j = ∏ j in Ioi i, v j.succ :=
by rw [Ioi_succ, finset.prod_map, rel_embedding.coe_fn_to_embedding, coe_succ_embedding]

@[to_additive]
lemma prod_congr' {M : Type*} [comm_monoid M] {a b : ℕ} (f : fin b → M) (h : a = b) :
  ∏ (i : fin a), f (cast h i) = ∏ (i : fin b), f i :=
by { subst h, congr, ext, congr, ext, rw coe_cast, }

@[to_additive]
lemma prod_univ_add {M : Type*} [comm_monoid M] {a b : ℕ} (f : fin (a+b) → M) :
  ∏ (i : fin (a+b)), f i =
  (∏ (i : fin a), f (cast_add b i)) * ∏ (i : fin b), f (nat_add a i) :=
begin
  rw fintype.prod_equiv fin_sum_fin_equiv.symm f (λ i, f (fin_sum_fin_equiv.to_fun i)), swap,
  { intro x,
    simp only [equiv.to_fun_as_coe, equiv.apply_symm_apply], },
  apply fintype.prod_sum_type,
end

@[to_additive]
lemma prod_trunc {M : Type*} [comm_monoid M] {a b : ℕ} (f : fin (a+b) → M)
  (hf : ∀ (j : fin b), f (nat_add a j) = 1) :
  ∏ (i : fin (a+b)), f i =
  ∏ (i : fin a), f (cast_le (nat.le.intro rfl) i) :=
by simpa only [prod_univ_add, fintype.prod_eq_one _ hf, mul_one]

section partial_prod

variables [monoid α] {n : ℕ}

/-- For `f = (a₁, ..., aₙ)` in `αⁿ`, `partial_prod f` is `(1, a₁, a₁a₂, ..., a₁...aₙ)` in `αⁿ⁺¹`. -/
@[to_additive "For `f = (a₁, ..., aₙ)` in `αⁿ`, `partial_sum f` is
`(0, a₁, a₁ + a₂, ..., a₁ + ... + aₙ)` in `αⁿ⁺¹`."]
def partial_prod (f : fin n → α) (i : fin (n + 1)) : α :=
((list.of_fn f).take i).prod

@[simp, to_additive] lemma partial_prod_zero (f : fin n → α) :
  partial_prod f 0 = 1 :=
by simp [partial_prod]

@[to_additive] lemma partial_prod_succ (f : fin n → α) (j : fin n) :
  partial_prod f j.succ = partial_prod f j.cast_succ * (f j) :=
by simp [partial_prod, list.take_succ, list.of_fn_nth_val, dif_pos j.is_lt, ←option.coe_def]

@[to_additive] lemma partial_prod_succ' (f : fin (n + 1) → α) (j : fin (n + 1)) :
  partial_prod f j.succ = f 0 * partial_prod (fin.tail f) j :=
by simpa [partial_prod]

@[to_additive] lemma partial_prod_left_inv {G : Type*} [group G] (f : fin (n + 1) → G) :
  f 0 • partial_prod (λ i : fin n, (f i)⁻¹ * f i.succ) = f :=
funext $ λ x, fin.induction_on x (by simp) (λ x hx,
begin
  simp only [coe_eq_cast_succ, pi.smul_apply, smul_eq_mul] at hx ⊢,
  rw [partial_prod_succ, ←mul_assoc, hx, mul_inv_cancel_left],
end)

@[to_additive] lemma partial_prod_right_inv {G : Type*} [group G]
  (g : G) (f : fin n → G) (i : fin n) :
  ((g • partial_prod f) i)⁻¹ * (g • partial_prod f) i.succ = f i :=
begin
  cases i with i hn,
  induction i with i hi generalizing hn,
  { simp [←fin.succ_mk, partial_prod_succ] },
  { specialize hi (lt_trans (nat.lt_succ_self i) hn),
    simp only [mul_inv_rev, fin.coe_eq_cast_succ, fin.succ_mk, fin.cast_succ_mk,
      smul_eq_mul, pi.smul_apply] at hi ⊢,
    rw [←fin.succ_mk _ _ (lt_trans (nat.lt_succ_self _) hn), ←fin.succ_mk],
    simp only [partial_prod_succ, mul_inv_rev, fin.cast_succ_mk],
    assoc_rw [hi, inv_mul_cancel_left] }
end

end partial_prod

end fin

namespace list

section comm_monoid

variables [comm_monoid α]

@[to_additive]
lemma prod_take_of_fn {n : ℕ} (f : fin n → α) (i : ℕ) :
  ((of_fn f).take i).prod = ∏ j in finset.univ.filter (λ (j : fin n), j.val < i), f j :=
begin
  have A : ∀ (j : fin n), ¬ ((j : ℕ) < 0) := λ j, not_lt_bot,
  induction i with i IH, { simp [A] },
  by_cases h : i < n,
  { have : i < length (of_fn f), by rwa [length_of_fn f],
    rw prod_take_succ _ _ this,
    have A : ((finset.univ : finset (fin n)).filter (λ j, j.val < i + 1))
      = ((finset.univ : finset (fin n)).filter (λ j, j.val < i)) ∪ {(⟨i, h⟩ : fin n)},
        by { ext ⟨_, _⟩, simp [nat.lt_succ_iff_lt_or_eq] },
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
lemma prod_of_fn {n : ℕ} {f : fin n → α} :
  (of_fn f).prod = ∏ i, f i :=
begin
  convert prod_take_of_fn f n,
  { rw [take_all_of_le (le_of_eq (length_of_fn f))] },
  { have : ∀ (j : fin n), (j : ℕ) < n := λ j, j.is_lt,
    simp [this] }
end

end comm_monoid

lemma alternating_sum_eq_finset_sum {G : Type*} [add_comm_group G] :
  ∀ (L : list G), alternating_sum L = ∑ i : fin L.length, (-1 : ℤ) ^ (i : ℕ) • L.nth_le i i.is_lt
| [] := by { rw [alternating_sum, finset.sum_eq_zero], rintro ⟨i, ⟨⟩⟩ }
| (g :: []) := by simp
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
