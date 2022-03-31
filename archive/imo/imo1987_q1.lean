/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.fintype.card
import dynamics.fixed_points.basic

/-!
# Formalization of IMO 1987, Q1

Let $p_{n, k}$ be the number of permutations of a set of cardinality `n ≥ 1` that fix exactly `k`
elements. Prove that $∑_{k=0}^n k p_{n,k}=n!$.

To prove this identity, we show that both sides are equal to the cardinality of the set
`{(x : α, σ : perm α) | σ x = x}`, regrouping by `card (fixed_points σ)` for the left hand side and
by `x` for the right hand side.

The original problem assumes `n ≥ 1`. It turns out that a version with `n * (n - 1)!` in the RHS
holds true for `n = 0` as well, so we first prove it, then deduce the original version in the case
`n ≥ 1`. -/

variables (α : Type*) [fintype α] [decidable_eq α]

open_locale big_operators nat
open equiv fintype function finset (range sum_const) set (Iic)

namespace imo_1987_q1

/-- The set of pairs `(x : α, σ : perm α)` such that `σ x = x` is equivalent to the set of pairs
`(x : α, σ : perm {x}ᶜ)`. -/
def fixed_points_equiv :
  {σx : α × perm α | σx.2 σx.1 = σx.1} ≃ Σ x : α, perm ({x}ᶜ : set α) :=
calc {σx : α × perm α | σx.2 σx.1 = σx.1} ≃ Σ x : α, {σ : perm α | σ x = x} : set_prod_equiv_sigma _
... ≃ Σ x : α, {σ : perm α | ∀ y : ({x} : set α), σ y = equiv.refl ↥({x} : set α) y} :
  sigma_congr_right (λ x, equiv.set.of_eq $ by { simp only [set_coe.forall], dsimp, simp })
... ≃ Σ x : α, perm ({x}ᶜ : set α) :
  sigma_congr_right (λ x, by apply equiv.set.compl)

theorem card_fixed_points :
  card {σx : α × perm α | σx.2 σx.1 = σx.1} = card α * (card α - 1)! :=
by simp [card_congr (fixed_points_equiv α), card_perm, finset.filter_not, finset.card_sdiff,
  finset.filter_eq', finset.card_univ]

/-- Given `α : Type*` and `k : ℕ`, `fiber α k` is the set of permutations of `α` with exactly `k`
fixed points. -/
@[derive fintype]
def fiber (k : ℕ) : set (perm α) := {σ : perm α | card (fixed_points σ) = k}

@[simp] lemma mem_fiber {σ : perm α} {k : ℕ} : σ ∈ fiber α k ↔ card (fixed_points σ) = k := iff.rfl

/-- `p α k` is the number of permutations of `α` with exactly `k` fixed points. -/
def p (k : ℕ) := card (fiber α k)

/-- The set of triples `(k ≤ card α, σ ∈ fiber α k, x ∈ fixed_points σ)` is equivalent
to the set of pairs `(x : α, σ : perm α)` such that `σ x = x`. The equivalence sends
`(k, σ, x)` to `(x, σ)` and `(x, σ)` to `(card (fixed_points σ), σ, x)`.

It is easy to see that the cardinality of the LHS is given by
`∑ k : fin (card α + 1), k * p α k`. -/
def fixed_points_equiv' :
  (Σ (k : fin (card α + 1)) (σ : fiber α k), fixed_points σ.1) ≃
    {σx : α × perm α | σx.2 σx.1 = σx.1} :=
{ to_fun := λ p, ⟨⟨p.2.2, p.2.1⟩, p.2.2.2⟩,
  inv_fun := λ p,
    ⟨⟨card (fixed_points p.1.2), (card_subtype_le _).trans_lt (nat.lt_succ_self _)⟩,
     ⟨p.1.2, rfl⟩, ⟨p.1.1, p.2⟩⟩,
  left_inv := λ ⟨⟨k, hk⟩, ⟨σ, hσ⟩, ⟨x, hx⟩⟩, by { simp only [mem_fiber, subtype.coe_mk] at hσ,
    subst k, refl },
  right_inv := λ ⟨⟨x, σ⟩, h⟩, rfl }

/-- Main statement for any `(α : Type*) [fintype α]`. -/
theorem main_fintype :
  ∑ k in range (card α + 1), k * p α k = card α * (card α - 1)! :=
have A : ∀ k (σ : fiber α k), card (fixed_points ⇑(↑σ : perm α)) = k := λ k σ, σ.2,
by simpa [A, ← fin.sum_univ_eq_sum_range, -card_of_finset, finset.card_univ,
  card_fixed_points, mul_comm] using card_congr (fixed_points_equiv' α)

/-- Main statement for permutations of `fin n`, a version that works for `n = 0`. -/
theorem main₀ (n : ℕ) :
  ∑ k in range (n + 1), k * p (fin n) k = n * (n - 1)! :=
by simpa using main_fintype (fin n)

/-- Main statement for permutations of `fin n`. -/
theorem main {n : ℕ} (hn : 1 ≤ n) :
  ∑ k in range (n + 1), k * p (fin n) k = n! :=
by rw [main₀, nat.mul_factorial_pred (zero_lt_one.trans_le hn)]

end imo_1987_q1
