/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import data.list.nodup
import data.list.range
import data.nat.succ_pred
import algebra.order.ring.with_top
import order.succ_pred.basic

/-!
# Antidiagonals in ℕ × ℕ as lists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the antidiagonals of ℕ × ℕ as lists: the `n`-th antidiagonal is the list of
pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

Files `data.multiset.nat_antidiagonal` and `data.finset.nat_antidiagonal` successively turn the
`list` definition we have here into `multiset` and `finset`.
-/

open list function nat

namespace list
namespace nat

/-- The antidiagonal of a natural number `n` is the list of pairs `(i, j)` such that `i + j = n`. -/
def antidiagonal : with_bot ℕ → list (ℕ × ℕ)
| ⊥ := []
| (n : ℕ) := (range (n+1)).map (λ i, (i, n - i))

/-- A pair (i, j) is contained in the antidiagonal of `n` if and only if `i + j = n`. -/
@[simp] lemma mem_antidiagonal {n : with_bot ℕ} {x : ℕ × ℕ} :
  x ∈ antidiagonal n ↔ ↑(x.1 + x.2) = n :=
begin
  induction n using with_bot.rec_bot_coe; rw [antidiagonal],
  { simp },
  rw [mem_map, with_bot.coe_inj], split,
  { rintros ⟨i, hi, rfl⟩, rw [mem_range, lt_succ_iff] at hi, exact add_tsub_cancel_of_le hi },
  { rintro rfl, refine ⟨x.fst, _, _⟩,
    { rw [mem_range, add_assoc, lt_add_iff_pos_right], exact zero_lt_succ _ },
    { exact prod.ext rfl (add_tsub_cancel_left _ _) } }
end

/-- The length of the antidiagonal of `n` is `n + 1`. -/
@[simp] lemma length_antidiagonal (n : with_bot ℕ) : (antidiagonal n).length = (order.succ n).unbot (order.succ_ne_bot _) :=
begin
  induction n using with_bot.rec_bot_coe; rw [antidiagonal],
  { simp, refl },
  rw [length_map, length_range],
  simp_rw [with_bot.succ_coe, nat.succ_eq_succ, with_bot.unbot_coe],
end

/-- The antidiagonal of `0` is the list `[(0, 0)]` -/
@[simp] lemma antidiagonal_zero : antidiagonal 0 = [(0, 0)] :=
rfl

/-- The antidiagonal of `n` does not contain duplicate entries. -/
lemma nodup_antidiagonal : ∀ (n : with_bot ℕ), nodup (antidiagonal n)
| ⊥ := nodup_nil
| (n : ℕ) := (nodup_range _).map (@left_inverse.injective ℕ (ℕ × ℕ) prod.fst (λ i, (i, n-i)) $ λ i, rfl)

@[simp] lemma antidiagonal_succ : ∀ (n : with_bot ℕ),
  antidiagonal (order.succ n) =
    (0, (order.succ n).unbot (order.succ_ne_bot _))
      :: ((antidiagonal n).map (prod.map nat.succ id))
| ⊥ := by { simp [antidiagonal], refl }
| (n : ℕ) := begin
  simp only [antidiagonal, range_succ_eq_map, map_cons, true_and, add_zero,
    id.def, eq_self_iff_true, tsub_zero, map_map, prod.map_mk, with_bot.succ_coe,
    with_bot.unbot_coe, nat.succ_eq_succ, nat.succ_sub_one],
  apply congr (congr rfl _) rfl,
  ext; simp,
end

lemma antidiagonal_succ' : ∀ {n : with_bot ℕ},
  antidiagonal (order.succ n) = ((antidiagonal n).map (prod.map id nat.succ))
                              ++ [((order.succ n).unbot (order.succ_ne_bot _), 0)]
| ⊥ := by { simp [antidiagonal], refl }
| (n : ℕ) := begin
  simp only [antidiagonal, range_succ, add_tsub_cancel_left, map_append,
    append_assoc, tsub_self, singleton_append, map_map, map, with_bot.succ_coe,
    with_bot.unbot_coe, nat.succ_eq_succ, nat.succ_sub],
  congr' 1,
  apply map_congr,
  simp [le_of_lt, nat.succ_eq_add_one, nat.sub_add_comm] { contextual := tt },
end

lemma antidiagonal_succ_succ' {n : with_bot ℕ} :
  antidiagonal (order.succ (order.succ n)) =
  (0, (order.succ (order.succ n)).unbot (order.succ_ne_bot _)) :: ((antidiagonal n).map (prod.map nat.succ nat.succ))
    ++ [((order.succ (order.succ n)).unbot (order.succ_ne_bot _), 0)] :=
begin
  rw [antidiagonal_succ', antidiagonal_succ, map_cons, prod.map, id.def, map_map],
  { cases n; refl },
end

lemma map_swap_antidiagonal : ∀ {n : with_bot ℕ},
  (antidiagonal n).map prod.swap = (antidiagonal n).reverse
| ⊥ := rfl
| (n : ℕ) := begin
  rw [antidiagonal, map_map, prod.swap, ← list.map_reverse,
    range_eq_range', reverse_range', ← range_eq_range', map_map],
  apply map_congr,
  simp [nat.sub_sub_self, lt_succ_iff] { contextual := tt },
end

end nat
end list
