/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.basic
import algebra.floor
import data.finset.intervals
import data.list.sort
import data.real.basic

open_locale big_operators
open finset

/-!
# IMO 2018 C3

Let `n` be a given positive integer. Sisyphus performs a sequence of turns on a board consisting of
`n - 1` squares in a row, numbered `0` to `n` from left to right. Initially, `n` stones are put
into square `0`, and the other squares are empty. At every turn, Sisyphus chooses any nonempty
square, say with `k` stones, takes one of those stones and moves it to the right by at most `k`
squares (the stone should stay within the board). Sisyphus' aim is to move all `n` stones to square
`n`.
Prove that Sisyphus cannot reach the aim in less than `⌈n/1⌉ + ... + ⌈n/n⌉` turns.
-/

variable {n : ℕ}

def energy (pos : vector ℕ n) : ℕ :=
list.sum (list.map₂ (λ a b, (a + b - 1)/b) (list.merge_sort (≤) pos.1) (list.range n))

variables {move : vector ℕ n → vector ℕ n} (hf : ∀ pos, ∃ i, (move pos).nth i ≤ pos.nth i +
  ((univ : finset (fin n)).filter (λ j, pos.nth j = pos.nth i)).card ∧
  ∀ j, i ≠ j → (move pos).nth j = pos.nth j)

lemma energy_move {pos : vector ℕ n} :
  energy (move pos) ≤ energy pos + 1 :=
begin
  sorry
end

theorem imo2018_c3 {m : ℕ} (h : move^[m] (λ i, 0) = λ i, n) :
  (∑ k in Ico 0 n, nat_ceil (n/k : ℝ)) ≤ m :=
begin
  suffices ∀ k, energy (move^[k] (λ i, 0)) ≤ k,
  {
    sorry
  },
  induction k with k hk,
  {
    sorry
  },
  sorry
end
