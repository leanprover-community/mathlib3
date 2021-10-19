/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import data.multiset.nodup
import data.list.nat_antidiagonal

/-!
# Antidiagonals in ℕ × ℕ as multisets

This file defines the antidiagonals of ℕ × ℕ as multisets: the `n`-th antidiagonal is the multiset
of pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines file `data.list.nat_antidiagonal` and is further refined by file
`data.finset.nat_antidiagonal`.
-/

namespace multiset
namespace nat

/-- The antidiagonal of a natural number `n` is
    the multiset of pairs `(i, j)` such that `i + j = n`. -/
def antidiagonal (n : ℕ) : multiset (ℕ × ℕ) :=
list.nat.antidiagonal n

/-- A pair (i, j) is contained in the antidiagonal of `n` if and only if `i + j = n`. -/
@[simp] lemma mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} :
  x ∈ antidiagonal n ↔ x.1 + x.2 = n :=
by rw [antidiagonal, mem_coe, list.nat.mem_antidiagonal]

/-- The cardinality of the antidiagonal of `n` is `n+1`. -/
@[simp] lemma card_antidiagonal (n : ℕ) : (antidiagonal n).card = n+1 :=
by rw [antidiagonal, coe_card, list.nat.length_antidiagonal]

/-- The antidiagonal of `0` is the list `[(0, 0)]` -/
@[simp] lemma antidiagonal_zero : antidiagonal 0 = {(0, 0)} :=
rfl

/-- The antidiagonal of `n` does not contain duplicate entries. -/
@[simp] lemma nodup_antidiagonal (n : ℕ) : nodup (antidiagonal n) :=
coe_nodup.2 $ list.nat.nodup_antidiagonal n

@[simp] lemma antidiagonal_succ {n : ℕ} :
  antidiagonal (n + 1) = (0, n + 1) ::ₘ ((antidiagonal n).map (prod.map nat.succ id)) :=
by simp only [antidiagonal, list.nat.antidiagonal_succ, coe_map, cons_coe]

end nat
end multiset
