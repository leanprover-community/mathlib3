/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import data.finset.basic
import data.multiset.nat_antidiagonal

/-!
# The "antidiagonal" {(0,n), (1,n-1), ..., (n,0)} as a finset.
-/

namespace finset

namespace nat

/-- The antidiagonal of a natural number `n` is
    the finset of pairs `(i,j)` such that `i+j = n`. -/
def antidiagonal (n : ℕ) : finset (ℕ × ℕ) :=
⟨multiset.nat.antidiagonal n, multiset.nat.nodup_antidiagonal n⟩

/-- A pair (i,j) is contained in the antidiagonal of `n` if and only if `i+j=n`. -/
@[simp] lemma mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} :
  x ∈ antidiagonal n ↔ x.1 + x.2 = n :=
by rw [antidiagonal, finset.mem_def, multiset.nat.mem_antidiagonal]

/-- The cardinality of the antidiagonal of `n` is `n+1`. -/
@[simp] lemma card_antidiagonal (n : ℕ) : (antidiagonal n).card = n+1 :=
by simp [antidiagonal]

/-- The antidiagonal of `0` is the list `[(0,0)]` -/
@[simp] lemma antidiagonal_zero : antidiagonal 0 = {(0, 0)} :=
rfl

end nat

end finset
