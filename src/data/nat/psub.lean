/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.nat.basic
/-!
# Partial predecessor and partial subtraction on the natural numbers

The usual definition of natural number subtraction (`nat.sub`) returns 0 as a "garbage value" for
`a - b` when `a < b`. Similarly, `nat.pred 0` is defined to be `0`. The functions in this file
wrap the result in an `option` type instead:

## Main definitions

- `nat.ppred`: a partial predecessor operation
- `nat.psub`: a partial subtraction operation

-/
namespace nat

/-- Partial predecessor operation. Returns `ppred n = some m`
  if `n = m + 1`, otherwise `none`. -/
@[simp] def ppred : ℕ → option ℕ
| 0     := none
| (n+1) := some n

/-- Partial subtraction operation. Returns `psub m n = some k`
  if `m = n + k`, otherwise `none`. -/
@[simp] def psub (m : ℕ) : ℕ → option ℕ
| 0     := some m
| (n+1) := psub n >>= ppred

theorem pred_eq_ppred (n : ℕ) : pred n = (ppred n).get_or_else 0 :=
by cases n; refl

theorem sub_eq_psub (m : ℕ) : ∀ n, m - n = (psub m n).get_or_else 0
| 0     := rfl
| (n+1) := (pred_eq_ppred (m-n)).trans $
  by rw [sub_eq_psub, psub]; cases psub m n; refl

@[simp] theorem ppred_eq_some {m : ℕ} : ∀ {n}, ppred n = some m ↔ succ m = n
| 0     := by split; intro h; contradiction
| (n+1) := by dsimp; split; intro h; injection h; subst n

@[simp] theorem ppred_eq_none : ∀ {n : ℕ}, ppred n = none ↔ n = 0
| 0     := by simp
| (n+1) := by dsimp; split; contradiction

theorem psub_eq_some {m : ℕ} : ∀ {n k}, psub m n = some k ↔ k + n = m
| 0     k := by simp [eq_comm]
| (n+1) k :=
  begin
    dsimp,
    apply option.bind_eq_some.trans,
    simp [psub_eq_some, add_comm, add_left_comm, nat.succ_eq_add_one]
  end

theorem psub_eq_none {m n : ℕ} : psub m n = none ↔ m < n :=
begin
  cases s : psub m n; simp [eq_comm],
  { show m < n, refine lt_of_not_ge (λ h, _),
    cases le.dest h with k e,
    injection s.symm.trans (psub_eq_some.2 $ (add_comm _ _).trans e) },
  { show n ≤ m, rw ← psub_eq_some.1 s, apply nat.le_add_left }
end

theorem ppred_eq_pred {n} (h : 0 < n) : ppred n = some (pred n) :=
ppred_eq_some.2 $ succ_pred_eq_of_pos h

theorem psub_eq_sub {m n} (h : n ≤ m) : psub m n = some (m - n) :=
psub_eq_some.2 $ nat.sub_add_cancel h

theorem psub_add (m n k) : psub m (n + k) = do x ← psub m n, psub x k :=
by induction k; simp [*, add_succ, bind_assoc]

/-- Same as `psub`, but with a more efficient implementation. -/
@[inline] def psub' (m n : ℕ) : option ℕ := if n ≤ m then some (m - n) else none

theorem psub'_eq_psub (m n) : psub' m n = psub m n :=
by rw [psub']; split_ifs;
  [exact (psub_eq_sub h).symm, exact (psub_eq_none.2 (not_le.1 h)).symm]

end nat
