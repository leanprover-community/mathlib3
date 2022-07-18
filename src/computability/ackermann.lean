import computability.primrec
import tactic
import order.filter.at_top_bot

/-- The two-argument Ackermann function, defined so that

- `ackermann 0 n = n + 1`
- `ackermann (m + 1) 0 = ackermann m 1`
- `ackermann (m + 1) (n + 1) = ackermann m (ackermann (m + 1) n)`.

This is of interest as both a fast-growing function, and as an example of a recursive function that
isn't primitive recursive. -/
def ackermann : ℕ → ℕ → ℕ
| 0       n       := n + 1
| (m + 1) 0       := ackermann m 1
| (m + 1) (n + 1) := ackermann m (ackermann (m + 1) n)

@[simp] theorem ackermann_zero (n : ℕ) : ackermann 0 n = n + 1 := by rw ackermann

@[simp] theorem ackermann_succ_zero (m : ℕ) : ackermann (m + 1) 0 = ackermann m 1 := by rw ackermann

@[simp] theorem ackermann_succ_succ (m n : ℕ) :
  ackermann (m + 1) (n + 1) = ackermann m (ackermann (m + 1) n) :=
by rw ackermann

@[simp] theorem ackermann_one (n : ℕ) : ackermann 1 n = n + 2 :=
begin
  induction n with n IH,
  { simp },
  { simp [IH] }
end

@[simp] theorem ackermann_two (n : ℕ) : ackermann 2 n = 2 * n + 3 :=
begin
  induction n with n IH,
  { simp },
  { simp [IH, nat.mul_succ] }
end

private theorem ackermann_three_aux (n : ℕ) : (ackermann 3 n : ℤ) = 2 ^ (n + 3) - 3 :=
begin
  induction n with n IH,
  { simp, norm_num },
  { simp [IH, pow_succ],
    rw [mul_sub, sub_add],
    norm_num }
end

@[simp] theorem ackermann_three (n : ℕ) : ackermann 3 n = 2 ^ (n + 3) - 3 :=
begin
  zify,
  rw nat.cast_sub,
  { exact_mod_cast ackermann_three_aux n },
  { have H : 3 ≤ 2 ^ 3 := by norm_num,
    exact H.trans (pow_mono one_le_two $ le_add_left le_rfl) }
end

theorem ackermann_pos : ∀ m n, 0 < ackermann m n
| 0       n       := by simp
| (m + 1) 0       := by { rw ackermann_succ_zero, apply ackermann_pos }
| (m + 1) (n + 1) := by { rw ackermann_succ_succ, apply ackermann_pos }

theorem one_lt_ackermann_succ : ∀ m n, 1 < ackermann (m + 1) n
| 0       n       := by simp
| (m + 1) 0       := by { rw ackermann_succ_zero, apply one_lt_ackermann_succ }
| (m + 1) (n + 1) := by { rw ackermann_succ_succ, apply one_lt_ackermann_succ }

theorem ackermann_strict_mono_left : ∀ m, strict_mono (ackermann m)
| 0 n₁ n₂ h := by simpa using h
| (m + 1) 0 0 h := h.false.elim
| (m + 1) 0 (n + 1) h := begin
  rw [ackermann_succ_zero, ackermann_succ_succ],
  exact ackermann_strict_mono_left _ (one_lt_ackermann_succ m n)
end
| (m + 1) (n₁ + 1) 0 h := (nat.not_lt_zero _ h).elim
| (m + 1) (n₁ + 1) (n₂ + 1) h := begin
  rw [ackermann_succ_succ, ackermann_succ_succ],
  apply ackermann_strict_mono_left _ (ackermann_strict_mono_left _ _),
  rwa add_lt_add_iff_right at h
end

theorem sum_lt_ackermann : ∀ m n, m + n < ackermann m n
| 0       n       := by simp
| (m + 1) 0       := by { rw [ackermann_succ_zero, add_zero], apply sum_lt_ackermann }
| (m + 1) (n + 1) := begin
  rw [ackermann_succ_succ, add_assoc],
  apply (sum_lt_ackermann m _).trans,
  apply ackermann_strict_mono_left,
end

theorem lt_ackermann_of_primrec₂ {f : ℕ → ℕ} (hf : nat.primrec f) :
  ∀ᶠ n in filter.at_top, f n < ackermann n n :=
begin
  induction hf,
  { exact filter.eventually_of_forall (λ n, ackermann_pos n n) },
  {

  }

end
