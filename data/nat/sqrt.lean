/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Johannes Hölzl

Very simple (sqrt n) function that returns s s.t.
    s * s ≤ n < (s + 1) * (s + 1)
-/
import data.nat.sub

namespace nat
open decidable

private lemma sqrt_exists (n : ℕ) : ∃k:ℕ, n < (k + 1) * (k + 1) :=
⟨n, calc n < (n + 1) * 1 : by simp; exact nat.lt_add_of_pos_right zero_lt_one
  ... ≤ (n + 1) * (n + 1) : mul_le_mul_left _ $ le_add_left _ _⟩

-- This is the simplest possible function that just performs a linear search
definition sqrt (n : nat) : nat := nat.find $ sqrt_exists n

theorem sqrt_upper {n : nat} : n < (sqrt n + 1) * (sqrt n + 1) :=
nat.find_spec $ sqrt_exists n

theorem sqrt_lower {n : nat} : sqrt n * sqrt n ≤ n :=
begin
  cases h : sqrt n,
  case nat.zero { simp [zero_le] },
  case nat.succ k h {
    have sqrt_min : ∀{k}, k < sqrt n → ¬ (n < (k + 1) * (k + 1)),
      from assume k, nat.find_min $ sqrt_exists n,
    show (k + 1) * (k + 1) ≤ n,
      from le_of_not_gt (sqrt_min $ by simp [h, nat.lt_succ_self]) }
end

theorem sqrt_mono {n k : ℕ} (h : n ≤ k) : sqrt n ≤ sqrt k :=
le_of_not_gt $ assume : sqrt k < sqrt n,
  have k < n,
    from calc k < (sqrt k + 1) * (sqrt k + 1) : sqrt_upper
      ... ≤ sqrt n * sqrt n : mul_le_mul this this (zero_le _) (zero_le _)
      ... ≤ n : sqrt_lower,
  absurd h ((lt_iff_not_ge _ _).mp this)

theorem sqrt_eq {m n : ℕ} (h₁ : n * n ≤ m) (h₂ : m < (n + 1) * (n + 1)) : sqrt m = n :=
have sqr_lt : ∀{n m:ℕ}, n * n < (m + 1) * (m + 1) → n ≤ m,
  from assume n m h, le_of_not_gt $ assume : n > m,
  have n * n ≥ (m + 1) * (m + 1), from mul_le_mul this this (zero_le _) (zero_le _),
  absurd h (not_lt_of_ge this),
le_antisymm
  (sqr_lt $ show sqrt m * sqrt m < (n + 1) * (n + 1), from lt_of_le_of_lt sqrt_lower h₂)
  (sqr_lt $ show n * n < (sqrt m + 1) * (sqrt m + 1), from lt_of_le_of_lt h₁ sqrt_upper)

private theorem le_squared : ∀ (n : nat), n ≤ n*n
| 0        := by simp
| (succ n) :=
  have 1 ≤ succ n, from succ_le_succ (zero_le _),
  have 1 * succ n ≤ succ n * succ n, from mul_le_mul_right _ this,
  by rwa [one_mul] at this

private theorem lt_squared : ∀ {n : nat}, n > 1 → n < n * n
| 0               h := absurd h dec_trivial
| 1               h := absurd h dec_trivial
| (succ (succ n)) h :=
  have 1 < succ (succ n),
    from dec_trivial,
  have succ (succ n) * 1 < succ (succ n) * succ (succ n),
    from mul_lt_mul_of_pos_left this dec_trivial,
  by rewrite [mul_one] at this; exact this

theorem eq_zero_of_sqrt_eq_zero {n : nat} : sqrt n = 0 → n = 0 :=
assume : sqrt n = 0,
have n < (sqrt n + 1) * (sqrt n + 1), from sqrt_upper,
have succ n ≤ succ 0, by simp [‹sqrt n = 0›] at this; assumption,
eq_zero_of_le_zero $ le_of_succ_le_succ this

theorem le_three_of_sqrt_eq_one {n : nat} : sqrt n = 1 → n ≤ 3 :=
assume : sqrt n = 1,
have n < 4,
  from calc n < (sqrt n + 1) * (sqrt n + 1) : sqrt_upper
    ... = 4 : by simp [this]; exact dec_trivial,
le_of_succ_le_succ this

theorem sqrt_lt : ∀ {n : nat}, n > 1 → sqrt n < n
| 0     h := absurd h dec_trivial
| 1     h := absurd h dec_trivial
| 2     h := dec_trivial
| 3     h := dec_trivial
| (n+4) h :=
  have sqrt (n+4) > 1, from decidable.by_contradiction $
    assume : ¬ sqrt (n+4) > 1,
    have sqrt (n+4) ≤ 1, from le_of_not_gt this,
    or.elim (le_iff_lt_or_eq.mp this)
      (assume : sqrt (n+4) < 1,
        have sqrt (n+4) = 0, from eq_zero_of_le_zero (le_of_lt_succ this),
        have n + 4 = 0,      from eq_zero_of_sqrt_eq_zero this,
        absurd this dec_trivial)
      (assume : sqrt (n+4) = 1,
        have n+4 ≤ 3, from le_three_of_sqrt_eq_one this,
        absurd this dec_trivial),
  calc sqrt (n+4) < sqrt (n+4) * sqrt (n+4) : lt_squared this
              ... ≤ n+4                     : sqrt_lower

theorem sqrt_pos_of_pos {n : nat} : n > 0 → sqrt n > 0 :=
assume : n > 0,
have sqrt n ≠ 0, from
  assume : sqrt n = 0,
  have n = 0, from eq_zero_of_sqrt_eq_zero this,
  by subst n; exact absurd ‹0 > 0› (lt_irrefl _),
lt_of_le_of_ne (zero_le _) this.symm

theorem sqrt_mul_eq {n : nat} : sqrt (n*n) = n :=
sqrt_eq (le_refl _) (mul_lt_mul' (le_add_right _ _) (lt_succ_self _) (zero_le _) (zero_lt_succ _))

theorem mul_square_cancel {a b : nat} : a*a = b*b → a = b :=
assume h,
have sqrt (a*a) = sqrt (b*b), by rewrite h,
by rwa [sqrt_mul_eq, sqrt_mul_eq] at this

end nat
