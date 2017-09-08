/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Elegant pairing function.
-/
import data.nat.sqrt
open prod decidable

namespace nat

def mkpair (a b : nat) : nat :=
if a < b then b*b + a else a*a + a + b

def unpair (n : nat) : nat × nat :=
let s := sqrt n in
if n - s*s < s then (n - s*s, s) else (s, n - s*s - s)

theorem mkpair_unpair (n : nat) : mkpair (unpair n).1 (unpair n).2 = n :=
let s := sqrt n in
by_cases
  (assume : n - s*s < s, by simp [unpair, mkpair, this, nat.add_sub_of_le sqrt_lower])
  (assume h₁ : ¬ n - s*s < s,
    have s ≤ n - s*s,                  from le_of_not_gt h₁,
    have s + s*s ≤ n - s*s + s*s,      from add_le_add_right this (s*s),
    have h₂ : s*s + s ≤ n,             by rwa [nat.sub_add_cancel sqrt_lower, add_comm] at this,

    have n < (s + 1) * (s + 1),        from sqrt_upper,
    have n < (s * s + s + s) + 1,      by simp [mul_add, add_mul] at this; simp [this],
    have n - s*s ≤ s + s,              from calc
        n - s*s ≤ (s*s + s + s) - s*s    : nat.sub_le_sub_right (le_of_succ_le_succ this) (s*s)
            ... = (s*s + (s+s)) - s*s    : by rewrite add_assoc
            ... = s + s                  : by rewrite nat.add_sub_cancel_left,
    have n - s*s - s ≤ s,              from calc
         n - s*s - s ≤ (s + s) - s       : nat.sub_le_sub_right this s
                 ... = s                 : by rewrite nat.add_sub_cancel_left,
    have h₃ : ¬ s < n - s*s - s,       from not_lt_of_ge this,
    begin
      simp [h₁, h₃, unpair, mkpair, -add_comm, -add_assoc],
      rewrite [nat.sub_sub, add_sub_of_le h₂]
    end)

theorem unpair_mkpair (a b : nat) : unpair (mkpair a b) = (a, b) :=
by_cases
 (assume : a < b,
  have a + b * b < (b + 1) * (b + 1),
    from calc a + b * b < b + b * b : add_lt_add_right this _
      ... ≤ b + b * b + (b + 1) : le_add_right _ _
      ... = (b + 1) * (b + 1) : by simp [mul_add, add_mul],
  have sqrt_mkpair : sqrt (mkpair a b) = b,
    by simp [mkpair, *]; exact sqrt_eq (le_add_left _ _) this,
  have mkpair a b - b * b = a, by simp [mkpair, ‹a < b›, -add_comm, nat.add_sub_cancel_left],
  by simp [unpair, sqrt_mkpair, this, ‹a < b›])
 (assume : ¬ a < b,
  have a + (b + a * a) < (a + 1) * (a + 1),
    from calc a + (b + a * a) ≤ a + (a + a * a) :
      add_le_add_left (add_le_add_right (le_of_not_gt this) _) _
      ... < (a + 1) * (a + 1) : lt_of_succ_le $ by simp [mul_add, add_mul, succ_eq_add_one],
  have sqrt_mkpair : sqrt (mkpair a b) = a,
    by simp [mkpair, *]; exact sqrt_eq (le_add_of_nonneg_of_le (zero_le _) (le_add_left _ _)) this,
  have mkpair_sub : mkpair a b - a * a = a + b,
    by simp [mkpair, ‹¬ a < b›]; rw [←add_assoc, nat.add_sub_cancel],
  have ¬ a + b < a, from not_lt_of_ge $ le_add_right _ _,
  by simp [unpair, ‹¬ a < b›, sqrt_mkpair, mkpair_sub, this, nat.add_sub_cancel_left])

theorem unpair_lt_aux {n : nat} : n ≥ 1 → (unpair n).1 < n :=
assume : n ≥ 1,
or.elim (nat.eq_or_lt_of_le this)
  (assume : 1 = n, by subst n; exact dec_trivial)
  (assume : n > 1,
   let s := sqrt n in
   by_cases
    (assume h : n - s*s < s,
      have n > 0, from lt_of_succ_lt ‹n > 1›,
      have sqrt n > 0, from sqrt_pos_of_pos this,
      have sqrt n * sqrt n > 0, from mul_pos this this,
      by simp [unpair, h]; exact sub_lt ‹n > 0› ‹sqrt n * sqrt n > 0›)
    (assume : ¬ n - s*s < s, by simp [unpair, this]; exact sqrt_lt ‹n > 1›))

theorem unpair_lt : ∀ (n : nat), (unpair n).1 < succ n
| 0        := dec_trivial
| (succ n) :=
  have (unpair (succ n)).1 < succ n, from unpair_lt_aux dec_trivial,
  lt.step this

end nat
