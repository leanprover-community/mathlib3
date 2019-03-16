/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging Presburger arithmetic goals using the Omega test.
-/

import data.nat.basic

namespace nat

lemma lt_iff_add_one_le {m n : ℕ} :
  m < n ↔ m + 1 ≤ n  := by rw succ_le_iff

lemma max_succ_succ {m n} : 
  max (succ m) (succ n) = succ (max m n) :=
begin
  by_cases h1 : m ≤ n, 
  rw [max_eq_right h1, max_eq_right (succ_le_succ h1)], 
  { rw not_le at h1, have h2 := le_of_lt h1,
    rw [max_eq_left h2, max_eq_left (succ_le_succ h2)] }
end

end nat

variable {α : Type}

def update (m a) (v : nat → α) : nat → α 
| n := if n = m then a else v n

notation v `⟨` m `↦` a `⟩` := update m a v

lemma update_eq (m a) (v : nat → α) : (v ⟨m ↦ a⟩) m = a :=
begin simp only [update, if_pos rfl] end

lemma update_eq_of_ne {m a} {v : nat → α} (k) : 
  k ≠ m → update m a v k = v k :=
begin intro h1, simp only [update], rw if_neg h1 end

def update_zero (a : α) (v : nat → α) : nat → α
| 0     := a 
| (k+1) := v k

open tactic

meta def revert_cond (t : expr → tactic bool) (x : expr) : tactic unit :=
mcond (t x) (revert x >> skip) skip 

meta def revert_cond_all (t : expr → tactic bool) : tactic unit :=
do hs ← local_context, mmap (revert_cond t) hs, skip
