/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.nat.order.basic
import algebra.order.monoid.with_top

/-!
# `with_bot ℕ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Lemmas about the type of natural numbers with a bottom element adjoined.
-/

namespace nat

namespace with_bot

lemma add_eq_zero_iff {n m : with_bot ℕ} : n + m = 0 ↔ n = 0 ∧ m = 0 :=
begin
  rcases ⟨n, m⟩ with ⟨_ | _, _ | _⟩,
  any_goals { tautology },
  repeat { erw [with_bot.coe_eq_coe] },
  exact add_eq_zero_iff
end

lemma add_eq_one_iff {n m : with_bot ℕ} : n + m = 1 ↔ n = 0 ∧ m = 1 ∨ n = 1 ∧ m = 0 :=
begin
  rcases ⟨n, m⟩ with ⟨_ | _, _ | _⟩,
  any_goals { tautology },
  repeat { erw [with_bot.coe_eq_coe] },
  exact add_eq_one_iff
end

lemma add_eq_two_iff {n m : with_bot ℕ} :
  n + m = 2 ↔ n = 0 ∧ m = 2 ∨ n = 1 ∧ m = 1 ∨ n = 2 ∧ m = 0 :=
begin
  rcases ⟨n, m⟩ with ⟨_ | _, _ | _⟩,
  any_goals { tautology },
  repeat { erw [with_bot.coe_eq_coe] },
  exact add_eq_two_iff
end

lemma add_eq_three_iff {n m : with_bot ℕ} :
  n + m = 3 ↔ n = 0 ∧ m = 3 ∨ n = 1 ∧ m = 2 ∨ n = 2 ∧ m = 1 ∨ n = 3 ∧ m = 0 :=
begin
  rcases ⟨n, m⟩ with ⟨_ | _, _ | _⟩,
  any_goals { tautology },
  repeat { erw [with_bot.coe_eq_coe] },
  exact add_eq_three_iff
end

lemma coe_nonneg {n : ℕ} : 0 ≤ (n : with_bot ℕ) :=
by { rw [← with_bot.coe_zero, with_bot.coe_le_coe], exact nat.zero_le _ }

@[simp] lemma lt_zero_iff (n : with_bot ℕ) : n < 0 ↔ n = ⊥ :=
option.cases_on n dec_trivial $ λ n, iff_of_false
  (by simp [with_bot.some_eq_coe, coe_nonneg]) (λ h, option.no_confusion h)

lemma one_le_iff_zero_lt {x : with_bot ℕ} : 1 ≤ x ↔ 0 < x :=
begin
  refine ⟨λ h, lt_of_lt_of_le (with_bot.coe_lt_coe.mpr zero_lt_one) h, λ h, _⟩,
  induction x using with_bot.rec_bot_coe,
  { exact (not_lt_bot h).elim },
  { exact with_bot.coe_le_coe.mpr (nat.succ_le_iff.mpr (with_bot.coe_lt_coe.mp h)) }
end

lemma lt_one_iff_le_zero {x : with_bot ℕ} : x < 1 ↔ x ≤ 0 :=
not_iff_not.mp (by simpa using one_le_iff_zero_lt)

lemma add_one_le_of_lt {n m : with_bot ℕ} (h : n < m) : n + 1 ≤ m :=
begin
  cases n, { exact bot_le },
  cases m, exacts [(not_lt_bot h).elim, with_bot.some_le_some.2 (with_bot.some_lt_some.1 h)],
end

end with_bot

end nat
