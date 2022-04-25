/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.nat.parity
import order.filter.at_top_bot

/-!
# Numbers are frequently modeq to fixed numbers

In this file we prove that `m ≡ d [MOD n]` frequently as `m → ∞`.
-/

open filter

namespace nat

/-- Infinitely many natural numbers are equal to `d` mod `n`. -/
lemma frequently_modeq {n : ℕ} (h : n ≠ 0) (d : ℕ) : ∃ᶠ m in at_top, m ≡ d [MOD n] :=
((tendsto_add_at_top_nat d).comp (tendsto_id.nsmul_at_top h.bot_lt)).frequently $
  frequently_of_forall $ λ m, by { simp [nat.modeq_iff_dvd, ← sub_sub] }

lemma frequently_mod_eq {d n : ℕ} (h : d < n) : ∃ᶠ m in at_top, m % n = d :=
by simpa only [nat.modeq, mod_eq_of_lt h] using frequently_modeq h.ne_bot d

lemma frequently_even : ∃ᶠ m : ℕ in at_top, even m :=
by simpa only [even_iff] using frequently_mod_eq zero_lt_two

lemma frequently_odd : ∃ᶠ m : ℕ in at_top, odd m :=
by simpa only [odd_iff] using frequently_mod_eq one_lt_two

end nat
