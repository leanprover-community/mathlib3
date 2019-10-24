/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.nat.prime
import tactic.fin_cases

/-!
# Lemmas about min_fac

These lemmas don't work in `data/nat/prime.lean`, because they use `fin_cases` in the proofs,
which would introduce a cyclic import.
-/

namespace nat

lemma min_fac_le_div {n : ℕ} (pos : 0 < n) (np : ¬ prime n) : min_fac n ≤ n / min_fac n :=
begin
  by_cases h : n = 1,
  { subst h, simp, },
  { replace h : 2 ≤ n := le_of_not_gt (λ hgt, h $ le_antisymm (nat.le_pred_of_lt hgt) (nat.succ_le_of_lt pos)),
    have d : min_fac n ∣ n := min_fac_dvd n,
    apply min_fac_le_of_dvd,
    { by_contradiction,
      rw [not_le] at a,
      -- replace with `nat_cases` when it arrives
      replace a : n / min_fac n ∈ [0,1] := list.Ico.mem.mpr ⟨zero_le _, a⟩,
      fin_cases a,
      { exact ne_of_gt pos (eq_zero_of_div_eq_zero a d (min_fac_pos _)) },
      { exact np (nat.prime_def_min_fac.2 ⟨h, (eq_of_dvd_quot_one d a)⟩) } },
    exact div_dvd_of_dvd d,
  }
end

end nat
