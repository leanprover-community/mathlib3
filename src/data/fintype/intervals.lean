/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.set.intervals
import data.set.finite
import data.fintype
import tactic

/-!
# fintype instances for intervals

We provide `fintype` instances for `Ico l u`, for `l u : ℕ`, and for `l u : ℤ`.
-/

namespace set

instance Ico_ℕ_fintype (l u : ℕ) : fintype (Ico l u) :=
fintype.of_finset (finset.Ico l u) $
  (λ n, by { simp only [mem_Ico, finset.Ico.mem], })

instance Ico_ℤ_fintype (l u : ℤ) : fintype (Ico l u) :=
fintype.of_finset (finset.Ico_ℤ l u) $
  (λ n, by { simp only [mem_Ico, finset.Ico_ℤ.mem], })

-- TODO other useful instances: pnat, fin n, zmod?

end set
