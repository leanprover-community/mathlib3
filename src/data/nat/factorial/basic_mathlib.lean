/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import data.nat.factorial.basic

/-!
# Stuff for data.nat.factorial.basic
-/

namespace nat

lemma asc_le_pow_mul_factorial {s t : ℕ} : t.asc_factorial s ≤ s.factorial * (t + 1) ^ s :=
begin
  induction s with s ih,
  { simp },
  rw [asc_factorial_succ, factorial_succ, pow_succ, mul_mul_mul_comm],
  refine nat.mul_le_mul _ ih,
  rw [add_comm t, add_one_mul, mul_add_one, add_assoc],
  simp,
end

end nat
