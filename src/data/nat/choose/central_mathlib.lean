/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.nat.choose.central

/-!
# Stuff for data.nat.choose.central
-/

section

lemma central_binom_monotone : monotone nat.central_binom :=
λ n m h, (nat.choose_le_choose n (nat.mul_le_mul_left 2 h)).trans (nat.choose_le_central_binom _ _)

end
