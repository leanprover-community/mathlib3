/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import data.nat.parity
import data.zmod.basic
/-!
# Relating parity to natural numbers mod 2

This module provides lemmas relating `zmod 2` to `even` and `odd`.

## Tags

parity, zmod, even, odd
-/

namespace zmod

lemma eq_zero_iff_even {n : ℕ} : (n : zmod 2) = 0 ↔ even n :=
(char_p.cast_eq_zero_iff (zmod 2) 2 n).trans even_iff_two_dvd.symm

lemma eq_one_iff_odd {n : ℕ} : (n : zmod 2) = 1 ↔ odd n :=
by { rw [← @nat.cast_one (zmod 2), zmod.eq_iff_modeq_nat, nat.odd_iff, nat.modeq], norm_num }

lemma ne_zero_iff_odd {n : ℕ} : (n : zmod 2) ≠ 0 ↔ odd n :=
by split; { contrapose, simp [eq_zero_iff_even], }

end zmod
