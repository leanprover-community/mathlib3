/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.nat.prime
import tactic.interactive

/- Turn off trace messages so they don't pollute the test build: -/
-- set_option trace.silence_library_search true
/- For debugging purposes, we can display the list of lemmas: -/
-- set_option trace.library_search true

open nat

namespace test.library_search

-- example {a b : ℕ} (h : a * 2 ≤ b) : a ≤ b / 2 :=
-- by library_search! -- exact (nat.le_div_iff_mul_le a b (dec_trivial)).mpr h

-- example : prime 61 :=
-- by library_search!

lemma h {a b : ℕ} (p : prime 61) : a^2 ≤ b ∨ b^2 ≤ a^4 :=
begin
  have t := le_total (a^2) b,
  tidy,
end
-- example {a b : ℕ} : a^2 ≤ b ∨ b^2 ≤ a^4 :=
-- by library_search!

end test.library_search
