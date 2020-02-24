/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import tactic.interval_cases

example (n : ℕ) : true :=
begin
  success_if_fail { interval_cases n },
  trivial
end

example (n : ℕ) (h : 2 ≤ n) : true :=
begin
  success_if_fail { interval_cases n },
  trivial
end

example (n m : ℕ) (h : n ≤ m) : true :=
begin
  success_if_fail { interval_cases n },
  trivial,
end

example (n : ℕ) (w₂ : n < 0) : false :=
by interval_cases n

example (n : ℕ) (w₂ : n < 1) : n = 0 :=
by { interval_cases n, refl }

attribute [simp] bot_eq_zero

example (n : ℕ) (w₂ : n < 2) : n = 0 ∨ n = 1 :=
by { interval_cases n, simp, simp, }

example (n : ℕ) (w₁ : 1 ≤ n) (w₂ : n < 3) : n = 1 ∨ n = 2 :=
by { interval_cases n, simp, simp, }

instance : lattice.has_bot ℕ+ :=
{ bot := 1 }
instance : lattice.order_bot ℕ+ :=
{ bot_le := λ a, a.property,
  ..(by apply_instance : lattice.has_bot ℕ+),
  ..(by apply_instance : partial_order ℕ+) }

@[simp] lemma pnat.bot_eq_zero : (⊥ : ℕ+) = 1 := rfl

lemma nat.pos_of_bit0_pos {n : ℕ} (h : 0 < bit0 n) : 0 < n :=
by { cases n, cases h, apply nat.succ_pos, }

-- Some lemmas that rewrite `pnat.mk n h`, for `n` an explicit numeral, into explicit numerals.
@[simp] lemma pnat.one {h} : (⟨1, h⟩ : ℕ+) = (1 : ℕ+) := rfl
@[simp] lemma pnat.bit0 (n) {h} : (⟨bit0 n, h⟩ : ℕ+) = (bit0 ⟨n, nat.pos_of_bit0_pos h⟩ : ℕ+) := rfl
@[simp] lemma pnat.bit1 (n) {h} {k} : (⟨bit1 n, h⟩ : ℕ+) = (bit1 ⟨n, k⟩ : ℕ+) := rfl

-- Some lemmas that rewrite inequalities between explicit numerals in `pnat`
-- into the corresponding inequalities in `nat`.
@[simp] lemma pnat.one_le_bit0 (m : ℕ+) : (1 : ℕ+) ≤ (bit0 m) ↔ (1 : ℕ) ≤ (bit0 (m : ℕ)) := iff.refl _
@[simp] lemma pnat.one_le_bit1 (m : ℕ+) : (1 : ℕ+) ≤ (bit1 m) ↔ (1 : ℕ) ≤ (bit1 (m : ℕ)) := iff.refl _
@[simp] lemma pnat.bit0_le_bit0 (n m : ℕ+) : (bit0 n) ≤ (bit0 m) ↔ (bit0 (n : ℕ)) ≤ (bit0 (m : ℕ)) := iff.refl _
@[simp] lemma pnat.bit0_le_bit1 (n m : ℕ+) : (bit0 n) ≤ (bit1 m) ↔ (bit0 (n : ℕ)) ≤ (bit1 (m : ℕ)) := iff.refl _
@[simp] lemma pnat.bit1_le_bit0 (n m : ℕ+) : (bit1 n) ≤ (bit0 m) ↔ (bit1 (n : ℕ)) ≤ (bit0 (m : ℕ)) := iff.refl _
@[simp] lemma pnat.bit1_le_bit1 (n m : ℕ+) : (bit1 n) ≤ (bit1 m) ↔ (bit1 (n : ℕ)) ≤ (bit1 (m : ℕ)) := iff.refl _

example (n : ℕ) (w₁ : 1 < n) (w₂ : n < 4) : n = 2 ∨ n = 3 :=
by { interval_cases n, { left, refl }, { right, refl }, }

example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
by { interval_cases n, { left, refl }, { right, refl }, }

example (n : ℕ) (w₀ : n ≥ 2) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
by { interval_cases n, { left, refl }, { right, refl }, }

example (n : ℕ) (w₁ : n > 2) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
by { interval_cases n, { left, refl }, { right, refl }, }

example (n : ℕ) (w₁ : n > 2) (w₂ : n ≤ 4) : n = 3 ∨ n = 4 :=
by { interval_cases n, { left, refl }, { right, refl }, }

example (n : ℕ) (w₁ : 2 < n) (w₂ : 4 ≥ n) : n = 3 ∨ n = 4 :=
by { interval_cases n, { left, refl }, { right, refl }, }

example (n : ℕ) (h1 : 4 < n) (h2 : n ≤ 6) : n < 20 :=
begin
  interval_cases n,
  guard_target 5 < 20, norm_num,
  guard_target 6 < 20, norm_num,
end

example (n : ℕ) (w₁ : n % 3 < 1) : n % 3 = 0 :=
by { interval_cases n % 3, assumption }

example (n : ℕ) (h1 : 4 ≤ n) (h2 : n < 10) : n < 20 :=
begin
  interval_cases_using h1 h2,
  all_goals {norm_num}
end

example (n : ℕ+) (w₂ : n < 1) : false :=
by interval_cases n

example (n : ℕ+) (w₂ : n < 2) : n = 1 :=
by interval_cases n

example (n : ℕ+) (h1 : 4 ≤ n) (h2 : n < 5) : n = 4 :=
by interval_cases n

example (n : ℕ+) (w₁ : 2 < n) (w₂ : 4 ≥ n) : n = 3 ∨ n = 4 :=
begin
  interval_cases n,
  { guard_target (3 : ℕ+) = 3 ∨ (3 : ℕ+) = 4, left, refl },
  { guard_target (4 : ℕ+) = 3 ∨ (4 : ℕ+) = 4, right, refl },
end

example (n : ℕ+) (w₁ : 1 < n) (w₂ : n < 4) : n = 2 ∨ n = 3 :=
by { interval_cases n, { left, refl }, { right, refl }, }

example (n : ℕ+) (w₂ : n < 3) : n = 1 ∨ n = 2 :=
by { interval_cases n, { left, refl }, { right, refl }, }

example (n : ℕ+) (w₂ : n < 4) : n = 1 ∨ n = 2 ∨ n = 3 :=
by { interval_cases n, { left, refl }, { right, left, refl }, { right, right, refl }, }

example (z : ℤ) (h1 : z ≥ -3) (h2 : z < 2) : z < 20 :=
begin
  interval_cases_using h1 h2,
  all_goals {norm_num}
end

example (z : ℤ) (h1 : z ≥ -3) (h2 : z < 2) : z < 20 :=
begin
  interval_cases z,
  guard_target (-3 : ℤ) < 20, norm_num,
  guard_target (-2 : ℤ) < 20, norm_num,
  guard_target (-1 : ℤ) < 20, norm_num,
  guard_target (0 : ℤ) < 20, norm_num,
  guard_target (1 : ℤ) < 20, norm_num,
end

/-
Sadly, this one doesn't work, reporting:
  `deep recursion was detected at 'expression equality test'`
-/
-- example (n : ℕ) (w₁ : n > 1000000) (w₁ : n < 1000002) : n < 2000000 :=
-- begin
--   interval_cases n,
--   norm_num,
-- end
