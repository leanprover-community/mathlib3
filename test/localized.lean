import tactic.localized

open tactic
local infix ` ⊹ `:59 := nat.mul
local infix ` ⊖ `:59 := nat.pow
example : 2 ⊹ 3 = 6 := rfl
example : 2 ⊖ 3 = 8 := rfl
example {n m : ℕ} (h : n < m) : n ≤ m := by { success_if_fail { simp [h] }, exact le_of_lt h }
section
localized "infix ` ⊹ `:59 := nat.add" in nat
localized "infix ` ⊖ `:59 := nat.mul" in nat.mul
localized "attribute [simp] le_of_lt" in le
example : 2 ⊹ 3 = 5 := rfl
example : 2 ⊖ 3 = 6 := rfl
example {n m : ℕ} (h : n < m) : n ≤ m := by { simp [h] }
end

section
example : 2 ⊹ 3 = 6 := rfl
example : 2 ⊖ 3 = 8 := rfl
example {n m : ℕ} (h : n < m) : n ≤ m := by { success_if_fail { simp [h] }, exact le_of_lt h }

open_notation int
example : 2 ⊹ 3 = 6 := rfl
example : 2 ⊖ 3 = 8 := rfl

open_notation nat
example : 2 ⊹ 3 = 5 := rfl
example : 2 ⊖ 3 = 8 := rfl

open_notation nat.mul
example : 2 ⊹ 3 = 5 := rfl
example : 2 ⊖ 3 = 6 := rfl
end

section
open_notation nat.mul nat nat.mul int le
example : 2 ⊹ 3 = 5 := rfl
example : 2 ⊖ 3 = 6 := rfl
example {n m : ℕ} (h : n < m) : n ≤ m := by { simp [h] }
end
