import tactic.localized
import algebra.group_power

open tactic
local infix ` ⊹ `:59 := nat.mul
local infix ` ↓ `:59 := pow
local infix ` ⊖ `:59 := pow
example : 2 ⊹ 3 = 6 := rfl
example : 2 ↓ 3 = 8 := rfl
example : 2 ⊖ 3 = 8 := rfl
example {n m : ℕ} (h : n < m) : n ≤ m := by { success_if_fail { simp [h] }, exact le_of_lt h }
section
localized "infix ` ⊹ `:59 := nat.add" in nat
localized "infix ` ↓ `:59 := nat.mul" in nat
localized "infix ` ⊖ `:59 := nat.mul" in nat.mul
localized "attribute [simp] le_of_lt" in le
example : 2 ⊹ 3 = 5 := rfl
example : 2 ↓ 3 = 6 := rfl
example : 2 ⊖ 3 = 6 := rfl
example {n m : ℕ} (h : n < m) : n ≤ m := by { simp [h] }
end

section
example : 2 ⊹ 3 = 6 := rfl
example : 2 ↓ 3 = 8 := rfl
example : 2 ⊖ 3 = 8 := rfl
example {n m : ℕ} (h : n < m) : n ≤ m := by { success_if_fail { simp [h] }, exact le_of_lt h }

-- test that `open_locale` will fail when given a nonexistent locale
run_cmd success_if_fail $ get_localized [`ceci_nest_pas_une_locale]

open_locale nat
example : 2 ⊹ 3 = 5 := rfl
example : 2 ↓ 3 = 6 := rfl
example : 2 ⊖ 3 = 8 := rfl

open_locale nat.mul
example : 2 ⊹ 3 = 5 := rfl
example : 2 ↓ 3 = 6 := rfl
example : 2 ⊖ 3 = 6 := rfl
end

section
open_locale nat.mul nat nat.mul le
example : 2 ⊹ 3 = 5 := rfl
example : 2 ↓ 3 = 6 := rfl
example : 2 ⊖ 3 = 6 := rfl
example {n m : ℕ} (h : n < m) : n ≤ m := by { simp [h] }
end
