import tactic.localized_notation

open tactic
local infix ` ⊹ `:59 := nat.mul
local infix ` ⊖ `:59 := nat.pow
example : 2 ⊹ 3 = 6 := rfl
example : 2 ⊖ 3 = 8 := rfl

section
localized "infix ` ⊹ `:59 := nat.add" in nat
localized "infix ` ⊖ `:59 := nat.mul" in nat.mul
example : 2 ⊹ 3 = 5 := rfl
example : 2 ⊖ 3 = 6 := rfl
end

section
example : 2 ⊹ 3 = 6 := rfl
example : 2 ⊖ 3 = 8 := rfl

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
open_notation nat.mul nat nat.mul int
example : 2 ⊹ 3 = 5 := rfl
example : 2 ⊖ 3 = 6 := rfl
end
