import tactic.localized_notation

open tactic

section
localized_notation "local infix ` ⊹ `:59 := nat.add" in nat
localized_notation "local infix ` ⊖ `:59 := nat.mul" in nat.mul
#print ⊹
#print ⊖
end
#print ⊹ -- fails
#print ⊖ -- fails
example : unit := ()
open_notation int
#print ⊹ -- fails
#print ⊖ -- fails
example : unit := ()
section
open_notation nat
#print ⊹
#print ⊖ -- fails
example : unit := ()
open_notation nat.mul
#print ⊹
#print ⊖
example : unit := ()
end
section
open_notation nat.mul nat nat.mul int
#print ⊹
#print ⊖
example : unit := ()
end

example : unit := by do print_localized_notations [`nat, `nat.mul], constructor
