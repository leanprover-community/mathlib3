
import tactic.find_unused

def unused1 : ℕ := 1

inductive unused_type
| intro : unused_type

def my_list := list ℕ

def some_val : list ℕ := [1,2,3]

@[main_declaration]
def other_val : my_list := some_val

def used_somewhere_else : my_list := some_val
