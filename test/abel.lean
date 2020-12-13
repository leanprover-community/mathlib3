import tactic.abel
variables {α : Type*} {a b : α}

example [add_comm_monoid α] : a + (b + a) = a + a + b := by abel
example [add_comm_group α] : (a + b) - ((b + a) + a) = -a := by abel
example [add_comm_group α] (x : α) : x - 0 = x := by abel
