import tactic.abel
import algebra.group.pi
variables {α : Type*} {a b : α}

example [add_comm_monoid α] : a + (b + a) = a + a + b := by abel
example [add_comm_group α] : (a + b) - ((b + a) + a) = -a := by abel
example [add_comm_group α] (x : α) : x - 0 = x := by abel
example [add_comm_monoid α] (x : α) : (3 : ℕ) • a = a + (2 : ℕ) • a := by abel
example [add_comm_group α] : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
example [add_comm_group α] (a b : α) : a-2•b = a -2•b := by abel
example [add_comm_group α] (a : α) : 0 + a = a := by abel1
example [add_comm_group α] (n : ℕ) (a : α) : n • a = n • a := by abel1
example [add_comm_group α] (n : ℕ) (a : α) : 0 + n • a = n • a := by abel1

-- instances do not have to syntactically be
-- `add_monoid.has_smul_nat` or `sub_neg_monoid.has_smul_int`
example [add_comm_monoid α] (x : ℕ → α) : ((2 : ℕ) • x) = x + x := by abel1
example [add_comm_group α] (x : ℕ → α) : ((2 : ℕ) • x) = x + x := by abel1
example [add_comm_group α] (x : ℕ → α) : ((2 : ℤ) • x) = x + x := by abel1

-- even if there's an instance we don't recognize, we treat it as an atom
example [add_comm_group α] [has_smul ℕ α] (x : ℕ → α) :
  ((2 : ℕ) • x) + ((2 : ℕ) • x) = (2 : ℤ) • ((2 : ℕ) • x) := by abel1

-- `abel!` should see through terms that are definitionally equal,
def id' (x : α) := x
example [add_comm_group α] : a + b - b - id' a = 0 :=
begin
  success_if_fail { abel; done },
  abel!
end
