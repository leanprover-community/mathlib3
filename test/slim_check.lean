
import tactic.slim_check

example : true :=
begin
  have : ∀ i j : ℕ, i < j → j < i,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
  "
===================
Found problems!

i := 0
j := 1
-------------------
",
  admit,
  trivial
end

example : true :=
begin
  have : (∀ x : ℕ, 2 ∣ x → x < 100),
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
  "
===================
Found problems!

x := 102
-------------------
",
  admit,
  trivial
end

example (xs : list ℕ) (w : ∃ x ∈ xs, x < 3) : true :=
begin
  have : ∀ y ∈ xs, y < 5,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

xs := [1, 10]
x := 1
y := 10
-------------------
",
  admit,
  trivial
end

example (x : ℕ) (h : 2 ∣ x) : true :=
begin
  have : x < 100,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

x := 102
-------------------
",
  admit,
  trivial
end

example (α : Type) (xs ys : list α) : true :=
begin
  have : xs ++ ys = ys ++ xs,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

α := ℤ
xs := [5]
ys := [7]
[5, 7] ≠ [7, 5]
-------------------
",
  admit,
  trivial
end

example : true :=
begin
  have : ∀ x ∈ [1,2,3], x < 4,
  slim_check { random_seed := some 257, quiet := tt },
    -- success
  trivial,
end
