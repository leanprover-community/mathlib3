
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
guard: 0 < 1 (by construction)
issue: 1 < 0 does not hold
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

x := 104
issue: 104 < 100 does not hold
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

xs := [5, 5, 0, 1]
x := 0
y := 5
issue: 5 < 5 does not hold
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

x := 104
issue: 104 < 100 does not hold
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
xs := [0]
ys := [1]
issue: [0, 1] = [1, 0] does not hold
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

open function slim_check

example (f : ℤ → ℤ) (h : injective f) : true :=
begin
  have : monotone (f ∘ small.mk),
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

f := [-1 ↦ 0, -2 ↦ -2, 0 ↦ -1, 1 ↦ 1, x ↦ x]
x := -1
y := 0
guard: -1 ≤ 0 (by construction)
issue: 0 ≤ -1 does not hold
-------------------
",
  admit,
  trivial
end

example (f : ℤ → ℤ) (h : injective f) : true :=
begin
  have : monotone f,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

f := [-1 ↦ 0, -2 ↦ -2, 0 ↦ -1, 1 ↦ 1, x ↦ x]
x := -1
y := 0
guard: -1 ≤ 0 (by construction)
issue: 0 ≤ -1 does not hold
-------------------
",
  admit,
  trivial
end

section

open tactic
@[interactive]
meta def mk_slim_check_test : tactic unit := do
tgt ← target,
msg ← (λ s, match interactive.slim_check { random_seed := some 257 } s with
      | result.success x _ := fail "expecting error" s
      | result.exception msg _ _ := result.success (msg.iget ()).to_string s
      end ),
trace!"Try this:
  have : {tgt},
  success_if_fail_with_msg
  {{ slim_check {{ random_seed := some 257 } }
\"{msg}\",
  admit,
  trivial
"

end

example (xs ys : list ℤ) (h : xs ~ ys) : true :=
begin
  have : list.qsort (λ x y, x ≠ y) xs = list.qsort (λ x y, x ≠ y) ys,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

xs := [0, 1]
ys := [1, 0]
guard: [0, 1] ~ [1, 0] (by construction)
issue: [0, 1] = [1, 0] does not hold
-------------------
",
  admit,
  trivial
end

example (x y : ℕ) : true :=
begin
  have : y ≤ x → x + y < 100,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

x := 59
y := 42
guard: 42 ≤ 59 (by construction)
issue: 101 < 100 does not hold
-------------------
",
  admit,
  trivial,
end

example (x : ℤ) : true :=
begin
  have : x ≤ 3 → 3 ≤ x,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

x := 2
guard: 2 ≤ 3 (by construction)
issue: 3 ≤ 2 does not hold
-------------------
",
  admit,
  trivial,
end

example (x y : ℤ) : true :=
begin
  have : y ≤ x → x + y < 100,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

x := 52
y := 49
guard: 49 ≤ 52 (by construction)
issue: 101 < 100 does not hold
-------------------
",
  admit,
  trivial,
end

example (x y : Prop) : true :=
begin
  have : x ∨ y → y ∧ x,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

x := tt
y := ff
guard: (true ∨ false)
issue: false does not hold
-------------------
",
  admit,
  trivial,
end

example (x y : Prop) : true :=
begin
  have : (¬x ↔ y) → y ∧ x,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

x := tt
y := ff
guard: (¬ true ↔ false)
issue: false does not hold
-------------------
",
  admit,
  trivial,
end

example (x y : Prop) : true :=
begin
  -- deterministic
  have : (x ↔ y) → y ∨ x,
  success_if_fail_with_msg
  { slim_check }
"
===================
Found problems!

x := ff
y := ff
guard: (false ↔ false)
issue: false does not hold
issue: false does not hold
-------------------
",
  admit,
  trivial,
end

example (x y : Prop) : true :=
begin
  -- deterministic
  have : y ∨ x,
  success_if_fail_with_msg
  { slim_check }
"
===================
Found problems!

x := ff
y := ff
issue: false does not hold
issue: false does not hold
-------------------
",
  admit,
  trivial,
end

example (x y : Prop) : true :=
begin
  have : x ↔ y,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

x := tt
y := ff
issue: false does not hold
issue: ¬ true does not hold
-------------------
",
  admit,
  trivial,
end
