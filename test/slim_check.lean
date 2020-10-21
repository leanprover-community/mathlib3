import tactic.slim_check
import .mk_slim_check_test

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
(0 shrinks)
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
(2 shrinks)
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
(5 shrinks)
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
(2 shrinks)
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
(4 shrinks)
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

f := [2 ↦ 3, 3 ↦ 9, 4 ↦ 6, 5 ↦ 4, 6 ↦ 2, 8 ↦ 5, 9 ↦ 8, x ↦ x]
x := 3
y := 4
guard: 3 ≤ 4 (by construction)
issue: 9 ≤ 6 does not hold
(5 shrinks)
-------------------
",
  admit,
  trivial,
end

example (f : ℤ → ℤ) (h : injective f) (g : ℤ → ℤ) (h : injective g) (i) : true :=
begin
  have : f i = g i,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

f := [x ↦ x]
g := [1 ↦ 2, 2 ↦ 1, x ↦ x]
i := 1
issue: 1 = 2 does not hold
(5 shrinks)
-------------------
",
  admit,
  trivial,
end

example (f : ℤ → ℤ) (h : injective f) : true :=
begin
  have : monotone f,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

f := [2 ↦ 3, 3 ↦ 9, 4 ↦ 6, 5 ↦ 4, 6 ↦ 2, 8 ↦ 5, 9 ↦ 8, x ↦ x]
x := 3
y := 4
guard: 3 ≤ 4 (by construction)
issue: 9 ≤ 6 does not hold
(5 shrinks)
-------------------
",
  admit,
  trivial,
end

example (f : ℤ → ℤ) : true :=
begin
  have : injective f,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

f := [_ ↦ 0]
x := 0
y := -1
guard: 0 = 0
issue: 0 = -1 does not hold
(0 shrinks)
-------------------
",
  admit,
  trivial,
end

example (f : ℤ → ℤ) : true :=
begin
  have : monotone f,
  success_if_fail_with_msg
  { slim_check { random_seed := some 257 } }
"
===================
Found problems!

f := [-6 ↦ 97, 0 ↦ 0, _ ↦ 4]
x := -6
y := -2
guard: -6 ≤ -2 (by construction)
issue: 97 ≤ 4 does not hold
(5 shrinks)
-------------------
",
  admit,
  trivial,
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
(4 shrinks)
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
y := 41
guard: 41 ≤ 59 (by construction)
issue: 100 < 100 does not hold
(8 shrinks)
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
(1 shrinks)
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
y := 52
guard: 52 ≤ 52 (by construction)
issue: 104 < 100 does not hold
(4 shrinks)
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
(0 shrinks)
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
(0 shrinks)
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
(0 shrinks)
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
(0 shrinks)
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
(0 shrinks)
-------------------
",
  admit,
  trivial,
end
