# Maths in Lean : integers


The integers `ℤ` (written `\Z` in VS Code) are an inductive type with
two constructors — `of_nat` (which takes a natural number `n` to the
associated integer `(n:ℤ)`) and `neg_succ_of_nat` (which takes `n` to
the integer `-1-n`).

There are around 30 theorems about integers in core lean and around 200
more in mathlib. Here are some examples of theorems in core Lean:

```lean
open int 

example : (6:ℤ) = of_nat (6:ℕ) := rfl 
example : (-6:ℤ) = neg_succ_of_nat (5:ℕ) := rfl 

example : -[1+5] = neg_succ_of_nat 5 := rfl 

-- + - * all defined.

-- Compability of these with the corresponding operators
-- on naturals needs to be checked

-- Explicit coercion from ℕ to ℤwith of_nat 

example (m n : ℕ) : of_nat (m * n) = of_nat m * of_nat n := of_nat_mul m n

-- Automatic coercion with an up-arrow. This lemma is protected
-- so we need to write "int" even though we opened int.

example (m n : ℕ) : (↑(m * n) : ℤ) = ↑m * ↑n := int.coe_nat_mul m n 

-- injectivity of coercion 

example (m n : ℕ) : (↑m : ℤ) = (↑n : ℤ) → m = n := int.coe_nat_inj  

-- nat_abs is the absolute value from ℤ to ℕ

example : nat_abs (-6) = 6 := rfl 

example (a : ℤ) : ↑(nat_abs a * nat_abs a) = a * a := nat_abs_mul_self 

-- Three ways to do division and remainder!

example : int.mod (-5) (-2) = 1 := rfl 
example : int.div (-5) (-2) = 3 := rfl

-- try fdiv/fmod and quot/rem for the other conventions.

-- ℤ is a commutative ring:

example : comm_ring ℤ := by apply_instance 

-- so anything you can do with commutative rings you can do in ℤ.

example (a : ℤ) : a * 0 = 0 := mul_zero a 
```

And here are a few examples of what one can do using mathlib.

```lean
import data.int.basic
import data.nat.gcd 

open int 

example (m n : ℕ) : (↑(m * n) : ℤ) = ↑m * ↑n := by simp -- wouldn't work without the import
-- but note rfl works,

-- division is defined on all of ℤ because type theory.

example (a : ℤ) : a / 0 = 0 := int.div_zero a -- junk theorem 

example (a b : ℤ) : a / (-b) = -(a / b) := int.div_neg a b -- junk for b=0.

example (a b c : ℤ) : c ≠ 0 → (a + b * c) / c = a / c + b := int.add_mul_div_right a b

example (a b c d : ℤ) : (a - c) % d = (b - c) % d ↔ a % d = b % d := mod_sub_cancel_right c

example (a b : ℤ) (α : Type) [ring α] : (((a + b) : ℤ) : α) = (a : α) + (b : α) := cast_add a b 

-- extended gcd's are actually in mathlib's nat section

open nat 

example (m n : ℕ) : (nat.gcd m n : ℤ) = m * (gcd_a m n) + n * (gcd_b m n) := gcd_eq_gcd_ab m n
```
