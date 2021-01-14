/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yakov Pechersky, Robert Y. Lewis
-/
import data.fin
import tactic.core

/-!
# Meta operations on Π (n : ℕ), fin n

This file defines functions for dealing with `fin n` numbers as expressions.

They are not defined earlier in the hierarchy, in the `tactic` or `meta` folders, since we do not
want to import `data.fin` there.

## Main definitions

* `fin.mk_numeral` embeds a `fin n` as a numeral expression into a type supporting the needed
  operations. It does not need a tactic state.
* `fin.reflect` specializes `fin.mk_numeral` to `fin (n + 1)`.
* `expr.of_fin` behaves like `fin.mk_numeral`, but uses the tactic state to infer the needed
  structure on the target type.

* `expr.to_fin` evaluates a normal numeral expression as a `fin n`.
* `expr.eval_fin` evaluates a numeral expression with arithmetic operations as a `fin n`.

-/

variables {n : ℕ}

/--
`fin.mk_numeral i` embeds `i` as a numeral expression inside a type with 0, 1, +

`type`: an expression representing the target type. This must live in Type 0.
`has_zero`, `has_one`, `has_add`: expressions of the type `has_zero %%type`, etc.

This function is similar to `expr.of_fin` but takes more hypotheses and is not tactic valued.
 -/
meta def fin.mk_numeral (type has_zero has_one has_add : expr) : fin n → expr
| ⟨i, _⟩ := nat.mk_numeral type has_zero has_one has_add i

/-- `fin.reflect i` represents the finite number `i`
as a numeral expression of type `fin (n + 1)`. -/
protected meta def fin.reflect : fin (n + 1) → expr :=
fin.mk_numeral `(fin (n + 1)) `((by apply_instance : has_zero (fin (n + 1))))
         `((by apply_instance : has_one (fin (n + 1))))`((by apply_instance : has_add (fin (n + 1))))

section
local attribute [semireducible] reflected
meta instance : has_reflect (fin (n + 1)) := fin.reflect
end

/-- Evaluates an expression as a finite number
if that expression represents a `fin 1`, which always gives back `0`. -/
private meta def expr.to_fin_one : expr → option (fin 1)
| e := do k ← e.to_nat, pure (fin.of_nat 0)

/-- Evaluates an expression as a finite number,
if that expression represents a numeral of a `fin (n + 2)`,
or `fin.succ` of a numeral.cast_succ` of a numeral. -/
private meta def expr.to_fin_succ : expr → option (fin (n + 2))
| `(@fin.succ %%t %%e) := do k ← e.to_nat, m ← t.to_nat, pure (fin.succ (@fin.of_nat n (k % m)))
| e := do k ← e.to_nat, pure (fin.of_nat k)

/-- Evaluates an expression as a finite number,
if that expression represents a numeral of a `fin (n + 1)`,
or `fin.succ` of a numeral.cast_succ` of a numeral. -/
protected meta def expr.to_fin : Π (n : ℕ), expr → option (fin (n + 1))
| 0       := expr.to_fin_one
| (n + 1) := expr.to_fin_succ

/-- Evaluates an expression into a finite `fin (n + 1)` number, if that expression is built up from
  numerals, +, *, /, ⁻¹  -/
protected meta def expr.eval_fin : expr → option (fin (n + 1))
| `(has_zero.zero) := some 0
| `(has_one.one) := some 1
| `(bit0 %%q) := (*) 2 <$> q.eval_fin
| `(bit1 %%q) := (+) 1 <$> (*) 2 <$> q.eval_fin
| `(%%a + %%b) := (+) <$> a.eval_fin <*> b.eval_fin
| `(%%a * %%b) := (*) <$> a.eval_fin <*> b.eval_fin
| _ := none

/-- `expr.of_fin α q` embeds `q` as a numeral expression inside the type `α`.
Lean will try to infer the correct type classes on `α`, and the tactic will fail if it cannot.
This function is similar to `fin.mk_numeral` but it takes fewer hypotheses and is tactic valued.
-/
protected meta def expr.of_fin (α : expr) : fin (n + 1) → tactic expr
| ⟨k, _⟩ := expr.of_nat α k

namespace tactic
namespace instance_cache

/-- `c.of_nat q` embeds `q` as a numeral expression inside the type `α`.
Lean will try to infer the correct type classes on `c.α`, and the tactic will fail if it cannot.
This function is similar to `fin.mk_numeral` but it takes fewer hypotheses and is tactic valued.
-/
protected meta def of_fin (c : instance_cache) : fin (n + 1) → tactic (instance_cache × expr)
| ⟨k, hk⟩ := c.of_nat k

end instance_cache
end tactic
