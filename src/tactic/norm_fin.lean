/-
Copyright (c) 2021 Yakov Pechersky All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import tactic.norm_num

/-!
# `norm_fin`

This file defines functions for dealing with `fin n` numbers as expressions.

## Main definitions

* `fin.mk_numeral` embeds a `fin n` as a numeral expression into a type supporting the needed
  operations. It does not need a tactic state.
* `fin.reflect` specializes `fin.mk_numeral` to `fin (n + 1)`.
* `expr.of_fin` behaves like `fin.mk_numeral`, but uses the tactic state to infer the needed
  structure on the target type.

* `expr.to_fin` evaluates a normal numeral expression as a `fin n`.
* `expr.eval_fin` evaluates a numeral expression with arithmetic operations as a `fin n`.

* 'norm_fin.eval' is a `norm_num` plugin for normalizing `k` where `k` are numerals,
optionally preceded by `fin.succ` or `fin.cast_succ`.

-/

/--
`fin.mk_numeral i` embeds `i` as a numeral expression inside a type with `0`, `1`, `+`

* `type`: an expression representing the target type. This must live in Type 0.
* `has_zero`, `has_one`, `has_add`: expressions of the type `has_zero %%type`, etc.

This function is similar to `expr.of_fin` but takes more hypotheses and is not tactic valued.
 -/
meta def fin.mk_numeral (type has_zero has_one has_add : expr) (n : ℕ) : fin n → expr
| ⟨i, _⟩ := nat.mk_numeral type has_zero has_one has_add i

/-- `fin.reflect i` represents the finite number `i : fin (n + 1)`. -/
protected meta def fin.reflect {n : ℕ} : fin (n + 1) → expr :=
fin.mk_numeral `(fin (n + 1)) `((by apply_instance : has_zero (fin (n + 1))))
  `((by apply_instance : has_one (fin (n + 1))))`((by apply_instance : has_add (fin (n + 1))))
  (n + 1)

section
local attribute [semireducible] reflected
meta instance {n : ℕ} : has_reflect (fin (n + 1)) := fin.reflect
end

/-- Evaluates an expression as a finite number
if that expression represents a `fin 1`, which always gives back `0`. -/
private meta def expr.to_fin_one : expr → option (fin 1)
| e := do guardb e.is_numeral, pure (fin.of_nat 0)

/-- Evaluates an expression as a finite number,
if that expression represents a numeral of a `fin (n + 2)`,
or `fin.succ` of a numeral.cast_succ` of a numeral. -/
private meta def expr.to_fin_succ {n : ℕ} : expr → option (fin (n + 2))
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
protected meta def expr.eval_fin (n : ℕ) : expr → option (fin (n + 1))
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
protected meta def expr.of_fin {n : ℕ} (α : expr) : fin (n + 1) → tactic expr
| ⟨k, _⟩ := expr.of_nat α k

open norm_num

namespace tactic

/-- Given `a`,`b` `fin n` numerals, proves `⊢ a < b`. -/
meta def prove_lt_fin : expr → expr → tactic expr
| a b := do
  `(fin %%en) ← infer_type a,
  nic ← mk_instance_cache `(ℕ),
  en ← prod.fst <$> eval_field en <|> pure en,
  nty ← en.to_nat,
  en ← pure `(nty),
  na ← expr.eval_fin nty a,
  nb ← expr.eval_fin nty b,
  (_, ena) ← nic.of_nat na,
  (_, pna) ← prove_lt_nat nic ena en,
  (_, enb) ← nic.of_nat nb,
  (_, pnb) ← prove_lt_nat nic enb en,
  (_, pnlt) ← prove_lt_nat nic ena enb,
  to_expr ``(fin.lt_num %%en %%ena %%enb %%pna %%pnb %%pnlt)

namespace instance_cache

/-- `c.of_nat q` embeds `q` as a numeral expression inside the type `α`.
Lean will try to infer the correct type classes on `c.α`, and the tactic will fail if it cannot.
This function is similar to `fin.mk_numeral` but it takes fewer hypotheses and is tactic valued.
-/
protected meta def of_fin {n : ℕ} (c : instance_cache) :
  fin (n + 1) → tactic (instance_cache × expr)
| ⟨k, hk⟩ := c.of_nat k

/-- Given `a`,`b` `fin n` numerals, proves `⊢ a ≠ b`. -/
meta def prove_ne_fin (ic : instance_cache) (a b : expr) (na nb : ℚ) :
  tactic (instance_cache × expr) :=
if na < nb then do
  p ← prove_lt_fin a b,
  ic.mk_app ``ne_of_lt [a, b, p]
else do
  p ← prove_lt_fin b a,
  ic.mk_app ``ne_of_gt [a, b, p]

end instance_cache

end tactic

open tactic expr

namespace norm_num

lemma fin.succ_num_eq (m n k l : ℕ) (hl : l < n) (hk : k < m) (h : m = n + 1) (h' : k = l + 1) :
  fin.succ (⟨l, hl⟩ : fin n) = (⟨k, hk⟩ : fin m) :=
begin
  cases n,
  { exact absurd hl (not_lt_of_le l.zero_le) },
  subst h,
  subst h',
  simp [fin.eq_iff_veq, fin.add_def, nat.mod_eq_of_lt hk],
end

lemma fin.cast_succ_num_eq (m n l : ℕ) (hl : l < n) (hl' : l < m) (h : m = n + 1) :
  fin.cast_succ (⟨l, hl⟩ : fin n) = (⟨l, hl'⟩ : fin m) :=
begin
  cases n,
  { exact absurd hl (not_lt_of_le l.zero_le) },
  subst h,
  simp [fin.eq_iff_veq, fin.add_def, nat.mod_eq_of_lt hl'],
end

lemma fin.bit0_of_mod (n k l m : ℕ) (hk : k < n) (hl : l < n)
  (h : l + l = m) (h' : m % n = k) :
  (bit0 ⟨l, hl⟩ : fin n) = (⟨k, hk⟩ : fin n) :=
begin
  cases n,
  { exact absurd hl (not_lt_of_le l.zero_le) },
  simp [fin.eq_iff_veq, bit0, fin.add_def, ←h', ←h]
end

lemma fin.bit1_of_mod (n k l m : ℕ) (hk : k < n + 1) (hl : l < n + 1)
  (h : l + l + 1 = m) (h' : m % (n + 1) = k) :
  (bit1 ⟨l, hl⟩ : fin (n + 1)) = (⟨k, hk⟩ : fin (n + 1)) :=
begin
  cases n,
  { simp },
  simp [fin.eq_iff_veq, bit1, bit0, fin.add_def, ←h', ←h]
end

lemma fin.lt_num (n a b : ℕ) (ha : a < n) (hb : b < n) (h : a < b) :
  (⟨a, ha⟩ : fin n) < ⟨b, hb⟩ :=
fin.lt_iff_coe_lt_coe.mpr h

end norm_num

open norm_num

namespace norm_fin

/--
A `norm_num` plugin for normalizing `(k : fin n)` where `k` is numeral.
It also handles `fin.succ k` and `fin.cast_succ k`.

```
example : (5 : fin 7) = fin.succ (fin.succ 3) := by norm_num
```
-/
@[norm_num] meta def eval : expr → tactic (expr × expr)
| `(@fin.succ %%en %%e) := do
  ic ← mk_instance_cache `(ℕ),
  en ← prod.fst <$> eval_field en <|> pure en,
  n ← eval_expr ℕ en,
  en ← pure `(n),
  fk ← e.to_fin n,
  (_, ek) ← ic.of_nat fk,
  (_, ltkn) ← prove_lt_nat ic ek en,
  (_, _, en', pn) ← prove_nat_succ ic `(nat.succ %%en),
  (_, _, ek', pk) ← prove_nat_succ ic `(nat.succ %%ek),
  (_, ltkn') ← prove_lt_nat ic ek' en',
  ty ← to_expr ``(fin %%en'),
  fk' ← ty.of_fin (fk + 1),
  pure (fk', `(fin.succ_num_eq %%en' %%en %%ek' %%ek %%ltkn %%ltkn' %%pn %%pk))
| (app `(@coe_fn (fin %%en ↪o fin %%en') %%inst %%fexpr) e) := do
  guard (fexpr.get_app_fn.const_name = ``fin.cast_succ),
  en ← prod.fst <$> eval_field en <|> pure en,
  ic ← mk_instance_cache `(ℕ),
  n ← eval_expr ℕ en,
  en ← pure `(n),
  fk ← e.to_fin n,
  (_, ek) ← ic.of_nat fk,
  (_, ltkn) ← prove_lt_nat ic ek en,
  (_, _, en', pn) ← prove_nat_succ ic `(nat.succ %%en),
  (_, ltkn') ← prove_lt_nat ic ek en',
  ty ← to_expr ``(fin %%en'),
  fk' ← ty.of_fin fk,
  pure (fk', `(fin.cast_succ_num_eq %%en' %%en %%ek %%ltkn %%ltkn' %%pn))
| `(bit0 %%e) := do
  ty ← infer_type e,
  `(fin %%en) ← pure ty,
  en ← prod.fst <$> eval_field en <|> pure en,
  nty ← eval_expr ℕ en,
  en ← pure `(nty),
  vale ← expr.eval_fin nty e,
  ic ← mk_instance_cache `(ℕ),
  (_, enat) ← ic.of_nat vale,
  (_, benat, pbit0) ← prove_add_nat' ic enat enat,
  beval ← benat.to_nat,
  guard (nty ≤ beval),
  (_, mode, pmod) ← prove_div_mod ic benat en tt,
  (_, ltkn) ← prove_lt_nat ic mode en,
  (_, ltkl) ← prove_lt_nat ic enat en,
  modf ← mode.to_fin nty,
  fk' ← ty.of_fin modf,
  pure (fk', `(fin.bit0_of_mod %%en %%mode %%enat %%benat %%ltkn %%ltkl %%pbit0 %%pmod))
| `(bit1 %%e) := do
  ty ← infer_type e,
  `(fin %%en) ← pure ty,
  en ← prod.fst <$> eval_field en <|> pure en,
  nty ← eval_expr ℕ en,
  en ← pure `(nty),
  vale ← expr.eval_fin nty e,
  ic ← mk_instance_cache `(ℕ),
  (_, enat) ← ic.of_nat vale,
  (_, benat) ← ic.mk_bit1 enat,
  beval ← benat.to_nat,
  guard (nty ≤ beval),
  (en', pn) ← prove_sub_nat ic en `(1),
  (_, _, en'', pn) ← prove_nat_succ ic `(nat.succ %%en'),
  (_, pbit1) ← prove_adc_nat ic enat enat benat,
  (_, mode, pmod) ← prove_div_mod ic benat en tt,
  (_, ltkn) ← prove_lt_nat ic mode en,
  (_, ltkl) ← prove_lt_nat ic enat en,
  modf ← mode.to_fin nty,
  fk' ← ty.of_fin modf,
  pure (fk', `(fin.bit1_of_mod %%en' %%mode %%enat %%benat %%ltkn %%ltkl %%pbit1 %%pmod))
| _ := failed

end norm_fin
