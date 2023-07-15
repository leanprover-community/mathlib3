/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import tactic.core

/-! ### Helpers to invoke functions involving algebra at tactic time

It's not clear whether using `instance_cache` is a sensible choice here.
In particular, we need to use these tactics below when the algebraic instances are local variables
that aren't in the "real" instance cache (the one used by `tactic.reset_instance_cache`).
-/
namespace expr

/-- Produce a `has_one` instance for the type cached by `t`, such that `1 : expr` is the one of that
type. -/
meta def has_one (t : tactic.instance_cache) :
  tactic (tactic.instance_cache × has_one expr) :=
do
  (t, one) ← t.mk_app `has_one.one [],
  pure (t, { one := one })

/-- Produce a `has_zero` instance for the type cached by `t`, such that `0 : expr` is the zero of
that type. -/
meta def has_zero (t : tactic.instance_cache) :
  tactic (tactic.instance_cache × has_zero expr) :=
do
  (t, zero) ← t.mk_app `has_zero.zero [],
  pure (t, { zero := zero })

/-- Produce a `has_mul` instance for the type cached by `t`, such that `(*) : expr → expr → expr` is
the multiplication of that type. -/
meta def has_mul (t : tactic.instance_cache) :
  tactic (tactic.instance_cache × has_mul expr) :=
do
  (t, mul) ← t.mk_app `has_mul.mul [],
  pure (t, { mul := λ a b, mul a b })

/-- Produce a `has_add` instance for the type cached by `t`, such that `(+) : expr → expr → expr` is
the addition of that type. -/
meta def has_add (t : tactic.instance_cache) :
  tactic (tactic.instance_cache × has_add expr) :=
do
  (t, add) ← t.mk_app `has_add.add [],
  pure (t, { add := λ a b, add a b })

end expr
