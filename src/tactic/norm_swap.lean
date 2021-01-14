/-
Copyright (c) 2021 Yakov Pechersky All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.equiv.basic
import meta.expr
import tactic.norm_num

/-!
# `norm_swap`

Evaluating `swap x y z` for numerals `x y z : ℕ`, via a `norm_cast` plugin.
Terms are passed to `eval`, quickly failing if not of the form `swap x y z`.
The expressions for numerals `x y z` are converted to `nat`, and then compared.
Based on equality of these `nat`s, equality proofs are generated using either
`equiv.swap_apply_left`, `equiv.swap_apply_right`, or `swap_apply_of_ne_of_ne`.
-/

open equiv tactic expr

open norm_num

namespace norm_swap

/--
A `norm_num` plugin for normalizing `equiv.swap a b c` where `a b c : ℕ` are numerals.

```
example : equiv.swap 1 2 1 = 2 := by norm_num
```
-/
@[norm_num] meta def eval : expr → tactic (expr × expr) := λ e, do
  (swapt, coe_fn_inst, fexpr, c) ← e.match_app_coe_fn <|> fail "did not get an app coe_fn expr",
  guard (fexpr.get_app_fn.const_name = ``equiv.swap) <|> fail "coe_fn not of equiv.swap",
  [α, deceq_inst, a, b] ← pure fexpr.get_app_args <|> fail "swap did not have exactly two args applied",
  na ← a.to_rat,
  nb ← b.to_rat,
  nc ← c.to_rat,
  if ha : nc = na
    then do
      let p : expr := `(@swap_apply_left.{1} %%α %%deceq_inst %%a %%b),
      pure (b, p)
  else if hb : nc = nb
    then do
      let p : expr := `(@swap_apply_right.{1} %%α %%deceq_inst %%a %%b),
      pure (a, p)
  else do
    nic ← mk_instance_cache α,
    (_, hca) ← (prove_ne nic c a nc na), -- this will fail on `fin n`
    (_, hcb) ← (prove_ne nic c b nc nb),
    let p : expr := `(@swap_apply_of_ne_of_ne.{1} %%α %%deceq_inst %%a %%b %%c %%hca %%hcb),
    pure (c, p)

end norm_swap
