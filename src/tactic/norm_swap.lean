/-
Copyright (c) 2021 Yakov Pechersky All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.equiv.basic
import tactic.norm_fin

/-!
# `norm_swap`

Evaluating `swap x y z` for numerals `x y z` that are `ℕ`, `ℤ`, or `ℚ`, via a `norm_num` plugin.
Terms are passed to `eval`, quickly failing if not of the form `swap x y z`.
The expressions for numerals `x y z` are converted to `nat`, and then compared.
Based on equality of these `nat`s, equality proofs are generated using either
`equiv.swap_apply_left`, `equiv.swap_apply_right`, or `swap_apply_of_ne_of_ne`.
-/

open equiv tactic expr

open norm_num

namespace norm_swap

/--
A `norm_num` plugin for normalizing `equiv.swap a b c`
where `a b c` are numerals of `ℕ`, `ℤ`, `ℚ` or `fin n`.

```
example : equiv.swap 1 2 1 = 2 := by norm_num
```
-/
@[norm_num] meta def eval : expr → tactic (expr × expr) := λ e, do
  (swapt, coe_fn_inst, fexpr, c) ← e.match_app_coe_fn <|> fail "did not get an app coe_fn expr",
  guard (fexpr.get_app_fn.const_name = ``equiv.swap) <|> fail "coe_fn not of equiv.swap",
  [α, deceq_inst, a, b] ← pure fexpr.get_app_args <|>
    fail "swap did not have exactly two args applied",
  na ← a.to_rat <|> (do (fa, _) ← norm_fin.eval_fin_num a, fa.to_rat),
  nb ← b.to_rat <|> (do (fb, _) ← norm_fin.eval_fin_num b, fb.to_rat),
  nc ← c.to_rat <|> (do (fc, _) ← norm_fin.eval_fin_num c, fc.to_rat),
  if nc = na then do
    p ← mk_mapp `equiv.swap_apply_left [α, deceq_inst, a, b],
    pure (b, p)
  else if nc = nb then do
    p ← mk_mapp `equiv.swap_apply_right [α, deceq_inst, a, b],
    pure (a, p)
  else do
    nic ← mk_instance_cache α,
    hca ← (prod.snd <$> prove_ne nic c a nc na) <|>
      (do (_, ff, p) ← norm_fin.prove_eq_ne_fin c a, pure p),
    hcb ← (prod.snd <$> prove_ne nic c b nc nb) <|>
      (do (_, ff, p) ← norm_fin.prove_eq_ne_fin c b, pure p),
    p ← mk_mapp `equiv.swap_apply_of_ne_of_ne [α, deceq_inst, a, b, c, hca, hcb],
    pure (c, p)

end norm_swap
