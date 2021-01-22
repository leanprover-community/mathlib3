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

namespace norm_fin

/-- If `a b : fin n`, then `prove_le_fin a b` proves `a ≠ b`. -/
meta def prove_ne_fin : expr → expr → tactic expr
| a b  := norm_fin.eval_rel a b $ λ n a' b' na nb,
  if na = nb then failure
  else if na < nb then do
    p ← norm_fin.prove_lt_fin' n a b a' b',
    pure $ `(@ne_of_lt (fin %%n) _).mk_app [a, b, p]
  else do
    p ← norm_fin.prove_lt_fin' n b a b' a',
    pure $ `(@ne_of_gt (fin %%n) _).mk_app [a, b, p]

end norm_fin

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
  if nc = na
    then let p : expr := `(@swap_apply_left.{1} %%α %%deceq_inst %%a %%b) in pure (b, p)
  else if nc = nb
    then let p : expr := `(@swap_apply_right.{1} %%α %%deceq_inst %%a %%b) in pure (a, p)
  else do
    nic ← mk_instance_cache α,
    hca ← (prod.snd <$> prove_ne nic c a nc na) <|> norm_fin.prove_ne_fin c a,
    hcb ← (prod.snd <$> prove_ne nic c b nc nb) <|> norm_fin.prove_ne_fin c b,
    let p : expr := `(@swap_apply_of_ne_of_ne.{1} %%α %%deceq_inst %%a %%b %%c %%hca %%hcb),
    pure (c, p)

end norm_swap
