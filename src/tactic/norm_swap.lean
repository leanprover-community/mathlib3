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

/--
Creates the application `n c.α p l`, where `p` is a type class instance found in the cache `c`,
but works on `c.α : Sort*` instead of how `mk_app` uses `c.α : Type*`.
-/
meta def tactic.instance_cache.mk_sorted_app (c : instance_cache) (n : name) (l : list expr) :
  tactic (instance_cache × expr) :=
do d ← get_decl n,
   (c, l) ← instance_cache.append_typeclasses d.type.binding_body c l,
   return (c, (const n [c.univ.succ]).mk_app (c.α :: l))

open norm_num

namespace norm_swap

/--
A tactic for normalizing `equiv.swap a b c` where `a b c : ℕ` are numerals.

```
example : equiv.swap 1 2 1 = 2 := by norm_num
```
-/
@[norm_num] meta def eval : expr → tactic (expr × expr) := λ e, do
  (swapt, coe_fn_inst, fexpr, c) ← e.match_app_coe_fn <|> fail "did not get an app coe_fn expr",
  guard (fexpr.get_app_fn.const_name = ``equiv.swap) <|> fail "coe_fn not of equiv.swap",
  [α, deceq_inst, a, b] ← pure fexpr.get_app_args <|> fail "swap did not have exactly two args applied",
  unify α `(ℕ) <|> fail "currently, norm_swap supports only ℕ",
  dic ← mk_instance_cache α,
  na ← a.to_nat,
  nb ← b.to_nat,
  nc ← c.to_nat,
  if ha : nc = na
    then do
      (dic, p) ← dic.mk_sorted_app ``swap_apply_left [a, b],
      pure (b, p)
  else if hb : nc = nb
    then do
      (dic, p) ← dic.mk_sorted_app ``swap_apply_right [a, b],
      pure (a, p)
  else do
    nic ← mk_instance_cache `(ℕ), -- our `na, nb, nc` are now in Nat
    (_, hca) ← (prove_ne nic c a nc na),
    (_, hcb) ← (prove_ne nic c b nc nb),
    (dic, p) ← dic.mk_sorted_app ``swap_apply_of_ne_of_ne [a, b, c, hca, hcb],
    pure (c, p)

end norm_swap
