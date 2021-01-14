/-
Copyright (c) 2021 Yakov Pechersky All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.equiv.basic
import meta.expr
import tactic.norm_num
import tactic.fin_meta_defs

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

namespace norm_fin

lemma fin.prove_succ (m n k l : ℕ) (hl : l < n) (hk : k < m) (h : m = n + 1) (h' : k = l + 1) :
  fin.succ (⟨l, hl⟩ : fin n) = (⟨k, hk⟩ : fin m) :=
begin
  cases n,
  { exact absurd hl (not_lt_of_le l.zero_le) },
  subst h,
  subst h',
  simp [fin.eq_iff_veq, fin.add_def, nat.mod_eq_of_lt hk],
end

/--
A `norm_num` plugin for normalizing `fin.succ k` where `k` are numerals.

```
example : (5 : fin 7) = fin.succ (fin.succ 3) := by norm_num
```
-/
@[norm_num] meta def eval : expr → tactic (expr × expr)
| `(@fin.succ %%en %%e) := do
  n ← en.to_nat,
  fk ← e.to_fin n,
  ic ← mk_instance_cache `(ℕ),
  (_, ek) ← ic.of_nat fk,
  (_, ltkn) ← prove_lt_nat ic ek en,
  (_, _, en', pn) ← prove_nat_succ ic `(nat.succ %%en),
  (_, _, ek', pk) ← prove_nat_succ ic `(nat.succ %%ek),
  (_, ltkn') ← prove_lt_nat ic ek' en',
  ty ← to_expr ``(fin %%en'),
  fk' ← ty.of_fin (fk + 1),
  pure (fk', `(fin.prove_succ %%en' %%en %%ek' %%ek %%ltkn %%ltkn' %%pn %%pk))
| _ := failed

end norm_fin

namespace norm_swap

/--
A `norm_num` plugin for normalizing `equiv.swap a b c`
where `a b c` are numerals of `ℕ`, `ℤ`, or `ℚ`.

```
example : equiv.swap 1 2 1 = 2 := by norm_num
```
-/
@[norm_num] meta def eval : expr → tactic (expr × expr) := λ e, do
  (swapt, coe_fn_inst, fexpr, c) ← e.match_app_coe_fn <|> fail "did not get an app coe_fn expr",
  guard (fexpr.get_app_fn.const_name = ``equiv.swap) <|> fail "coe_fn not of equiv.swap",
  [α, deceq_inst, a, b] ← pure fexpr.get_app_args <|>
    fail "swap did not have exactly two args applied",
  na ← a.to_rat,
  nb ← b.to_rat,
  nc ← c.to_rat,
  if nc = na
    then let p : expr := `(@swap_apply_left.{1} %%α %%deceq_inst %%a %%b) in pure (b, p)
  else if nc = nb
    then let p : expr := `(@swap_apply_right.{1} %%α %%deceq_inst %%a %%b) in pure (a, p)
  else do
    nic ← mk_instance_cache α,
    (_, hca) ← (prove_ne nic c a nc na), -- this will fail on `fin n`
    (_, hcb) ← (prove_ne nic c b nc nb),
    let p : expr := `(@swap_apply_of_ne_of_ne.{1} %%α %%deceq_inst %%a %%b %%c %%hca %%hcb),
    pure (c, p)

end norm_swap
