/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import tactic.interactive

/-!
# Swap bound variable tactic

This files defines a tactic `swap_var` whose main purpose is to be a weaker
version of `wlog` that juggles bound names.

It is a helper around the core tactic `rename`.

* `swap_var old new` renames all names named `old` to `new` and vice versa in the goal
  and all hypotheses.

```lean
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
begin
  split,
  work_on_goal 1 { swap_var [P Q] },
  all_goals { exact ‹P› }
end
```

# See also
* `rename`
* `rename_vars`

## Tags

tactic

-/

namespace tactic.interactive

setup_tactic_parser

private meta def swap_arg_parser : lean.parser (name × name) :=
  prod.mk <$> ident <*> (optional (tk "<->" <|> tk "↔") *> ident)

private meta def swap_args_parser : lean.parser (list (name × name)) :=
  (functor.map (λ x, [x]) swap_arg_parser)
  <|>
  (tk "[" *> sep_by (tk ",") swap_arg_parser <* tk "]")

meta def swap_var (renames : parse swap_args_parser) : tactic unit := do
  renames.mmap' (λ e, do
    n ← tactic.get_unused_name,
    -- how to call `interactive.tactic.rename` here?
    propagate_tags $ tactic.rename_many $ native.rb_map.of_list [(e.1, n), (e.2, e.1)],
    propagate_tags $ tactic.rename_many $ native.rb_map.of_list [(n, e.2)]),
  pure ()

end tactic.interactive
