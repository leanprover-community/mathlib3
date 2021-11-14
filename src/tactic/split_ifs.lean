/-
Copyright (c) 2018 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner

Tactic to split if-then-else-expressions.
-/
import tactic.hint

open expr tactic

namespace tactic
setup_tactic_parser

meta def find_if_cond : expr → option expr | e :=
e.fold none $ λ e _ acc, acc <|> do
c ← match e with
| `(@ite _ %%c %%_ _ _) := some c
| `(@dite _ %%c %%_ _ _) := some c
| _ := none
end,
guard ¬c.has_var,
find_if_cond c <|> return c

meta def find_if_cond_at (at_ : loc) : tactic (option expr) := do
lctx ← at_.get_locals, lctx ← lctx.mmap infer_type, tgt ← target,
let es := if at_.include_goal then tgt::lctx else lctx,
return $ find_if_cond $ es.foldr app (default expr)

run_cmd mk_simp_attr `split_if_reduction
run_cmd add_doc_string `simp_attr.split_if_reduction "Simp set for if-then-else statements"

attribute [split_if_reduction] if_pos if_neg dif_pos dif_neg

meta def reduce_ifs_at (at_ : loc) : tactic unit := do
sls ← get_user_simp_lemmas `split_if_reduction,
let cfg : simp_config := { fail_if_unchanged := ff },
let discharger := assumption <|> (applyc `not_not_intro >> assumption),
hs ← at_.get_locals, hs.mmap' (λ h, simp_hyp sls [] h cfg discharger >> skip),
when at_.include_goal (simp_target sls [] cfg discharger >> skip)

meta def split_if1 (c : expr) (n : name) (at_ : loc) : tactic unit :=
by_cases c n; reduce_ifs_at at_

private meta def get_next_name (names : ref (list name)) : tactic name := do
ns ← read_ref names,
match ns with
| [] := get_unused_name `h
| n::ns := do write_ref names ns, return n
end

private meta def value_known (c : expr) : tactic bool := do
lctx ← local_context, lctx ← lctx.mmap infer_type,
return $ c ∈ lctx ∨ `(¬%%c) ∈ lctx

private meta def split_ifs_core (at_ : loc) (names : ref (list name)) :
  list expr → tactic unit | done := do
some cond ← find_if_cond_at at_ | fail "no if-then-else expressions to split",
let cond := match cond with `(¬%%p) := p | p := p end,
if cond ∈ done then skip else do
no_split ← value_known cond,
if no_split then
    reduce_ifs_at at_; try (split_ifs_core (cond :: done))
else do
    n ← get_next_name names,
    split_if1 cond n at_; try (split_ifs_core (cond :: done))

meta def split_ifs (names : list name) (at_ : loc := loc.ns [none]) :=
using_new_ref names $ λ names, split_ifs_core at_ names []

namespace interactive
open interactive interactive.types expr lean.parser

/-- Splits all if-then-else-expressions into multiple goals.

Given a goal of the form `g (if p then x else y)`, `split_ifs` will produce
two goals: `p ⊢ g x` and `¬p ⊢ g y`.

If there are multiple ite-expressions, then `split_ifs` will split them all,
starting with a top-most one whose condition does not contain another
ite-expression.

`split_ifs at *` splits all ite-expressions in all hypotheses as well as the goal.

`split_ifs with h₁ h₂ h₃` overrides the default names for the hypotheses.
-/
meta def split_ifs (at_ : parse location) (names : parse with_ident_list) : tactic unit :=
tactic.split_ifs names at_

add_hint_tactic "split_ifs"

add_tactic_doc
{ name := "split_ifs",
  category := doc_category.tactic,
  decl_names := [``split_ifs],
  tags := ["case bashing"] }

end interactive

end tactic
