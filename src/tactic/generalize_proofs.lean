/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import tactic.doc_commands

/-!
# `generalize_proofs`

A simple tactic to find and replace all occurrences of proof terms in the
context and goal with new variables.
-/

namespace tactic

private meta def collect_proofs_in :
  expr → list expr → list name × list expr → tactic (list name × list expr)
| e ctx (ns, hs) :=
let go (tac : list name × list expr → tactic (list name × list expr)) :
  tactic (list name × list expr) :=
do t ← infer_type e,
   mcond (is_prop t) (do
     first (hs.map $ λ h, do
       t' ← infer_type h,
       is_def_eq t t',
       g ← target,
       change $ g.replace (λ a n, if a = e then some h else none),
       return (ns, hs)) <|>
     (let (n, ns) := (match ns with
        | [] := (`_x, [])
        | (n :: ns) := (n, ns)
        end : name × list name) in
      do generalize e n,
         h ← intro n,
         return (ns, h::hs)) <|> return (ns, hs)) (tac (ns, hs)) in
match e with
| (expr.const _ _)   := go return
| (expr.local_const _ _ _ _) := do t ← infer_type e, collect_proofs_in t ctx (ns, hs)
| (expr.mvar _ _ _)  := do t ← infer_type e, collect_proofs_in t ctx (ns, hs)
| (expr.app f x)     :=
  go (λ nh, collect_proofs_in f ctx nh >>= collect_proofs_in x ctx)
| (expr.lam n b d e) :=
  go (λ nh, do
    nh ← collect_proofs_in d ctx nh,
    var ← mk_local' n b d,
    collect_proofs_in (expr.instantiate_var e var) (var::ctx) nh)
| (expr.pi n b d e) := do
  nh ← collect_proofs_in d ctx (ns, hs),
  var ← mk_local' n b d,
  collect_proofs_in (expr.instantiate_var e var) (var::ctx) nh
| (expr.elet n t d e) :=
  go (λ nh, do
    nh ← collect_proofs_in t ctx nh,
    nh ← collect_proofs_in d ctx nh,
    collect_proofs_in (expr.instantiate_var e d) ctx nh)
| (expr.macro m l) :=
  go (λ nh, mfoldl (λ x e, collect_proofs_in e ctx x) nh l)
| _                  := return (ns, hs)
end

/-- Generalize proofs in the goal, naming them with the provided list. -/
meta def generalize_proofs (ns : list name) (loc : interactive.loc) : tactic unit :=
do intros_dep,
  hs ← local_context >>= mfilter is_proof,
  n ← loc.get_locals >>= revert_lst,
  t ← target,
  collect_proofs_in t [] (ns, hs),
  intron n <|> (intros $> ())

open interactive interactive.types lean.parser
local postfix *:9001 := many

namespace interactive
/-- Generalize proofs in the goal, naming them with the provided list.

For example:
```lean
example : list.nth_le [1, 2] 1 dec_trivial = 2 :=
begin
  -- ⊢ [1, 2].nth_le 1 _ = 2
  generalize_proofs h,
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nth_le 1 h = 2
end
```
-/
meta def generalize_proofs : parse ident_* → parse location → tactic unit :=
tactic.generalize_proofs
end interactive

add_tactic_doc
{ name       := "generalize_proofs",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.generalize_proofs],
  tags       := ["context management"] }

end tactic
