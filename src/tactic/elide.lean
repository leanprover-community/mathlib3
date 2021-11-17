/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon
-/
import tactic.core

namespace tactic
namespace elide

meta def replace : ℕ → expr → tactic expr
| 0 e := do
  t ← infer_type e,
  expr.sort u ← infer_type t,
  return $ (expr.const ``hidden [u]).app t e
| (i+1) (expr.app f x) := do
  f' ← replace (i+1) f,
  x' ← replace i x,
  return (f' x')
| (i+1) (expr.lam n b d e) := do
  d' ← replace i d,
  var ← mk_local' n b d,
  e' ← replace i (expr.instantiate_var e var),
  return (expr.lam n b d' (expr.abstract_local e' var.local_uniq_name))
| (i+1) (expr.pi n b d e) := do
  d' ← replace i d,
  var ← mk_local' n b d,
  e' ← replace i (expr.instantiate_var e var),
  return (expr.pi n b d' (expr.abstract_local e' var.local_uniq_name))
| (i+1) el@(expr.elet n t d e) := do
  t' ← replace i t,
  d' ← replace i d,
  var ← mk_local_def n t,
  e' ← replace i (expr.instantiate_var e var),
  return (expr.elet n t' d' (expr.abstract_local e' var.local_uniq_name))
| (i+1) e := return e

meta def unelide (e : expr) : expr :=
expr.replace e $ λ e n,
match e with
| (expr.app (expr.app (expr.const n _) _) e') :=
  if n = ``hidden then some e' else none
| (expr.app (expr.lam _ _ _ (expr.var 0)) e') := some e'
| _ := none
end

end elide

namespace interactive
setup_tactic_parser

/-- The `elide n (at ...)` tactic hides all subterms of the target goal or hypotheses
beyond depth `n` by replacing them with `hidden`, which is a variant
on the identity function. (Tactics should still mostly be able to see
through the abbreviation, but if you want to unhide the term you can use
`unelide`.) -/
meta def elide (n : parse small_nat) (loc : parse location) : tactic unit :=
loc.apply
  (λ h, do t ← infer_type h >>= tactic.elide.replace n,
           tactic.change_core t (some h))
  (target >>= tactic.elide.replace n >>= tactic.change)

/-- The `unelide (at ...)` tactic removes all `hidden` subterms in the target
types (usually added by `elide`). -/
meta def unelide (loc : parse location) : tactic unit :=
loc.apply
  (λ h,  do t ← infer_type h,
            tactic.change_core (elide.unelide t) (some h))
  (target >>= tactic.change ∘ elide.unelide)

/--
The `elide n (at ...)` tactic hides all subterms of the target goal or hypotheses
beyond depth `n` by replacing them with `hidden`, which is a variant
on the identity function. (Tactics should still mostly be able to see
through the abbreviation, but if you want to unhide the term you can use
`unelide`.)

The `unelide (at ...)` tactic removes all `hidden` subterms in the target
types (usually added by `elide`).
-/
add_tactic_doc
{ name        := "elide / unelide",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.elide, `tactic.interactive.unelide],
  tags        := ["goal management", "context management", "rewriting"] }

end interactive

end tactic
