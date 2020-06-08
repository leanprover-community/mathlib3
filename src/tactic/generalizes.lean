/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import tactic.core

universes u v w

namespace tactic

open expr

-- Input must be in reverse dependency order!
-- Output constants are also in reverse dependency order.
private meta def generalizes'_aux₁ (md : transparency) (unify : bool)
  : expr → list expr → list (name × expr) → tactic (expr × list expr)
| e cnsts [] := pure (e, cnsts.reverse)
| e cnsts ((n, x) :: xs) := do
  x_type ← infer_type x,
  c ← mk_local' n binder_info.default x_type,
  e ← kreplace e x c md unify,
  cnsts ← cnsts.mmap $ λ c', kreplace c' x c md unify,
  generalizes'_aux₁ e (c :: cnsts) xs

-- Input must be in reverse dependency order!
private meta def generalizes'_aux₂ : expr → list (name × expr × expr) → tactic expr
| e [] := pure e
| e ((eq_name, cnst, arg) :: cs) := do
  cnst_type ← infer_type cnst,
  arg_type ← infer_type arg,
  sort u ← infer_type arg_type,
  let e :=
    pi cnst.local_pp_name binder_info.default cnst_type $
    pi eq_name binder_info.default ((const `heq [u]) cnst_type (var 0) arg_type arg) $
    (e.abstract cnst).lift_vars 0 1,
  generalizes'_aux₂ e cs

meta def generalizes' (args : list (name × name × expr))
  (md := semireducible) (unify := tt) : tactic nat := focus1 $ do
  tgt ← target,
  let args_rev := args.reverse,
  (tgt, cnsts) ← generalizes'_aux₁ md unify tgt []
    (args_rev.map (λ ⟨e_name, _, e⟩, (e_name, e))),
  let args' :=
    @list.map₂ (name × name × expr) expr _
      (λ ⟨x_name, eq_name, x⟩ cnst, (eq_name, cnst, x)) args_rev cnsts,
  tgt ← generalizes'_aux₂ tgt args',
  type_check tgt <|> fail! "TODO",
  n ← mk_fresh_name,
  h ← assert n tgt,
  swap,
  apps ← args.mmap $ λ ⟨_, _, x⟩, do {
    x_type ← infer_type x,
    sort u ← infer_type x_type,
    pure [x, (const `heq.refl [u]) x_type x]
  },
  exact $ h.mk_app apps.join,
  pure $ args.length * 2


namespace interactive

open interactive
open lean.parser

private meta def generalizes_arg_parser : lean.parser (name × name × pexpr) :=
with_desc "id : expr = id" $ do
  hyp_name ← ident,
  tk ":",
  arg ← lean.parser.pexpr 0,
  (arg, arg_name) ←
    match arg with
    | (app (app (macro _ [const `eq _ ]) e) (local_const x _ _ _)) := pure (e, x)
    | _ := failure
    end,
  pure $ (arg_name, hyp_name, arg)

private meta def generalizes_args_parser
  : lean.parser (list (name × name × pexpr)) :=
with_desc "[id : expr = id, ...]" $
  tk "[" *> sep_by (tk ",") generalizes_arg_parser <* tk "]"

meta def generalizes (args : parse generalizes_args_parser) : tactic unit := do
  args ← args.mmap $ λ ⟨arg_name, hyp_name, arg⟩, do {
    arg ← to_expr arg,
    pure (arg_name, hyp_name, arg)
  },
  propagate_tags $ do {
    n ← generalizes' args,
    intron n,
    pure ()
  },
  pure ()

end interactive
end tactic
