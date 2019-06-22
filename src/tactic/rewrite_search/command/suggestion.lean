import tactic.where

-- Import the `@[suggest]` attribute definition, since we emit code which uses it.
import tactic.rewrite_search.discovery.suggest

open lean.parser interactive

open tactic.rewrite_search.discovery

@[user_command]
meta def suggestion_cmd (d : decl_meta_info) (_ : parse $ tk "suggestion") : lean.parser unit := do
  bn ← opt_single_or_list ident,
  -- Implement option parsing here, e.g:
  -- tgt ← optional (tk "at" *> ident),
  pfx ← get_namespace,
  of_tactic' $ do
    sfx ← tactic.mk_user_fresh_name,
    let n := pfx ++ sfx,
    tactic.add_meta_definition n [] `(list name) (reflect bn).to_expr,
    user_attribute.set suggest_attr n [] tt
