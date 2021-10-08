/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import tactic.push_neg

/-!
# by_contra'

`by_contra'` is a tactic for proving propositions by contradiction.
It is more flexible then `by_contra` and `by_contradiction`
because it uses `push_neg` to normalize negations.
-/

namespace tactic
namespace interactive
setup_tactic_parser

/--
If the target of the main goal is a proposition `p`,
`by_contra'` reduces the goal to proving `false` using the additional hypothesis `h : ¬ p`.
`by_contra' h` can be used to name the hypothesis `h : ¬ p`.
This tactic will attempt to normalize negations in `¬ p` using `push_neg`.

This tactic uses classical reasoning.

A variant on the tactic `by_contra` (`tactic.interactive.by_contra`).
-/
meta def by_contra' (h : parse ident?) (t : parse (tk ":" *> texpr)?) : tactic unit := do
  let h := h.get_or_else `this,
  tgt ← target,
  mk_mapp `classical.by_contradiction [some tgt] >>= tactic.eapply >> skip,
  h₁ ← tactic.intro h,
  t' ← infer_type h₁,
  -- negation-normalize `t'` to the expression `e'` and get a proof `pr'` of `t' = e'`
  (e', pr') ← push_neg.normalize_negations t' <|> refl_conv t',
  match t with
  | none := () <$ replace_hyp h₁ e' pr'
  | some t := do
    t ← to_expr ``(%%t : Prop),
    -- negation-normalize `t` to the expression `e` and get a proof `pr` of `t = e`
    (e, pr) ← push_neg.normalize_negations t <|> refl_conv t,
    unify e e',
    () <$ (mk_eq_symm pr >>= mk_eq_trans pr' >>= replace_hyp h₁ t)
  end

add_tactic_doc
{ name       := "by_contra'",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.by_contra'],
  tags       := ["logic"] }

end interactive
end tactic
