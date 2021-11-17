/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import tactic.core
import tactic.push_neg

/-!
# by_contra'

`by_contra'` is a tactic for proving propositions by contradiction.
It is similar to `by_contra` except that it also uses `push_neg` to normalize negations.
-/

namespace tactic
namespace interactive
setup_tactic_parser

/--
If the target of the main goal is a proposition `p`,
`by_contra'` reduces the goal to proving `false` using the additional hypothesis `h : ¬ p`.
`by_contra' h` can be used to name the hypothesis `h : ¬ p`.
The hypothesis `¬ p` will be negation normalized using `push_neg`.
For instance, `¬ a < b` will be changed to `b ≤ a`.
`by_contra' h : q` will normalize negations in `¬ p`, normalize negations in `q`,
and then check that the two normalized forms are equal.
The resulting hypothesis is the pre-normalized form, `q`.

If the name `h` is not explicitly provided, then `this` will be used as name.

This tactic uses classical reasoning.
It is a variant on the tactic `by_contra` (`tactic.interactive.by_contra`).

Examples:

```lean
example : 1 < 2 :=
begin
  by_contra' h,
  -- h : 2 ≤ 1 ⊢ false
end

example : 1 < 2 :=
begin
  by_contra' h : ¬ 1 < 2,
  -- h : ¬ 1 < 2 ⊢ false
end
```
-/
meta def by_contra' (h : parse ident?) (t : parse (tk ":" *> texpr)?) : tactic unit := do
  let h := h.get_or_else `this,
  tgt ← target,
  mk_mapp `classical.by_contradiction [some tgt] >>= tactic.eapply,
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
