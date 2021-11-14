/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.core

/-!
This file provides an alternative implementation for `apply` to fix the so-called "apply bug".

The issue arises when the goals is a Π-type -- whether it is visible or hidden behind a definition.

For instance, consider the following proof:

```
example {α β} (x y z : α → β) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin
  apply le_trans,
end
```

Because `x ≤ z` is definitionally equal to `∀ i, x i ≤ z i`, `apply` will fail. The alternative
definition, `apply'` fixes this. When `apply` would work, `apply` is used and otherwise,
a different strategy is deployed
-/

namespace tactic

/-- With `gs` a list of proof goals, `reorder_goals gs new_g` will use the `new_goals` policy
`new_g` to rearrange the dependent goals to either drop them, push them to the end of the list
or leave them in place. The `bool` values in `gs` indicates whether the goal is dependent or not. -/
def reorder_goals {α} (gs : list (bool × α)) : new_goals → list α
| new_goals.non_dep_first :=
  let ⟨dep,non_dep⟩ := gs.partition (coe ∘ prod.fst) in
  non_dep.map prod.snd ++ dep.map prod.snd
| new_goals.non_dep_only := (gs.filter (coe ∘ bnot ∘ prod.fst)).map prod.snd
| new_goals.all := gs.map prod.snd

private meta def has_opt_auto_param_inst_for_apply (ms : list (name × expr)) : tactic bool :=
ms.mfoldl
 (λ r m, do type ← infer_type m.2,
            b ← is_class type,
            return $ r || type.is_napp_of `opt_param 2 || type.is_napp_of `auto_param 2 || b)
 ff

private meta def try_apply_opt_auto_param_instance_for_apply (cfg : apply_cfg)
  (ms : list (name × expr)) : tactic unit :=
mwhen (has_opt_auto_param_inst_for_apply ms) $ do
  gs ← get_goals,
  ms.mmap' (λ m, mwhen (bnot <$> (is_assigned m.2)) $
                   set_goals [m.2] >>
                   try apply_instance >>
                   when cfg.opt_param (try apply_opt_param) >>
                   when cfg.auto_param (try apply_auto_param)),
  set_goals gs

private meta def retry_apply_aux :
  Π (e : expr) (cfg : apply_cfg), list (bool × name ×  expr) → tactic (list (name × expr))
| e cfg gs :=
focus1 (do {
     tgt : expr ← target, t ← infer_type e,
     unify t tgt,
     exact e,
     gs' ← get_goals,
     let r := reorder_goals gs.reverse cfg.new_goals,
     set_goals (gs' ++ r.map prod.snd),
     return r }) <|>
do (expr.pi n bi d b) ← infer_type e >>= whnf | apply_core e cfg,
   v ← mk_meta_var d,
   let b := b.has_var,
   e ← head_beta $ e v,
   retry_apply_aux e cfg ((b, n, v) :: gs)

private meta def retry_apply (e : expr) (cfg : apply_cfg) : tactic (list (name × expr)) :=
apply_core e cfg <|> retry_apply_aux e cfg []

/-- `apply'` mimics the behavior of `apply_core`. When
`apply_core` fails, it is retried by providing the term with meta
variables as additional arguments. The meta variables can then
become new goals depending on the `cfg.new_goals` policy.

`apply'` also finds instances and applies opt_params and auto_params. -/
meta def apply' (e : expr) (cfg : apply_cfg := {}) : tactic (list (name × expr)) :=
do r ← retry_apply e cfg,
   try_apply_opt_auto_param_instance_for_apply cfg r,
   return r

/-- Same as `apply'` but __all__ arguments that weren't inferred are added to goal list. -/
meta def fapply' (e : expr) : tactic (list (name × expr)) :=
apply' e {new_goals := new_goals.all}
/-- Same as `apply'` but only goals that don't depend on other goals are added to goal list. -/
meta def eapply' (e : expr) : tactic (list (name × expr)) :=
apply' e {new_goals := new_goals.non_dep_only}

/-- `relation_tactic` finds a proof rule for the relation found in the goal and uses `apply'`
to make one proof step. -/
private meta def relation_tactic (md : transparency) (op_for : environment → name → option name)
  (tac_name : string) : tactic unit :=
do tgt   ← target >>= instantiate_mvars,
   env   ← get_env,
   let r := expr.get_app_fn tgt,
   match op_for env (expr.const_name r) with
   | (some refl) := do r ← mk_const refl,
                       retry_apply r {md := md, new_goals := new_goals.non_dep_only },
                       return ()
   | none        := fail $ tac_name ++
     " tactic failed, target is not a relation application with the expected property."
   end

/-- Similar to `reflexivity` with the difference that `apply'` is used instead of `apply` -/
meta def reflexivity' (md := semireducible) : tactic unit :=
relation_tactic md environment.refl_for "reflexivity"

/-- Similar to `symmetry` with the difference that `apply'` is used instead of `apply` -/
meta def symmetry' (md := semireducible) : tactic unit :=
relation_tactic md environment.symm_for "symmetry"

/-- Similar to `transitivity` with the difference that `apply'` is used instead of `apply` -/
meta def transitivity' (md := semireducible) : tactic unit :=
relation_tactic md environment.trans_for "transitivity"

namespace interactive

setup_tactic_parser

/--
Similarly to `apply`, the `apply'` tactic tries to match the current goal against the conclusion
of the type of term.

It differs from `apply` in that it does not unfold definition in order to find out what the
assumptions of the provided term is. It is especially useful when defining relations on function
spaces (e.g. `≤`) so that rules like transitivity on `le : (α → β) → (α → β) → (α → β)` will be
considered to have three parameters and two assumptions (i.e. `f g h : α → β`, `H₀ : f ≤ g`,
`H₁ : g ≤ h`) instead of three parameters, two assumptions and then one more parameter
(i.e. `f g h : α → β`, `H₀ : f ≤ g`, `H₁ : g ≤ h`, `x : α`). Whereas `apply` would expect the goal
`f x ≤ h x`, `apply'` will work with the goal `f ≤ h`.
-/
meta def apply' (q : parse texpr) : tactic unit :=
concat_tags (do h ← i_to_expr_for_apply q, tactic.apply' h)

/--
Similar to the `apply'` tactic, but does not reorder goals.
-/
meta def fapply' (q : parse texpr) : tactic unit :=
concat_tags (i_to_expr_for_apply q >>= tactic.fapply')

/--
Similar to the `apply'` tactic, but only creates subgoals for non-dependent premises that have not
been fixed by type inference or type class resolution.
-/
meta def eapply' (q : parse texpr) : tactic unit :=
concat_tags (i_to_expr_for_apply q >>= tactic.eapply')

/--
Similar to the `apply'` tactic, but allows the user to provide a `apply_cfg` configuration object.
-/
meta def apply_with' (q : parse parser.pexpr) (cfg : apply_cfg) : tactic unit :=
concat_tags (do e ← i_to_expr_for_apply q, tactic.apply' e cfg)

/--
Similar to the `apply'` tactic, but uses matching instead of unification.
`mapply' t` is equivalent to `apply_with' t {unify := ff}`
-/
meta def mapply' (q : parse texpr) : tactic unit :=
concat_tags (do e ← i_to_expr_for_apply q, tactic.apply' e {unify := ff})


/--
Similar to `reflexivity` with the difference that `apply'` is used instead of `apply`.
-/
meta def reflexivity' : tactic unit :=
tactic.reflexivity'

/--
Shorter name for the tactic `reflexivity'`.
-/
meta def refl' : tactic unit :=
tactic.reflexivity'

/--
`symmetry'` behaves like `symmetry` but also offers the option `symmetry' at h` to apply symmetry
to assumption `h`
-/
meta def symmetry' : parse location → tactic unit
| l@loc.wildcard := l.try_apply symmetry_hyp tactic.symmetry'
| (loc.ns hs) := (loc.ns hs.reverse).apply symmetry_hyp tactic.symmetry'

/--
Similar to `transitivity` with the difference that `apply'` is used instead of `apply`.
-/
meta def transitivity' (q : parse texpr?) : tactic unit :=
tactic.transitivity' >> match q with
| none := skip
| some q :=
  do (r, lhs, rhs) ← target_lhs_rhs,
     t ← infer_type lhs,
     i_to_expr ``(%%q : %%t) >>= unify rhs
end

end interactive

end tactic
