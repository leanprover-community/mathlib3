/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import computability.primrec.basic

/-!
# Tactic for proving functions are in a computational class
(Written only for `primrec` for now, but it is relatively general)
-/

namespace tactic
setup_tactic_parser

@[reducible]
def primrec_key := with_bot name

meta def get_primrec_fun (E : expr) : tactic expr :=
(do `(primrec %%e) ← pure E,
   return e) <|>
(do `(primrec_pred %%e) ← pure E,
   return e)

meta def mk_key_of_expr' (f : expr) : primrec_key :=
if f.is_app then
  let app := f.get_app_fn in
  if app.is_constant then app.const_name else ⊥
else if f.is_constant then f.const_name
else ⊥

meta def mk_key_of_expr (f : expr) : primrec_key :=
if f.is_lambda then mk_key_of_expr' f.lambda_body else mk_key_of_expr' f

meta def mk_key_of_name (f : name) : tactic primrec_key :=
do f' ← mk_const f,
   tp ← infer_type f' >>= instantiate_mvars,
   a ← get_primrec_fun tp.pi_binders.2 |
      fail!"{tp} is not a lemma of the form `primrec f`",
   return (mk_key_of_expr a)

@[user_attribute]
meta def primrec_attr : user_attribute
  (native.rb_lmap primrec_key name) (list primrec_key) :=
{ name  := `primrec
, descr := "Attribute marking a lemma to be used to prove function is primitive recursive"
, cache_cfg :=
  { dependencies := [],
    mk_cache := λ ls,
    do ps ← ls.mmap primrec_attr.get_param,
       pure $ (ps.zip ls).foldl
         (flip $ function.uncurry (λ k n m, k.foldl (λ m' k', m'.insert k' n) m))
         (native.rb_lmap.mk primrec_key _) }
, after_set := some $ λ n prio p,
  do { ks ← primrec_attr.get_param n,
      if ks.length = 0 then do
        when_tracing `primrec_tac trace!"Setting attribute {n}",
        k ← mk_key_of_name n,
        when_tracing `primrec_tac trace!"Using key {k}",
        primrec_attr.set n [k] tt,
        return ()
      else when_tracing `primrec_tac trace!"Using keys {ks}" }
, parser :=
  (functor.map (λ x : name, [x]) ident)
  <|>
  (tk "[" *> sep_by (tk ",") ((coe : name → primrec_key) <$> ident) <* tk "]")
  <|> pure []
 }

/- Given a goal of the form `primrec (λ x, f (a b c [types/instances]) x₁ x₂ .. xₙ)
  split into `primrec (f (a b c ...)` and `primrec (λ x, x₁) ... primrec (λ x, xₙ)`.

  Edge cases: `primrec f` becomes `primrec (λ x, f x)` or `primrec (λ x, f x.1 x.2)` etc.
  We need to detect this cycle

  Steps:
    0. Call `dsimp only`
    1. detect non-lambda functions (i.e. constants/app's with constant fun's),
      try solve using lemma or assumption;
    2. Unfold `primrec` to `primrec1`, then to `primrec`
    3. Take head term, look it up in tree; try those lemmas
    4. Find head term, try using `comp`
  -/

/-- Given `fn` applied to `args`, where `fn` has type `tp`
    - `expr`: `fn` partially applied to `args` which are not encodable
    - `list expr`: the remaining (unconsumed) args
    - `list expr`: the types of the above args
    - `list expr`: a list of `tencodable` instance results corresponding to above -/
meta def app_to_comp : expr → list expr → expr → bool →
  tactic (expr × list expr × list expr × list expr)
| fn (arg :: args) (expr.pi v bi dm body) frozen :=
do
  e ← to_expr ``(tencodable %%dm) >>= instantiate_mvars,
  inst_or_ret ← (sum.inl <$> mk_instance e)
    <|> (do
      guard (¬frozen) <|> fail!"Argument of type {dm} is expected to be tencodable, since not frozen",
      sum.inr <$> app_to_comp (fn.app arg) args (body.instantiate_var arg) ff),
  match inst_or_ret with
  | (sum.inl inst) := do
      (fn_part, rest, rest_tp, insts) ← app_to_comp fn args (body.instantiate_var arg) tt,
      return (fn_part, arg :: rest, dm :: rest_tp, inst :: insts)
  | (sum.inr ret) := pure ret
  end

| fn [] e frozen := pure (fn, [], [], [])
| _ _ _ _ := fail!"Argument provided but not a pi type. Probably bug in tactic."

meta def comp_lemmas : list name :=
[``primrec.const, ``primrec.comp, ``primrec.comp₂, ``primrec.comp₃, ``primrec.comp₄, ``primrec.comp₅]

meta def comp_lemmas_pred : list name :=
[``primrec.const, ``primrec_pred.comp, ``primrec_pred.comp₂]

meta def get_comp_lemma
  (fn_app : expr) (args : list expr)
  (dm_tp : expr) (v : expr)
  (dm_enc : expr) (out_enc : option expr)
  (exclude : list expr) : tactic expr :=
do
  app_tp ← infer_type fn_app,
  (fn_part, rest, rest_tp, insts) ← app_to_comp fn_app args app_tp ff,
  let out_tp := app_tp.instantiate_pis args,
  when_tracing `primrec_tac (do
    trace!"App type: {app_tp}",
    trace!"Applied arguments: {args}",
    trace!"Partially applied term: {fn_part}",
    trace!"Unapplied arguments: {rest}",
    trace!"Unapplied arguments' types: {rest_tp}",
    trace!"Instances: {insts}",
    trace!"Output type: {out_tp}",
    trace!"Excluding: {exclude}"),
  let lemmas : list name := if out_enc.is_some then comp_lemmas else comp_lemmas_pred,
  guard (rest.length < lemmas.length) <|> fail!"Not enough comp lemmas for {fn_app} ({rest.length} arguments)",
  exclude.mall (λ e : expr, bnot <$> succeeds (unify fn_part e reducible)) >>= guardb <|> fail!"Unable to make progress",
  -- Loop through app_tp, which should be of the form (Π α₁, Π α₂, ..., αₙ → α_{n+1} → ... → αₘ → β)
  -- and the args should be `m` expressions which match the types.
  if rest.length = 0 then fail "Unimplemented: special case constants"
  else do
    let lemm : expr := expr.const (lemmas.inth rest.length) [],
    let rest' : list expr := rest.map (λ x, x.bind_lambda v),
    return (lemm.mk_app
      (rest_tp ++ (if out_enc.is_some then [out_tp] else []) ++
      [dm_tp] ++ insts ++ [out_enc, dm_enc].reduce_option ++
        [fn_part] ++ rest'))

/-- The goal is supposed to be `primrec fn@(λ x, _)` where _ is whnf -/
meta def comp_core (fn : expr)
  (dm_enc : expr) (out_enc : option expr)
  (exclude : opt_param (list expr) []) : tactic unit :=
do guard fn.is_lambda <|> fail!"{fn} is not a lambda function",
   v ← mk_local_def fn.binding_name fn.binding_domain,
   let fn_body : expr := (fn.instantiate_lambdas [v]),
   guard fn_body.is_app <|> fail!"{fn_body} is not an application",
   let fn_body_app := fn_body.get_app_fn,
   comp_lemma ← get_comp_lemma fn_body_app fn_body.get_app_args fn.binding_domain v dm_enc out_enc exclude,
   when_tracing `primrec_tac trace!"Final lemma: {comp_lemma}",
   apply comp_lemma {md := reducible},
   return ()

meta def get_goal_fun : tactic expr :=
target >>= get_primrec_fun

meta def get_goal_uncurry_base_fun : tactic (expr × option expr × expr) :=
(do `(@primrec _ _ _ %%dm_enc %%out_enc (@function.has_uncurry_base _ _) %%e) ← target,
   return (dm_enc, out_enc, e)) <|>
(do `(@primrec_pred _ _ %%dm_enc (@function.has_uncurry_base _ _) %%e) ← target,
   return (dm_enc, none, e))

meta def solve_const (e : expr) : tactic unit :=
do let nm := mk_key_of_expr' e,
   guard (nm ≠ ⊥) <|> fail!"Goal {e} not of the form `primrec f`",
   when_tracing `primrec_tac trace!"Looking up {nm}",
   rb ← primrec_attr.get_cache,
   let results := rb.find_def [] nm,
   when_tracing `primrec_tac trace!"Trying {results}",
   solve $ results.map (λ x, mk_const x >>= (λ e, apply e { md := reducible }) >> skip)

meta def solve_apply (e : expr) : tactic unit :=
do guard e.is_lambda <|> fail!"Goal {e} not a lambda function",
   let nm := mk_key_of_expr e,
   when_tracing `primrec_tac trace!"Looking up {nm}",
   rb ← primrec_attr.get_cache,
   let results := (if nm ≠ ⊥ then rb.find_def [] ⊥ else []) ++ rb.find_def [] nm,
   when_tracing `primrec_tac trace!"Trying {results}",
   first $ results.map (λ x, mk_const x >>= λ e, apply e { md := reducible }),
   skip

meta def uncurry_target : tactic unit :=
do fail_if_success get_goal_uncurry_base_fun,
   dsimp_target simp_lemmas.mk [``primrec, ``primrec_pred, ``function.has_uncurry.uncurry, ``id]
  { md := reducible },
   (to_expr ``(primrec1_iff_primrec_pred) >>= rewrite_target) <|>
   (to_expr ``(primrec1_iff_primrec) >>= rewrite_target)

meta def step_computability : tactic unit :=
do dsimp_target simp_lemmas.mk [] { fail_if_unchanged := ff },
   e ← get_goal_fun,
   when_tracing `primrec_tac trace!"Trying to solve {e}",
   (assumption <|> solve_const e >>
    when_tracing `primrec_tac trace!"Solved goal!") <|> (do
    try uncurry_target,
    (dm_enc, out_enc, e') ← get_goal_uncurry_base_fun,
    e'' ← (guard (e'.is_lambda) >> pure e') <|> (head_eta_expand e'),
    (solve_apply e'' >>
      when_tracing `primrec_tac trace!"Made progress using solve_apply") <|>
    (comp_core e'' dm_enc out_enc [e] >>
      when_tracing `primrec_tac trace!"Made progress using comp") <|>
    fail!"No progress could be made"
   )

meta def rw_arg_ext (new_tgt : pexpr) : tactic unit :=
do tgt ← target,
   guard (expr.is_app tgt),
   let arg := expr.app_arg tgt,
   n ← mk_fresh_name,
   to_expr ``(%%arg = %%new_tgt) >>= assert n,
   focus1 (symmetry >> tactic.funext),
   swap,
   resolve_name n >>= to_expr >>= rewrite_target

namespace interactive

meta def primrec (rw_tgt : parse $ (tk "using" *> texpr)?) :
  tactic unit :=
`[simp only [primrec1_iff_primrec, primrec1_iff_primrec_pred', unit_tree.primrec.iff_primrec] { fail_if_unchanged := ff}] >>
rw_tgt.elim skip (λ rw_tgt', rw_arg_ext rw_tgt') >>
repeat1 step_computability


end interactive

end tactic

declare_trace primrec_tac

attribute [primrec]
  primrec.fst
  primrec.snd
  primrec.id
  primrec.const
  primrec.ite

@[primrec] lemma primrec.id' {α : Type} [tencodable α] : primrec (λ x : α, x) :=
primrec.id
