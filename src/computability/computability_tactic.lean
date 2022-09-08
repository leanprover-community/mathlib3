/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import computability.primrec.basic

/-!
# Tactic for proving functions are in a computational class

-/

namespace tactic

@[reducible]
def primrec_key := with_bot name

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
   `(primrec %%a) ← pure tp.pi_binders.2 |
      fail!"{tp} is not a lemma of the form `primrec f`",
   return (mk_key_of_expr a)

@[user_attribute]
meta def primrec_attr : user_attribute
  (native.rb_lmap primrec_key name) (option primrec_key) :=
{ name  := `primrec
, descr := "Attribute marking a lemma to be used to prove function is primitive recursive"
, cache_cfg :=
  { dependencies := [],
    mk_cache := λ ls,
    do ps ← ls.mmap primrec_attr.get_param,
       let ps := ps.reduce_option,
       pure $ (ps.zip ls).foldl
         (flip $ function.uncurry (λ k n m, m.insert k n))
         (native.rb_lmap.mk primrec_key _) }
, after_set := some $ λ n prio p,
  do { none ← primrec_attr.get_param n | pure (),
      when_tracing `primrec_tac trace!"Setting attribute {n}",
      k ← mk_key_of_name n,
      when_tracing `primrec_tac trace!"Using key {k}",
      primrec_attr.set n (some k) tt,
      return () }
, parser := some (none : option primrec_key) }

/- In order to help resolve propositions (which are converted to bool's),
  we simplify -/
meta def simp_to_bool : tactic unit :=
`[simp only [bool.to_bool_not, bool.to_bool_and, bool.to_bool_or, bool.to_bool_coe] { eta := ff }]

/- Given a goal of the form `primrec (λ x, f (a b c [types/instances]) x₁ x₂ .. xₙ)
  split into `primrec (f (a b c ...)` and `primrec (λ x, x₁) ... primrec (λ x, xₙ)`.

  Edge cases: `primrec f` becomes `primrec (λ x, f x)` or `primrec (λ x, f x.1 x.2)` etc.
  We need to detect this cycle

  Steps:
    0. Call `dsimp only` (or just `whnf`?), ensure no lambda terms in head
    0.5. Try `id` and `const`
    1. detect non-lambda functions (i.e. constants/app's with constant fun's),
      try solve using tree or assumption;
    2. Unfold `primrec` to `primrec1`, then to `primrec`
    3. Find head term, try using `comp`
    4. Take head term, look it up in tree; try those lemmas
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

meta def get_comp_lemma
  (fn_app : expr) (args : list expr)
  (dm_tp : expr) (v : expr)
  (dm_enc : expr) (out_enc : expr)
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
  guard (rest.length < comp_lemmas.length) <|> fail!"Not enough comp lemmas for {fn_app} ({rest.length} arguments)",
  exclude.mall (λ e : expr, bnot <$> succeeds (unify fn_part e reducible)) >>= guardb <|> fail!"Unable to make progress",
  -- Loop through app_tp, which should be of the form (Π α₁, Π α₂, ..., αₙ → α_{n+1} → ... → αₘ → β)
  -- and the args should be `m` expressions which match the types.
  if rest.length = 0 then fail "Unimplemented: special case constants"
  else do
    lemm : expr ← mk_const (comp_lemmas.inth rest.length),
    let rest' : list expr := rest.map (λ x, x.bind_lambda v),
    return (lemm.mk_app
      (rest_tp ++ [out_tp, dm_tp] ++ insts ++ [out_enc, dm_enc] ++
        [fn_part] ++ rest'))

/-- The goal is supposed to be `primrec fn@(λ x, _)` where _ is whnf -/
meta def comp_core (fn : expr)
  (dm_enc : expr) (out_enc : expr)
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
do `(primrec %%e) ← target,
   return e

meta def get_goal_uncurry_base_fun : tactic (expr × expr × expr) :=
do `(@primrec _ _ _ %%dm_enc %%out_enc (@function.has_uncurry_base _ _) %%e) ← target,
   return (dm_enc, out_enc, e)

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

meta def step_computability : tactic unit :=
do dsimp_target simp_lemmas.mk [] { fail_if_unchanged := ff },
   e ← get_goal_fun,
   when_tracing `primrec_tac trace!"Trying to solve {e}",
   (assumption <|> solve_const e >>
    when_tracing `primrec_tac trace!"Solved goal!") <|> (do
    dsimp_target simp_lemmas.mk [``primrec, ``function.has_uncurry.uncurry, ``id],
    to_expr ``(primrec1_iff_primrec) >>= rewrite_target,
    (dm_enc, out_enc, e') ← get_goal_uncurry_base_fun,
    e'' ← (guard (e'.is_lambda) >> pure e') <|> (head_eta_expand e'),
    (solve_apply e'' >>
      when_tracing `primrec_tac trace!"Made progress using solve_apply") <|>
    (comp_core e'' dm_enc out_enc [e] >>
      when_tracing `primrec_tac trace!"Made progress using comp")
   )

namespace interactive

end interactive

end tactic

declare_trace primrec_tac

attribute [primrec] primrec.fst
attribute [primrec] primrec.snd
attribute [primrec] primrec.id
attribute [primrec] primrec.const

@[primrec] lemma primrec.id' {α : Type*} [tencodable α] : primrec (λ x : α, x) :=
primrec.id

@[primrec] lemma primrec.prod_mk {α β : Type*} [tencodable α] [tencodable β] :
  primrec (@prod.mk α β) := primrec.id
