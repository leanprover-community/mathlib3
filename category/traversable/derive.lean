/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Automation to construct `traversable` instances
-/

import category.traversable.basic category.traversable.instances category.basic data.list.basic
import tactic.basic tactic.cache

namespace tactic.interactive

open tactic list monad functor

meta def fill_implicit_arg' : expr → expr → tactic expr
| f (expr.pi n bi d b) :=
if b.has_var then
do v ← mk_meta_var d,
   fill_implicit_arg' (expr.app f v) (b.instantiate_var v)
else return f
| e _ := return e

meta def fill_implicit_arg (n : name) : tactic expr :=
do c ← mk_const n,
   t ← infer_type c,
   fill_implicit_arg' c t

meta def mk_down (e : expr) : tactic expr :=
mk_app ``ulift.down [e] <|> pure e

/-- similar to `nested_traverse` but for `functor` -/
meta def nested_map (f v : expr) : expr → tactic expr
| t :=
do t ← instantiate_mvars t,
   mcond (succeeds $ is_def_eq t v)
      (pure f)
      (if ¬ v.occurs (t.app_fn)
          then do
            cl ← mk_app ``functor [t.app_fn],
            _inst ← mk_instance cl,
            f' ← nested_map t.app_arg,
            mk_mapp ``functor.map [t.app_fn,_inst,none,none,f']
          else fail format!"type {t} is not a functor with respect to variable {v}")

/-- similar to `traverse_field` but for `functor` -/
meta def map_field (n : name) (cl f α β e : expr) : tactic expr :=
do t ← infer_type e >>= whnf,
   if t.get_app_fn.const_name = n
   then trace (β.instantiate_local α.local_uniq_name t) >> trace_state >> fail "recursive types not supported"
   else if α.occurs t
   then do f' ← nested_map f α t,
           pure $ f' e
   else
         (is_def_eq t.app_fn cl >> mk_app ``comp.mk [e])
     <|> pure e

/-- similar to `traverse_constructor` but for `functor` -/
meta def map_constructor (c n : name) (f α β : expr) (args : list expr) : tactic unit :=
do g ← target,
   (args,rec_call) ← args.mpartition $ λ e, (bnot ∘ β.occurs) <$> infer_type e,
   let args₀ := args.take $ args.length - rec_call.length,
   args' ← mmap (map_field n g.app_fn f α β) args₀,
   constr ← fill_implicit_arg c,
   let r := constr.mk_app (args' ++ rec_call),
   () <$ tactic.exact r

/-- derive the `map` definition of a `functor` -/
meta def mk_map (type : name) (cs : list name) :=
do [α,β,f,x] ← tactic.intro_lst [`α,`β,`f,`x],
   reset_instance_cache,
   xs ← tactic.induction x,
   () <$ mzip_with'
      (λ (c : name) (x : name × list expr × list (name × expr)),
      solve1 (map_constructor c type f α β x.2.1))
      cs xs

/-- `seq_apply_constructor [x,y,z] f` synthesizes `f <*> x <*> y <*> z` -/
meta def seq_apply_constructor : list expr → expr → tactic expr
| (x :: xs) e := to_expr ``(%%e <*> %%x) >>= seq_apply_constructor xs
| [] e := return e

/-- ``nested_traverse f α (list (array n (list α)))`` synthesizes the expression
`traverse (traverse (traverse f))`. `nested_traverse` assumes that `α` appears in
`(list (array n (list α)))` -/
meta def nested_traverse (f v : expr) : expr → tactic expr
| t :=
do t ← instantiate_mvars t,
   mcond (succeeds $ is_def_eq t v)
      (pure f)
      (if ¬ v.occurs (t.app_fn)
          then do
            cl ← mk_app ``traversable [t.app_fn],
            _inst ← mk_instance cl,
            f' ← nested_traverse t.app_arg,
            mk_mapp ``traversable.traverse [t.app_fn,_inst,none,none,none,none,f']
          else fail format!"type {t} is not traversable with respect to variable {v}")

/--
For a sum type `inductive foo (α : Type) | foo1 : list α → ℕ → foo | ...`
``traverse_field `foo appl_inst f `α `(x : list α)`` synthesizes
`traverse f x` as part of traversing `foo1`. -/
meta def traverse_field (n : name) (appl_inst cl f v e : expr) : tactic expr :=
do t ← infer_type e >>= whnf,
   if t.get_app_fn.const_name = n
   then fail "recursive types not supported"
   else if v.occurs t
   then do f' ← nested_traverse f v t,
           pure $ f' e
   else
         (is_def_eq t.app_fn cl >> mk_app ``comp.mk [e])
     <|> to_expr ``(@pure _ (%%appl_inst).to_has_pure _ (ulift.up %%e))

/--
For a sum type `inductive foo (α : Type) | foo1 : list α → ℕ → foo | ...`
``traverse_constructor `foo1 `foo appl_inst f `α `β [`(x : list α), `(y : ℕ)]``
synthesizes `foo1 <$> traverse f x <*> pure y.` -/
meta def traverse_constructor (c n : name) (appl_inst f α β : expr) (args : list expr) : tactic unit :=
do g ← target,
   (args,rec_call) ← args.mpartition $ λ e, (bnot ∘ β.occurs) <$> infer_type e,
   let args₀ := args.take $ args.length - rec_call.length,
   args' ← mmap (traverse_field n appl_inst g.app_fn f α) args₀,
   constr ← fill_implicit_arg c,
   v ← mk_mvar,
   constr' ← to_expr ``(@pure %%(g.app_fn) (%%appl_inst).to_has_pure _ %%v),
   r ← seq_apply_constructor (args' ++ rec_call) constr',
   gs ← get_goals,
   set_goals [v],
   vs ← tactic.intros >>= mmap mk_down,
   tactic.exact (constr.mk_app vs),
   done,
   set_goals gs,
   () <$ tactic.exact r

/-- derive the `traverse` definition of a `traversable` instance -/
meta def mk_traverse (type : name) (cs : list name) := do
do [m,appl_inst,α,β,f,x] ← tactic.intro_lst [`m,`appl_inst,`α,`β,`f,`x],
   reset_instance_cache,
   xs ← tactic.induction x,
   () <$ mzip_with'
      (λ (c : name) (x : name × list expr × list (name × expr)),
      solve1 (traverse_constructor c type appl_inst f α β x.2.1))
      cs xs

open applicative

meta def derive_functor : tactic unit :=
do `(functor %%f) ← target,
   env ← get_env,
   let n := f.get_app_fn.const_name,
   let cs := env.constructors_of n,
   refine ``( { functor . map := _ , .. } ),
   mk_map n cs

meta def derive_traverse : tactic unit :=
do `(traversable %%f) ← target,
   env ← get_env,
   let n := f.get_app_fn.const_name,
   let cs := env.constructors_of n,
   constructor,
   mk_traverse n cs

meta def mk_one_instance
  (n : name)
  (cls : name)
  (tac : tactic unit) : tactic unit :=
do decl ← get_decl n,
   cls_decl ← get_decl cls,
   env ← get_env,
   guard (env.is_inductive n) <|> fail format!"failed to derive '{cls}', '{n}' is not an inductive type",
   let ls := decl.univ_params.map $ λ n, level.param n,
   -- incrementally build up target expression `Π (hp : p) [cls hp] ..., cls (n.{ls} hp ...)`
   -- where `p ...` are the inductive parameter types of `n`
   let tgt : expr := expr.const n ls,
   ⟨params, _⟩ ← mk_local_pis (decl.type.instantiate_univ_params (decl.univ_params.zip ls)),
   let params := params.init,
   let tgt := tgt.mk_app params,
   tgt ← mk_app cls [tgt],
   tgt ← params.enum.mfoldr (λ ⟨i, param⟩ tgt,
   do -- add typeclass hypothesis for each inductive parameter
      tgt ← do {
        guard $ i < env.inductive_num_params n,
        param_cls ← mk_app cls [param],
        pure $ expr.pi `a binder_info.inst_implicit param_cls tgt
      } <|> pure tgt,
      pure $ tgt.bind_pi param
   ) tgt,
   () <$ mk_instance tgt <|> do
     (_, val) ← tactic.solve_aux tgt (do
       tactic.intros >> tac),
     val ← instantiate_mvars val,
     let trusted := decl.is_trusted ∧ cls_decl.is_trusted,
     add_decl (declaration.defn (n ++ cls)
               decl.univ_params
               tgt val reducibility_hints.abbrev trusted),
     set_basic_attribute `instance (n ++ cls) tt

open function
meta def higher_order_derive_handler
  (cls : name)
  (tac : tactic unit)
  (deps : list (name × tactic unit) := []) :
  derive_handler :=
λ p n,
if p.is_constant_of cls then
do mmap' (uncurry $ mk_one_instance n) deps,
   mk_one_instance n cls tac,
   pure tt
else pure ff

@[derive_handler]
meta def functor_derive_handler :=
higher_order_derive_handler ``functor derive_functor

@[derive_handler]
meta def traversable_derive_handler :=
higher_order_derive_handler ``traversable derive_traverse [(``functor,derive_functor)]

end tactic.interactive
