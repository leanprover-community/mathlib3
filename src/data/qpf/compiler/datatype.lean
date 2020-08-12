import data.qpf.compiler.shape
import .for_mathlib

namespace tactic

open interactive lean lean.parser
open expr

meta def trace' {α} (x : α) [has_to_tactic_format α] : tactic α :=
x <$ trace x

-- #check eq.mpr

meta def mk_constr (mk_fn : name) (d : internal_mvfunctor) : tactic unit :=
trace_scope $
do let my_t := (@const tt d.induct.name d.induct.u_params).mk_app d.params,
   let intl_eq := (@const tt (d.induct.name <.> "shape" <.> "internal_eq") d.induct.u_params).mk_app d.params my_t,
   let params' := d.params.map to_implicit_local_const,
   d.induct.ctors.mmap' $ λ c : type_cnstr,
     do { t ← type_cnstr.type d.induct c,
          let t := instantiate_pi t d.params,
          let c' := c.name.update_prefix (d.decl.to_name <.> "shape"),
          (vs,t') ← mk_local_pis t,
          let mk_shape := ((@const tt c' d.induct.u_params).mk_app d.params my_t).mk_app vs,
          e ← mk_eq_mpr intl_eq mk_shape,
          df ← mk_app mk_fn [e] >>= lambdas' [d.params,vs],
          t ← pis params' t,
          add_decl $ mk_definition c.name d.induct.u_names t df }

meta def mk_destr (dest_fn mk_fn mk_dest_eqn : name) (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
trace_scope $
do let params := d.params.map to_implicit_local_const,
   let my_t := (@const tt d.induct.name d.induct.u_params).mk_app params,
   vec ← mk_live_vec d.vec_lvl (d.live_params ++ [my_t]),
   vec' ← mk_live_vec d.vec_lvl d.live_params,
   let my_shape_t := (@const tt (d.induct.name <.> "shape" <.> "internal") d.induct.u_params).mk_app func.dead_params,
   let u_params := d.induct.u_params,
   let u := fresh_univ d.induct.u_names,
   let intl_eq := (@const tt (d.induct.name <.> "shape" <.> "internal_eq") u_params).mk_app params my_t,
   v_t ← mk_local_def `x (my_shape_t vec),
   C ← mk_local' `C binder_info.implicit (my_t.imp (sort $ level.param u)),
   let n := d.live_params.length,
   C' ← mk_mapp mk_fn [reflect n,my_shape_t,none,none,vec',v_t] >>= lambdas [v_t] ∘ C,
   cs ← d.induct.ctors.mmap $ λ c : type_cnstr,
     do { let t := (@const tt c.name u_params).mk_app params ,
          (vs,_) ← infer_type t >>= mk_local_pis,
          x ← pis vs (C $ t.mk_app vs),
          v ← mk_local_def `v x,
          pure (v) },
   n ← mk_local_def `n my_t,
   n' ← mk_app dest_fn [n],
   let vs := [params,[C,n],cs],
   rec_t ← pis' vs (C n),
   let shape_cases := (@const tt (d.induct.name <.> "shape" <.> "cases_on") $ level.param u :: u_params).mk_app (params ++ [my_t,C',n'] ++ cs),
   shape_cases ← mk_app mk_dest_eqn [n] >>= mk_congr_arg C >>= flip mk_eq_mp shape_cases,
   df ← lambdas' vs shape_cases,
   add_decl $ mk_definition (d.induct.name <.> "cases_on") (u :: d.induct.u_names) rec_t df,
   set_basic_attribute `elab_as_eliminator (d.induct.name <.> "cases_on"),
   pure ()

meta def mk_destr_constr_eqn (dest_mk : name) (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
trace_scope $
do let params := d.params.map to_implicit_local_const,
   let my_t := (@const tt d.induct.name d.induct.u_params).mk_app params,
   let u := fresh_univ d.induct.u_names,
   C ← mk_local' `C binder_info.implicit (my_t.imp (sort $ level.param u)),
   let my_shape_intl_t := (@const tt (d.induct.name <.> "shape" <.> "internal") d.induct.u_params).mk_app $ d.dead_params,
   let my_shape_t := (@const tt (d.induct.name <.> "shape") d.induct.u_params).mk_app params my_t,
   C' ← mk_local' `C binder_info.implicit (my_shape_t.imp (sort $ level.param u)),
   let cases_on := @const tt (d.induct.name <.> "cases_on") (level.param u :: d.induct.u_params),
   let cases_on := cases_on.mk_app params C,
   let shape_cases_on := (@const tt (d.induct.name <.> "shape" <.> "cases_on") (level.param u :: d.induct.u_params)).mk_app params my_t C',
   (_ :: vs,_) ← infer_type cases_on >>= mk_local_pis,
   (c :: vs',_) ← infer_type shape_cases_on >>= mk_local_pis,
   c' ← renew c,
   h ← mk_app `eq [c,c'] >>= mk_local_def `h,
   t ← mk_mapp `heq [none,shape_cases_on.mk_app $ c :: vs',none,shape_cases_on.mk_app $ c' :: vs']
     >>= pis [c,c',h] >>= pis (C' :: vs') >>= pis params,
   (_,cases_congr) ← solve_aux t (intros >> cc),
   (d.induct.ctors.zip vs).mmap' $ λ ⟨ctor,v⟩,
   do { let c := ((@const tt ctor.name d.induct.u_params).mk_app params).mk_app ctor.args,
        eqn ← mk_app `eq [cases_on.mk_app $ c::vs,v.mk_app ctor.args],
        df ← solve_async [params,C::vs,ctor.args] eqn $ do
        { dunfold_target [d.induct.name <.> "cases_on",ctor.name],
          applyc ``mp_eq_of_heq,
          transitivity,
          apply cases_congr,
          applyc dest_mk, reflexivity,
          done },
        t ← pis ctor.args eqn >>= pis (C :: vs) >>= pis (params),
        let n := ((d.induct.name <.> "cases_on").bundle ctor.name),
        add_decl $ declaration.thm n (u :: d.induct.u_names) t df,
        add_eqn_lemmas n,
        simp_attr.pseudo_eqn.set n () tt,
        skip }

open tactic.interactive (rw_rules_t rw_rule)
open tactic.interactive.rw_rules_t
open interactive.rw_rule
open_locale mvfunctor

meta def mk_dep_recursor (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
trace_scope $
do let params := d.params.map to_implicit_local_const,
   let my_shape_intl_t := (@const tt (d.induct.name <.> "shape" <.> "internal") d.induct.u_params).mk_app func.dead_params,
   let u_params := d.induct.u_params,
   vec' ← mk_live_vec d.vec_lvl d.live_params,
   arg ← mk_local_def `y ((@const tt d.induct.name d.induct.u_params).mk_app params),
   C ← pis [arg] d.type >>= mk_local' `C binder_info.implicit,
   X ← mk_app ``sigma [C],
   vec ← mk_live_vec d.vec_lvl (d.live_params ++ [X]),
   let my_shape_t := (@const tt (d.induct.name <.> "shape") d.induct.u_params).mk_app params X,
   v_t ← mk_local_def `x my_shape_t,
   x ← mk_local_def `x' (my_shape_intl_t vec),
   let intl_eq := (@const tt (d.induct.name <.> "shape" <.> "internal_eq") u_params).mk_app params X,
   x' ← mk_eq_mpr intl_eq x,
   C' ← to_expr ``(%%C $ mvqpf.fix.mk (typevec.append_fun typevec.id sigma.fst <$$> %%x')) >>= lambdas [x],
   let cases_on := d.induct.name <.> "shape" <.> "cases_on",
   let cases_u : list level := level.succ d.vec_lvl :: d.induct.u_params,
   let fs := (@const tt cases_on cases_u).mk_app params X C' x',
   (vs,_) ← infer_type fs >>= mk_local_pis,
   vs ← mzip_with (λ l (c : type_cnstr),
     do { (args,t) ← infer_type l >>= mk_local_pis,
          head_beta t >>= pis args >>= mk_local_def l.local_pp_name }) vs d.induct.ctors,
   let fn := fs.mk_app vs,
   rule ← mk_const ``mpr_mpr,
   (t',pr,_) ← infer_type fn >>= head_beta >>= rewrite rule,
   fn ← mk_eq_mp pr fn >>= lambdas [x],
   df ← mk_mapp ``mvqpf.fix.drec [none,my_shape_intl_t,none,none,vec',C,fn,arg]
     >>= lambdas' [params, C :: vs, [arg]],
   t ← infer_type df,
   add_decl $ mk_definition (d.induct.name <.> "drec") d.induct.u_names t df,
   pure ()

meta def mk_recursor (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
trace_scope $
do let my_shape_intl_t := (@const tt (d.induct.name <.> "shape" <.> "internal") d.induct.u_params).mk_app func.dead_params,
   let my_shape_t := (@const tt (d.induct.name <.> "shape") d.induct.u_params).mk_app func.params,
   let u_params := d.induct.u_params,
   let X := to_implicit_local_const func.hole,
   let intl_eq := (@const tt (d.induct.name <.> "shape" <.> "internal_eq") u_params).mk_app d.params X,
   vec' ← mk_live_vec d.vec_lvl d.live_params,
   vec ← mk_live_vec d.vec_lvl (d.live_params ++ [X]),
   x ← mk_local_def `x (my_shape_intl_t vec),
   v_t ← mk_local_def `x my_shape_t,
   C ← lambdas [v_t] X,
   v_t ← mk_eq_mp intl_eq x,
   let cases_on := d.induct.name <.> "shape" <.> "cases_on",
   let cases_u : list level := level.succ d.vec_lvl :: d.induct.u_params,
   let fs := (@const tt cases_on $ cases_u).mk_app func.params C v_t,
   (vs,_) ← infer_type fs >>= mk_local_pis,
   vs ← mzip_with (λ l (c : type_cnstr),
     do { (args,t) ← infer_type l >>= mk_local_pis,
          head_beta t >>= pis args >>= mk_local_def l.local_pp_name }) vs d.induct.ctors,
   fn ← lambdas [x] (fs.mk_app vs),
   arg ← mk_local_def `y $ (@const tt d.induct.name d.induct.u_params).mk_app d.params,
   let params := d.params.map to_implicit_local_const,
   df ← mk_mapp ``mvqpf.fix.rec [none,my_shape_intl_t,none,none,vec',X,fn,arg] >>= lambdas' [params, X :: vs, [arg]],
   t ← infer_type df,
   add_decl $ mk_definition (d.induct.name <.> "rec") d.induct.u_names t df,
   pure ()

meta def mk_corecursor (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
trace_scope $
do -- let u := fresh_univ d.induct.u_names,
   let t := (@const tt d.decl.to_name d.induct.u_params).mk_app d.params,
   let x := func.hole,
   v ← mk_live_vec d.vec_lvl $ d.live_params,
   v' ← mk_live_vec d.vec_lvl $ x :: d.live_params,
   let u_params := d.induct.u_params,
   let n := d.decl.to_name,
   let shape_n := n <.> "shape",
   let internal_eq_n := shape_n <.> "internal_eq",
   let t' := (@const tt (shape_n <.> "internal") d.induct.u_params).mk_app func.dead_params,
   let intl_eq := (@const tt internal_eq_n u_params).mk_app $ d.params,
   let my_fun (rec_n rec_n' : name) (a : expr) := do
   { let ft := imp x $ (@const tt shape_n u_params).mk_app d.params a,
     fn ← mk_local_def `f ft,
     i  ← mk_local_def `i x,
     fn' ← mk_eq_mpr (intl_eq a) (fn i) >>= lambdas [i],
     df ← mk_mapp rec_n [none,t',none,none,v,x,fn'],
     let t := imp x $ (@const tt n u_params).mk_app d.params,
     t ← pis' [d.params, [x,fn]] t,
     df ← lambdas' [d.params, [x,fn]] df,
     add_decl $ mk_definition rec_n' (d.induct.u_names) t df },
   x' ← mk_mapp ``sum [t,x],
   -- my_fun ``mvqpf.cofix.corec₁ (n <.> "corec₁") x',
   my_fun ``mvqpf.cofix.corec' (n <.> "corec'") x',
   my_fun ``mvqpf.cofix.corec (n <.> "corec") x,
   do
   { let rec_n := ``mvqpf.cofix.corec₁,
     let rec_n' := n <.> "corec₁",
     let shape_t := (@const tt shape_n u_params).mk_app d.params,
     `(%%t₂ → _) ← infer_type shape_t,
     X ← mk_local_def `X t₂,
     let ft := shape_t X,
     exit_fn ← mk_local_def `exit_fn (t.imp X),
     rec_fn ← mk_local_def `rec_fn (func.hole.imp X),
     x₀ ← mk_local_def `x₀ x,
     shape_fn ← pis [X,exit_fn,rec_fn,x₀] (shape_t X) >>= mk_local_def `shape_fn,
     df ← mk_mapp rec_n [none,t',none,none,v,x,shape_fn,x₀],
     t ← pis' [d.params, [x,shape_fn,x₀]] t,
     df ← lambdas' [d.params, [x,shape_fn,x₀]] df,
     add_decl $ mk_definition rec_n' (d.induct.u_names) t df,
     pure () },
   pure ()

meta def parse_conjunction_aux : (expr → expr) → expr → expr → dlist expr
| ρ `(true) e := dlist.empty
| ρ `(%%p ∧ %%q) e := parse_conjunction_aux (λ e, @const tt ``and.elim_left [] p q (ρ e)) p e ++ parse_conjunction_aux (λ e, @const tt ``and.elim_right [] p q (ρ e)) q e
| ρ _ e := dlist.singleton $ ρ e

meta def parse_conjunction (e : expr) : tactic $ list expr :=
trace_scope $
do t ← infer_type e >>= instantiate_mvars,
   return (parse_conjunction_aux id t e).to_list

meta def mk_ind (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
trace_scope $
do let my_shape_intl_t := (@const tt (d.induct.name <.> "shape" <.> "internal") d.induct.u_params).mk_app func.dead_params,
   let my_t := (@const tt (d.induct.name) d.induct.u_params).mk_app d.params,
   let my_shape_t := (@const tt (d.induct.name <.> "shape") d.induct.u_params).mk_app $ d.params,
   v' ← mk_live_vec d.vec_lvl d.live_params,
   v ← mk_live_vec d.vec_lvl $ d.live_params ++ [my_t],
   yy ← mk_local_def `y (my_shape_intl_t v),
   x ← mk_local_def `x my_t,
   p ← mk_local_def `p (my_t.imp `(Prop)),
   let eqn := (@const tt (func.eqn_name) d.induct.u_params).mk_app d.params my_t,
   a ← mk_mapp ``typevec.pred_last [none,v',none,p],
   liftp ← mk_const ``mvfunctor.liftp,
   unify_mapp liftp [none,my_shape_intl_t,none],
   b ← unify_mapp liftp [none,my_shape_intl_t,none,none,a,yy] >>= mk_local_def `a,
   mk_y ← mk_app ``mvqpf.fix.mk [yy],
   branches ← d.induct.ctors.mmap $ λ c,
     do { let c_t := (@const tt c.name d.induct.u_params).mk_app d.params,
          (args,_) ← infer_type c_t >>= mk_local_pis,
          ih ← args.mmap $ λ x,
            do { t ← infer_type x,
                 if my_t.occurs t then do
                   (xs,_) ← mk_local_pis t,
                   v ← pis xs (p $ x.mk_app xs) >>= mk_local_def `v,
                   pure [v]
                 else pure [] },
          b ← pis' [args, ih.join] (p $ c_t.mk_app args) >>= mk_local_def `a,
          pure (c,ih,b) },
   ht ← pis [yy,b] (p mk_y),
   (_,h) ← solve_aux ht $ do
   { y ← intro1,
     y' ← mk_eq_mp eqn y,
     generalize_with `h `y' y',
     C ← mk_motive, y' ← intro `y',
     cases_fn ← mk_const (d.induct.name <.> "shape" <.> "cases_on"),
     gs ← list.mrepeat d.induct.ctors.length mk_mvar,
     unify_app cases_fn (d.params ++ [my_t,C,y'] ++ gs) >>= exact,
     set_goals gs,
     branches.mmap $ λ ⟨c,ih,b⟩,
       solve1 $ do
       { let _a : type_cnstr := c,
         args ← intron' c.args.length,
         h ← intro1,
         h' ← mk_app ``eq_mpr_of_mp_eq [h] >>= rewrite_target,
         ih ← intro1,
         v ← mk_mvar, v' ← mk_mvar,
         thm ← mk_const ``mvfunctor.liftp_last_pred_iff,
         thm ← unify_app' thm [v',v],
         mpr ← mk_const ``iff.mpr,
         ih ← (unify_app' mpr [thm,ih] >>= instantiate_mvars >>= note ih.local_pp_name none) <* clear ih,
         simp_only [``(typevec.pred_last'),``(typevec.const_append1),``(typevec.const_nil),``(typevec.subtype_val_append1),``(typevec.subtype_val_nil)] [] (some ih.local_pp_name),
         let n := (c.name.update_prefix $ c.name.get_prefix <.> "shape").append_suffix "_liftp",
         n' ← mk_const n,
         ih ← get_local ih.local_pp_name,
         ih ← (unify_app' n' [ih] >>= note ih.local_pp_name none) <* clear ih,
         p_args ← parse_conjunction ih,
         exact $ b.mk_app' [args,p_args],
         done },
     done },
   ind ← mk_const ``mvqpf.fix.ind,
   df ← unify_mapp ind [none,my_shape_intl_t,none,none,v',p,h,x] >>= instantiate_mvars,
   df ← lambdas' [d.params.map to_implicit_local_const, to_implicit_local_const p :: branches.map (prod.snd ∘ prod.snd),[x]] df,
   t ← infer_type df,
   add_decl $ declaration.thm (d.induct.name <.> "ind") d.induct.u_names t (pure df),
   skip

meta def mk_last_rel' : list (expr ⊕ expr) → tactic (bool × list (expr ⊕ expr × expr))
| [] := pure (ff,[])
| (sum.inl x :: xs) :=
  prod.map id (list.cons $ sum.inl x) <$> mk_last_rel' xs
| (sum.inr x :: xs) :=
  do (b,ys) ← mk_last_rel' xs,
     if b then do
       R ← mk_mapp ``eq [x],
       pure (tt,sum.inr (x, R) :: ys)
     else do
       R ← mk_rel_var x,
       pure (tt,sum.inr R :: ys)

meta def mk_last_rel : list (expr ⊕ expr) → tactic (list (expr ⊕ expr × expr)) :=
(<$>) prod.snd ∘ mk_last_rel'

-- #check mvqpf.cofix.bisim

-- #exit
meta def mk_bisim (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
trace_scope $ do
do let my_shape_intl_t := (@const tt (d.induct.name <.> "shape" <.> "internal") d.induct.u_params).mk_app func.dead_params,
   let my_t := (@const tt (d.induct.name) d.induct.u_params).mk_app d.params,
   v' ← mk_live_vec d.vec_lvl d.live_params,
   x ← mk_local_def `x my_t,
   y ← mk_local_def `y my_t,
   -- r  ← mk_local_def `r (my_t.imp $ my_t.imp `(Prop)) >>= trace_expr,
   let rel := (@const tt (d.induct.name <.> "bisim_rel") d.induct.u_params).mk_app d.params,
   -- trace $ ls,

   -- let R := (@const tt (func.induct.name ++ "liftr") func.univ_params).mk_app (params.bind decls') x y,
   -- R ← mk_app (func.induct.name ++ "liftr") [r',x',y'],
   -- R' ← mk_app ``mvfunctor.liftr [r',x',y'],
   -- trace_expr my_shape_intl_t,
   e ← mk_mapp ``mvqpf.cofix.bisim [none,my_shape_intl_t,none,none,v',rel] >>= trace_expr,
   t ← infer_type e,
   let t := t.binding_domain,
   solve_aux t $ do {
     xs ← introv [],
     hr ← intro `hr,
     trace_state,
     h ← mk_const ``mvfunctor.liftr_last_rel_iff,
     -- trace_expr h,
     rewrite_target h { symm := tt },
     `[simp only [typevec.rel_last'] with typevec],
     trace_state },

   -- mk_const ``mvqpf.cofix.bisim >>= trace_expr,
   skip

/-

-/
meta def mk_bisim' (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
trace_scope $ do
do let my_shape_intl_t := (@const tt (d.induct.name <.> "shape" <.> "internal") d.induct.u_params).mk_app func.dead_params,
   let my_t := (@const tt (d.induct.name) d.induct.u_params).mk_app d.params,

   v' ← mk_live_vec d.vec_lvl d.live_params,
   x ← mk_local_def `x my_t,
   y ← mk_local_def `y my_t,
   x' ← mk_app ``mvqpf.cofix.dest [x],
   y' ← mk_app ``mvqpf.cofix.dest [y],
   r  ← mk_local_def `r (my_t.imp $ my_t.imp `(Prop)),
   r' ← mk_mapp ``typevec.rel_last [none,v',none,none,r],
   hr ← mk_local_def `a (r x y),
   R ← mk_app ``mvfunctor.liftr [r',x',y'],
   f ← pis [x,y,hr] R >>= mk_local_def `f,
   trace_expr f,
   df ← mk_mapp ``mvqpf.cofix.bisim [none,my_shape_intl_t,none,none,v',r,f,x,y,hr]
      >>= lambdas (d.params ++ [r,f,x,y,hr]),
   t  ← mk_app `eq [x,y] >>= pis (d.params ++ [r,f,x,y,hr]),
   f ← add_decl' $ declaration.thm (d.induct.name <.> "bisim") d.induct.u_names t (pure df),
   -- let r := (@const tt (d.induct.name <.> "bisim_rel") d.induct.u_params).mk_app d.params,
   -- let e := f.mk_app d.params r,
   -- t ← expr.binding_domain <$> infer_type e,
   -- @solve_aux unit t $ do
   -- { x ← intro1, y ← intro1, h ← intro1,
   --   C ← target >>= lambdas [x,y],
   --   let cases_on := (@const tt (d.induct.name <.> "bisim_rel" <.> "cases_on") d.induct.u_params).mk_app d.params C x y h,
   --   args ← infer_type cases_on >>= mk_mvar_pis,
   --   exact $ cases_on.mk_app args,
   --   mzip_with (λ g (c : type_cnstr),
   --   do { set_goals [g], trace c.name,
   --        dunfold_target [c.name,``mvfunctor.liftr],
   --        simp_only [``(mvqpf.cofix.dest_mk)],
   --        `(∃ _ : %%t, _) ← target,
   --        v ← mk_meta_var t, trace t,
   --        let cn := c.name.update_prefix $ c.name.get_prefix <.> "shape",
   --        let n  := (cn.update_prefix $ cn.get_prefix <.> "pfunctor").append_suffix "_map",
   --        mk_const n >>= trace_expr,
   --        let w := (@const tt cn d.induct.u_params).mk_app [], -- d.params v,
   --        args ← infer_type w >>= mk_mvar_pis,
   --        let w := w.mk_app args,
   --        trace "",
   --        trace_expr w,
   --        trace "",
   --        existsi w,
   --        -- simp_only [] [`typevec],
   --        trace_state, done })
   --    args d.induct.ctors,
   --   trace "",
   --   trace_state },
   -- trace_expr $ e,
   skip

open environment.implicit_infer_kind
-- meta def mk_bisim_rel (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
-- -- trace_scope $
-- do let params := d.params.map to_implicit_local_const,
--    let t := (@const tt d.induct.name d.induct.u_params).mk_app params,
--    let n := d.induct.name <.> "bisim_rel",
--    let decl := d.induct,
--    let type_ctor := (@const tt n decl.u_params).mk_app params,
--    cs ← d.induct.ctors.mmap $ λ c,
--    do { args ← c.args.mmap $ λ e,
--              if t.occurs e then renew e
--                            else pure e,
--         let (xs,ys) := c.args.partition $ λ e, t.occurs e,
--         let xs' := args.filter $ λ e, t.occurs e,
--         co_ind ← mzip_with (λ x x' : expr,
--         do (args,t) ← infer_type x >>= mk_local_pis,
--            pis args (type_ctor (x.mk_app args) (x'.mk_app args)) >>= mk_local_def `h ) xs xs',
--         let x  := (@const tt c.name d.induct.u_params).mk_app' [d.params,c.args],
--         let x' := (@const tt c.name d.induct.u_params).mk_app' [d.params,args],
--         return ({ name := c.name.update_prefix n,
--                   args := ys ++ xs ++ xs' ++ co_ind,
--                   result := [x,x'],
--                   infer := relaxed_implicit } : type_cnstr) },
--    x ← mk_local_def `x t,
--    y ← mk_local_def `y t,
--    let decl : inductive_type :=
--             { pre := d.induct.pre,
--               name := n,
--               u_names := d.induct.u_names,
--               params := params,
--               idx := [x,y],
--               type := `(Prop),
--               ctors := cs },
--    sig ← decl.sig,
--    intros ← decl.intros,
--    add_coinductive_predicate decl.u_names decl.params [(sig,intros)]

meta def mk_fix_functor_instance (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do let params := func.dead_params,
   let c := (@const tt func.def_name func.induct.u_params).mk_app params,
   let shape_c := (@const tt (func.induct.name <.> "shape" <.> "internal") func.induct.u_params).mk_app params,
   t ← mk_app ``mvfunctor [c] >>= pis params,
   df ← mk_mapp ``mvqpf.fix.mvfunctor [none,shape_c,none,none] >>= lambdas params,
   -- updateex_env $ λ env, pure $ env.add_namespace func.induct.name,
   add_decl $ mk_definition (func.induct.name <.> "mvfunctor") func.induct.u_names t df,
   set_basic_attribute `instance (func.induct.name <.> "mvfunctor"),
   t ← mk_mapp ``mvqpf [none,c,none] >>= pis params,
   df ← mk_mapp ``mvqpf.mvqpf_fix [none,shape_c,none,none] >>= lambdas params,
   add_decl $ mk_definition (func.induct.name <.> "mvqpf") func.induct.u_names t df,
   set_basic_attribute `instance (func.induct.name <.> "mvqpf")

meta def mk_cofix_functor_instance (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do let params := func.dead_params,
   let c := (@const tt func.def_name func.induct.u_params).mk_app params,
   let shape_c := (@const tt (func.induct.name <.> "shape" <.> "internal") func.induct.u_params).mk_app params,
   t ← mk_app ``mvfunctor [c] >>= pis params,
   df ← mk_mapp ``mvqpf.cofix.mvfunctor [none,shape_c,none,none] >>= lambdas params,
   -- updateex_env $ λ env, pure $ env.add_namespace func.induct.name,
   add_decl $ mk_definition (func.induct.name <.> "mvfunctor") func.induct.u_names t df,
   set_basic_attribute `instance (func.induct.name <.> "mvfunctor"),
   t ← mk_mapp ``mvqpf [none,c,none] >>= pis params,
    df ← mk_mapp ``mvqpf.mvqpf_cofix [none,shape_c,none,none] >>= lambdas params,
   add_decl $ mk_definition (func.induct.name <.> "mvqpf") func.induct.u_names t df,
   set_basic_attribute `instance (func.induct.name <.> "mvqpf")

@[user_command]
meta def data_decl (meta_info : decl_meta_info) (_ : parse (tk "data")) : lean.parser unit :=
do d ← inductive_decl.parse meta_info,
   trace_scope $
   trace_error "bad" (do
     (func,d) ← mk_datatype ``mvqpf.fix d,
     mk_liftp_eqns func.to_internal_mvfunctor,
     mk_constr ``mvqpf.fix.mk d,
     mk_destr ``mvqpf.fix.dest ``mvqpf.fix.mk ``mvqpf.fix.mk_dest func d,
     mk_destr_constr_eqn ``mvqpf.fix.dest_mk func d,
     mk_recursor func d,
     mk_dep_recursor func d,
     mk_fix_functor_instance d,
     mk_ind func d,
     mk_no_confusion_type d.induct,
     mk_no_confusion d.induct,
     pure ())

@[user_command]
meta def codata_decl (meta_info : decl_meta_info) (_ : parse (tk "codata")) : lean.parser unit :=
do d ← inductive_decl.parse meta_info,
   -- let d := { name :=  .. d },
   trace_scope $
   trace_error "bad" (do
     (func,d) ← mk_datatype ``mvqpf.cofix d,
     mk_liftp_eqns func.to_internal_mvfunctor,
     mk_constr ``mvqpf.cofix.mk d,
     mk_destr ``mvqpf.cofix.dest ``mvqpf.cofix.mk ``mvqpf.cofix.mk_dest func d,
     mk_destr_constr_eqn ``mvqpf.cofix.dest_mk func d,
     mk_corecursor func d,
     mk_cofix_functor_instance d,
     mk_liftr_defn' d,
     -- mk_liftr_eqns₀ d,
     -- mk_liftr_eqns₁ d,
     -- mk_bisim_rel func d,
     -- mk_bisim func d,
     mk_no_confusion_type d.induct,
     mk_no_confusion d.induct,
     pure ())

meta def mk_liftp_eqns₀_debug (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do params ← func.params'.mmap_live' mk_pred_var,
   let F := (@const tt func.induct.name func.induct.u_params).mk_app $ params.map $ elim id prod.fst,
   let F_intl := (@const tt func.def_name func.induct.u_params).mk_app func.dead_params,
   let n := func.live_params.length,
   vec ← mk_live_vec func.vec_lvl func.live_params,
   let fs := params.filter_map $ get_right prod.snd,
   map_f ← mk_map_vec func.vec_lvl func.vec_lvl fs,
   x ← mk_local_def `x F,
   let vs := [params.bind $ decls' ∘ bimap to_implicit_local_const (bimap to_implicit_local_const id),[x]],
   liftp ← mk_mapp ``mvfunctor.liftp' [`(n),F_intl,none,vec],
   let df := liftp map_f x,
   mk_const ``mvfunctor.liftp_def,
   fn ← mk_mapp ``is_lawful_mvfunctor [`(n),F_intl,none] >>= mk_instance,
   defn ← mk_mapp ``mvfunctor.liftp_def [`(n),F_intl,none,vec], -- ,map_f,none,x,y
   let defn := defn map_f fn x,
   param_sub ← params.mmap_live' $ λ ⟨α,f⟩,
   do { σ ← mk_mapp ``subtype [none,f],
        pure (α,f,σ) },
   let F_sub := (@const tt func.induct.name func.induct.u_params).mk_app $ param_sub.map $ elim id $ prod.snd ∘ prod.snd,
   u ← mk_local_def `u F_sub,
   args ← list.join <$> param_sub.mmap (elim (pure ∘ list.ret) $ λ ⟨α,unc,σ⟩,
           do { val ← mk_mapp ``subtype.val [none,unc],
                -- f ← to_expr ``(%%val),
                pure [σ,α,val] }),
   let map  := (@const tt (func.induct.name <.> "map") func.induct.u_params).mk_app args u,
   l ← mk_app ``eq [map,x],
   -- trace_expr df,
   `(@Exists %%t₀ _) ← whnf df,
   let lhs := df,
   rhs ← mk_exists [u] l,
   t ← mk_app `iff [lhs,rhs],
   is_def_eq F_sub t₀ <|> fail "not def eq",
   -- trace!"F_sub : {F_sub}",
   -- trace!"t₀    : {t₀}",
   -- trace!"t₀    : {whnf t₀}",
   -- trace!"defn  : {infer_type defn}",
   -- trace!"t     : {t}",
   v ← mk_mvar,
   (_,pr) ← solve_aux t $ refine ``(iff.trans %%defn %%v), -- (iff.refl _)
   trace_expr v,
   retrieve $ do {
     set_goals [v],
     applyc ``exists_congr, intro1,
     applyc ``eq.congr,
     (l,r) ← target >>= match_eq,
     trace!"l: {l}",
     trace!"r: {whnf r}",
     applyc ``congr_arg,
     trace_state},

   t ← pis' vs t,
   pr ← instantiate_mvars pr >>= lambdas' vs,
   let vars := pr.list_local_consts,
   add_decl $ mk_definition (func.induct.name <.> "liftp_def") func.induct.u_names t pr,
   skip

attribute [vm_override mk_liftp_eqns₀_debug] mk_liftp_eqns₀

-- meta def mk_meta_sort : tactic expr :=
-- expr.sort <$> mk_meta_univ >>= mk_meta_var

end tactic

set_option trace.app_builder true
set_option trace.trace_scope.error true
set_option trace.compiler.input true

codata tree' (α β : Type)
| nil : tree'
| cons : α → (β → tree') → tree'
