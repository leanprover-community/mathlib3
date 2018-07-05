-- import data.list.basic
import data.equiv.basic
import tactic.interactive
-- import meta.expr
-- import tactic.refine

universes u v w

open function

class canonical_equiv (α : Sort*) (β : Sort*) extends equiv α β.

def equiv.injective {α : Sort*} {β : Sort*} (eq : α ≃ β) :
  injective eq :=
injective_of_left_inverse eq.left_inv

#print prefix equiv.injective
#print equiv.injective.equations._eqn_1

variables  (f : Type u → Prop)
variables (on_equiv : Π {α β : Type u} (e : equiv α β), equiv (f α) (f β))


section
open tactic.interactive
meta def prove_on_equiv_law' (n := `on_equiv) :=
do intros [],
   eqv ← tactic.resolve_name n,
   `[dsimp [equiv.refl,equiv.trans]],
   generalize none () (``(%%eqv _),`k),
   `[cases k, refl]

meta def prove_on_equiv_law := prove_on_equiv_law'
end

class transportable (f : Type u → Type v) :=
(on_equiv : Π {α β : Type u} (e : equiv α β), equiv (f α) (f β))
(on_refl  : Π (α : Type u), on_equiv (equiv.refl α) = equiv.refl (f α) . prove_on_equiv_law)
(on_trans : Π {α β γ : Type u} (d : equiv α β) (e : equiv β γ), on_equiv (equiv.trans d e) = equiv.trans (on_equiv d) (on_equiv e) . prove_on_equiv_law)

-- Finally a command like: `initialize_transport group` would create the next two declarations automagically:

open transportable

definition equiv_mul {α β : Type u} : equiv α β → equiv (has_mul α) (has_mul β) := λ E,
{ to_fun :=  λ αmul,⟨λ b1 b2, E.to_fun (@has_mul.mul α αmul (E.inv_fun b1) (E.inv_fun b2))⟩,
  inv_fun := λ βmul,⟨λ a1 a2, E.inv_fun (@has_mul.mul β βmul (E.to_fun a1) (E.to_fun a2))⟩, -- didn't I just write that?
                                                                      -- should we introduce E-dual?
  left_inv := λ f, begin
    cases f, simp, -- aargh why do I struggle
    congr,
    -- suffices :  (λ (a1 a2 : α), E.inv_fun (E.to_fun (f _ _))) = (λ a1 a2, f a1 a2),
    --   by rw this,
    funext,
    simp [E.left_inv _,E.right_inv _], -- got there in the end
  end,
  right_inv := -- I can't even do this in term mode so I just copy out the entire tactic mode proof again.
 λ g, begin
    cases g, simp, -- aargh why do I struggle
    suffices :  (λ (b1 b2 : β), E.to_fun (E.inv_fun (g _ _))) = (λ b1 b2, g b1 b2),
      by rw this,
    funext,
    simp [E.left_inv _,E.right_inv _], -- got there in the end
  end, -- didn't I just write that?
}

namespace tactic

namespace interactive

open interactive function
#check @rfl
meta def eqn_lemma_type : expr → expr → expr → tactic (expr × expr)
| (expr.pi n bi d b) fn arg :=
do v ← mk_local' n bi d,
   arg ← head_beta (arg v),
   prod.map (expr.pis [v]) (expr.lambdas [v]) <$> eqn_lemma_type (b.instantiate_var v) (fn v) arg
| _ fn arg :=
prod.mk <$> to_expr ``(%%fn = %%arg) <*> to_expr ``(@rfl _ %%arg)

meta def eq_lemma_name (n : name) := n <.> "equations" <.> "_eqn_1"

meta def abstract_def (suffix : name) (t : expr) (tac : tactic unit) : tactic name :=
do (_,v) ← solve_aux t tac,
   n ← (++ suffix) <$> decl_name,
   v ← instantiate_mvars v,
   t ← instantiate_mvars t,
   add_decl $ mk_definition n t.collect_univ_params t v,
   defn ← mk_const n,
   (t,p) ← eqn_lemma_type t defn v,
   add_decl $ declaration.thm (eq_lemma_name n) t.collect_univ_params t (return p),
   set_basic_attribute `_refl_lemma (eq_lemma_name n),
   return n

meta def build_aux_decl_with (c : name) (type : pexpr) (is_lemma : bool) (tac : tactic unit) : tactic expr :=
do type' ← to_expr type,
   ((),v) ← solve_aux type' tac,
   add_aux_decl c type' v is_lemma

open functor

def strip_prefix (n : name) : name :=
name.update_prefix n name.anonymous
-- #check @equiv.injective
-- #print injective

meta def all_field_names : tactic (list name) :=
do gs ← get_goals,
   gs.mmap (λ g, set_goals [g] >> get_current_field)
   <* set_goals gs

meta def mk_app_aux : expr → expr → list (option expr) → tactic expr
| (expr.pi n bi d b) e (none :: args) :=
do v ← mk_meta_var d,
   mk_app_aux (b.instantiate_var v) (e v) args
| (expr.pi n bi d b) e (some v :: args) :=
   mk_app_aux (b.instantiate_var v) (e v) args
| t _ (_ :: _) := fail format!"{t} is not a Π-type"
| _ e [] := pure e

meta def mk_app' (e : expr) (es : list (option expr)) : tactic expr :=
do t ← infer_type e,
   mk_app_aux t e es

meta def qualified_field_list (struct_n : name) : tactic (list name) :=
map (uncurry $ flip name.update_prefix) <$> expanded_field_list struct_n

meta def mk_to_fun (n : name) : tactic name :=
do env  ← get_env,
   decl ← env.get n,
   let univs := decl.univ_params,
   e ← resolve_name n,
   fields ← qualified_field_list n,
   t ← to_expr ``(Π α β : Type u, α ≃ β → %%e α → %%e β),
   abstract_def (n <.> "transport" <.> "to_fun") t
     (do α  ← tactic.intro `α, β  ← tactic.intro `β, eq_ ← tactic.intro `eqv,
         eqv ← to_expr ``(@coe_fn _ equiv.has_coe_to_fun (%%eq_)),
         eqv_symm ← to_expr ``(@coe_fn _ equiv.has_coe_to_fun (%%eq_).symm),
         x ← tactic.intro `x,
         [v] ← get_goals,
         refine_struct ``( { .. } ),
         let unfold_more := [`has_one.one,`has_zero.zero,`has_mul.mul,`has_add.add
                            ,`semigroup.mul,`group.mul],
         fs ← all_field_names >>= mmap resolve_name ∘ list.append unfold_more,
         all_goals (do
           fl ← get_current_field,
           xs ← tactic.intros,
           p ← mk_const fl >>= infer_type >>= pp,
           xs' ← mmap (λ x,
             mcond (is_proof x)
                 (pure none)
                 (pure $ some $ eqv_symm x)) xs,
           e ← mk_app fl (map eqv_symm xs) <|>
               (mk_mapp fl [none,some x] >>= flip mk_app' xs') <|>
               fail format!"{fl} - {xs'} :: {p}",
           infer_type e >>= trace,
           trace "a",
           tactic.exact (eqv e) <|>
           (do refine ``((equiv.apply_eq_iff_eq (%%eq_).symm _ _).1 _) <|>
                      refine ``((not_iff_not_of_iff $ equiv.apply_eq_iff_eq (%%eq_).symm _ _).1 _),
               trace "b",
               g ← mk_mvar,
               refine ``(iff.elim_left (eq.to_iff %%g) %%e),
               -- tactic.type_check e,
               num_goals >>= trace,
               trace_state,
               gs ← get_goals, set_goals $ g :: gs.diff [g],
               num_goals >>= trace,
               solve1 (do
               -- simp (some ()) ff (map simp_arg_type.expr $ ``(@equiv.inverse_apply_apply) :: fs) [] (loc.ns [none]),
               -- simp (some ()) ff (map simp_arg_type.expr $ fs) [] (loc.ns [none]),
               -- repeat $ dsimp ff (map simp_arg_type.expr $ fs ++ [``(@equiv.inverse_apply_apply)]) [] (loc.ns [none]),
                 trace "c",
                 -- infer_type e >>= trace,
                 unfold_projs (loc.ns [none]),
                 simp (some ()) tt (map simp_arg_type.expr [``(@equiv.inverse_apply_apply),``(id)]) [] (loc.ns [none]),
               -- try $ simp (some ()) ff (map simp_arg_type.expr $ fs ++ [``(@has_mul.mul),``(@equiv.inverse_apply_apply)]) [] (loc.ns [none]),
               -- repeat `[rw [equiv.inverse_apply_apply]],
                 trace_state,
                 trace "d",
                 done <|> refl <|> (congr; done <|> refl)),
               trace "e",
               done <|> solve1 (do
                 trace "f",
                 target >>= infer_type >>= trace,
                 target >>= instantiate_mvars >>= tactic.change,
                 target >>= trace,
                 done )) <|>
           (do refine ``((not_iff_not_of_iff $ equiv.apply_eq_iff_eq (%%eq_).symm _ _).1 _),
               refine ``(iff.elim_left _ %%e),
               refine ``(not_iff_not_of_iff _),
               refine ``(eq.to_iff _),
               unfold_projs (loc.ns [none]),
               simp (some ()) tt (map simp_arg_type.expr [``(@equiv.inverse_apply_apply),``(id)]) [] (loc.ns [none]),
               done) <|>
           (do -- trace_state,
               infer_type e >>= trace,
               trace "dude",
               done)))


-- set_option pp.universes true
-- set_option pp.notation false
-- set_option pp.implicit true

-- run_cmd add_interactive [`mk_to_fun]

-- run_cmd mk_to_fun `group
-- #print prefix _run_command.group

meta def mk_on_equiv (n to_fun : name) : tactic name :=
do f ← resolve_name n,
   fn ← resolve_name to_fun,
   t ← to_expr ``(Π (α β : Type u), α ≃ β → %%f α ≃ %%f β),
   abstract_def (n ++ `on_eqv) t $
     do tactic.intron 2,
        eqv ← tactic.intro1,
        refine ``( { to_fun := %%fn _ _ %%eqv,
                     inv_fun := %%fn _ _ (%%eqv).symm,
                     .. } );
        abstract none (
        dunfold [`function.left_inverse,`function.right_inverse] (loc.ns [none]);
        (do x ← tactic.intro1, tactic.cases x,
            dunfold [to_fun] (loc.ns [none]),
            congr; tactic.funext;
            `[ simp only [equiv.inverse_apply_apply,equiv.apply_inverse_apply,id] ],
            return ()))

meta def mk_transportable_instance  (n : name) : tactic unit :=
do d ← decl_name,
   -- let to_fun := d ++ `group.transport.to_fun,
   to_fun ← mk_to_fun n,
   to_fun_lmm ← resolve_name $ eq_lemma_name to_fun,
   on_eqv_n ← mk_on_equiv n to_fun,
   on_eqv ← resolve_name on_eqv_n,
   on_eqv_lmm ← resolve_name $ eq_lemma_name on_eqv_n,
   fs ← expanded_field_list n,
   env  ← get_env,
   decl ← env.get n,
   let univs := decl.univ_params,
   let e := @expr.const tt n $ univs.map level.param,
   t ← to_expr ``(transportable %%e),
   let goal := (loc.ns [none]),
   (_,d) ← solve_aux t
     (do refine ``( { on_equiv := %%on_eqv, on_refl := _, on_trans := _ } ),
         -- cleanup,
         abstract (some $ n ++ `on_refl) (do
           intro1,
           fs' ← fs.mmap (resolve_name ∘ uncurry (flip name.update_prefix)),
           -- simp (some ()) ff (map simp_arg_type.expr $ [``(equiv.refl),``(equiv.symm),on_eqv_lmm,to_fun_lmm]) [] goal,
           dsimp ff (map simp_arg_type.expr $
             [``(equiv.refl),``(equiv.symm),on_eqv_lmm,to_fun_lmm]) [] goal,
           -- done,
           -- dunfold [``equiv.refl,on_eqv_n,to_fun] goal,
         -- num_goals >>= trace,
           -- done,
           try congr; tactic.funext; cases (none,```(x)) [];
           dunfold [`id,to_fun] goal;refl ),
         abstract (some $ n ++ `on_trans) (do
           intro1,
           fs' ← fs.mmap (resolve_name ∘ uncurry (flip name.update_prefix)),
           dsimp ff (map simp_arg_type.expr $
             [``(function.comp),``(equiv.to_fun),``(equiv.inv_fun),``(equiv.trans),
              ``(equiv.symm),on_eqv_lmm,to_fun_lmm  ]) [] goal,
         -- num_goals >>= trace,
           -- dunfold [on_eqv_n,`function.comp,`equiv.to_fun,`equiv.inv_fun,``equiv.trans] goal,
           -- dunfold [`id] goal,
         -- num_goals >>= trace,
           intron 4,
           try congr; tactic.funext; cases (none,```(x)) [];
           dunfold [`id,to_fun] goal;refl ),
         -- num_goals >>= trace,
         -- dunfold [`id,to_fun] goal,
         -- num_goals >>= trace,
         -- target >>= trace,
         -- num_goals >>= trace,
         -- dsimp ff (map simp_arg_type.expr fs') [] goal,
         -- num_goals >>= trace,
         -- trace_state,
         -- target >>= trace,
         -- prove_on_equiv_law,
         -- prove_on_equiv_law,
         done),
   d ← instantiate_mvars d,
   let def_name := n <.> "transportable",
   add_decl $ mk_definition def_name univs t d,
   set_basic_attribute `instance def_name tt

set_option profiler true
set_option formatter.hide_full_terms false
set_option pp.delayed_abstraction false
set_option pp.universes true


-- run_cmd do
--  mk_transportable_instance `group

set_option profiler false

-- example  : Π {α β : Type u} (e : equiv α β), equiv (group α) (group β) :=
-- begin
--   introv eqv,
--   refine_struct { to_fun  := @group.transport.to_fun _ _ eqv
--                 , inv_fun := @group.transport.to_fun _ _ eqv.symm
--                 , .. };
--   dsimp [left_inverse,function.right_inverse];
--   intro x ; dunfold group.transport.to_fun;
--   cases x; congr; funext;
--   simp only [equiv.inverse_apply_apply,equiv.apply_inverse_apply,id],
-- end

#check congr_arg


-- #print group.transport.to_fun

-- meta def mk_transportable (n : name) (e : expr) : tactic unit :=
-- do [v] ← get_goals,
--    trace "begin mk_transportable",
--    trace "-- | TO_FUN",
--    fields ← qualified_field_list n,
--    to_fun ← to_expr ``(Π α β : Type u, α ≃ β → %%e α → %%e β)
--      >>= define ( `to_fun),
--    solve1
--      (do α  ← tactic.intro `α,
--          β  ← tactic.intro `β,
--          eq ← tactic.intro `eqv,
--          eqv ← to_expr ``(@coe_fn _ equiv.has_coe_to_fun (%%eq)),
--          eqv_symm ← to_expr ``(@coe_fn _ equiv.has_coe_to_fun (%%eq).symm),
--          x ← tactic.intro `x,
--          [v] ← get_goals,
--          refine_struct ``( { .. } ),
--          -- trace_state,
--          all_goals (do
--            tgt ← target,
--            p ← is_prop tgt,
--            if p then do
--              trace "A",
--              current ← get_current_field <|> fail "get_current_field",
--              vs ← tactic.intros,
--              h ← mk_mapp current ( [α,x] ++ vs.map (some ∘ eqv_symm) ) >>= note `h none
--                <|> fail "mk_mapp",
--              unfold (fields) (loc.ns [none,h.local_pp_name]), -- h.local_pp_name]),
--              h ← get_local h.local_pp_name,
--              infer_type h >>= trace,
--              -- tactic.revert h,
--              fs ← mmap (resolve_name ∘ strip_prefix) fields,
--              simp (some ()) tt (map simp_arg_type.expr $ [``(equiv.apply_inverse_apply),``(equiv.inverse_apply_apply)] ++ fs) [] (loc.ns [none,h.local_pp_name]), -- ,h.local_pp_name
--              -- h ← get_local h.local_pp_name,
--              -- infer_type h >>= trace,
--              trace_state,
--              -- target >>= trace,
--              -- tactic.exact h,
--              done,
--              trace "C",
--              return ()
--            else do
--              trace "B",
--              -- target >>= trace,
--              -- [v] ← get_goals,
--              current ← get_current_field,
--              trace current,
--              vs ← tactic.intros,
--              -- infer_type eqv_symm >>= trace,
--              -- refine ``(%%eqv _) <|> fail "refine",
--              trace eqv_symm,
--              -- trace vs,
--              -- instantiate_mvars v >>= trace,
--              let vs' := map (some ∘ eqv_symm) vs,
--              e ← mk_mapp current ( [α,x] ++ vs' ),
--              e ← to_expr ``(@coe_fn _ equiv.has_coe_to_fun %%eq %%e),
--              trace "to_expr",
--              trace e,
--              tactic.exact e,
--              trace "C",
--              -- trace_state,
--              return () ),
--          -- instantiate_mvars v >>= trace,
--          trace_state,
--          return () ),
--    -- inv_fun ← build_aux_decl_with ( (`inv_fun).update_prefix n)
--    --   ``(Π {α β}, %%e β → %%e α) ff
--    --   (do trace_state >> admit),
--    trace "-- | EQUIV",
--    is_inv ← to_expr ``(∀ α β (eqv : equiv α β),
--             left_inverse (%%to_fun β α eqv.symm) (%%to_fun α β eqv))
--           >>= assert `is_inv,
--    solve1 (do
--           α  ← tactic.intro `α,
--           β  ← tactic.intro `β,
--           eq ← tactic.intro `eqv,
--           x ← tactic.intro `x,
--           tactic.cases x,
--           -- trace_state,
--           `[simp only [to_fun]],
--           congr ; funext [] ; dunfold fields (loc.ns [none]) ;
--           `[simp! only [_root_.eq.mpr,equiv.apply_inverse_apply,equiv.inverse_apply_apply]],
--           -- trace_state,
--           return () ),
--    fn ← to_expr ``(Π α β, equiv α β → equiv (%%e α) (%%e β))
--      >>= define ( (`on_equiv).update_prefix n),
--    solve1
--      (do α  ← tactic.intro `α,
--          β  ← tactic.intro `β,
--          eq ← tactic.intro `eqv,

--          refine_struct ``( { to_fun := %%to_fun %%α %%β %%eq,
--                        inv_fun := %%to_fun %%β %%α (%%eq).symm,
--                        left_inv := %%is_inv %%α %%β %%eq }),
--          admit ),
--      -- | transport
--    trace "-- | TRANSPORT",
--    refine_struct ``( { on_equiv := %%fn, .. } ), -- (some `duh),
--    admit <|> fail "admit A",
--    admit <|> fail "admit B",
--    trace_state <|> fail "here",
--    -- instantiate_mvars v >>= trace ,
--    trace "end (mk_transportable)"


meta def instance_derive_handler' (univ_poly := tt)
  (modify_target : name → list expr → expr → tactic expr := λ _ _, pure) : derive_handler :=
λ p n, do
let cls := `transportable,
if p.is_constant_of cls then
do decl ← get_decl n,
   cls_decl ← get_decl cls,
   env ← get_env,
   -- guard (env.is_inductive n) <|> fail format!"failed to derive '{cls}', '{n}' is not an inductive type",
   let ls := decl.univ_params.map $ λ n, if univ_poly then level.param n else level.zero,
   -- incrementally build up target expression `Π (hp : p) [cls hp] ..., cls (n.{ls} hp ...)`
   -- where `p ...` are the inductive parameter types of `n`
   let tgt : expr := expr.const n ls,
   ⟨params, _⟩ ← mk_local_pis (decl.type.instantiate_univ_params (decl.univ_params.zip ls)),
   (type,tgt) ← params.inits.any_of (λ param, do
     let tgt := tgt.mk_app param,
     prod.mk tgt <$> mk_app cls [tgt]),
   tgt ← modify_target n [] tgt,
   -- tgt ← params.enum.mfoldr (λ ⟨i, param⟩ tgt,
   -- do -- add typeclass hypothesis for each inductive parameter
   --    tgt ← do {
   --      guard $ i < env.inductive_num_params n,
   --      param_cls ← mk_app cls [param] <|> fail "fart",
   --      -- TODO(sullrich): omit some typeclass parameters based on usage of `param`?
   --      pure $ expr.pi `a binder_info.inst_implicit param_cls tgt
   --    } <|> pure tgt,
   --    pure $ tgt.bind_pi param
   -- ) tgt,
   mk_transportable_instance n,
   pure true
else pure false


@[derive_handler]
meta def transportable_handler : derive_handler :=
instance_derive_handler' tt $
λ n params, pure

-- -- ``(transportable) _

end interactive
end tactic

-- namespace group

-- variables {α β : Type u}
-- variables (eq : equiv α β)

-- @[simp] def tr₀ : α → β := eq
-- @[simp] def tr₁ (f : α → α) : β → β := λ x : β, eq (f $ eq.symm x)
-- @[simp] def tr₂ (f : α → α → α) : β → β → β := λ (x y : β), eq $ f (eq.symm x) (eq.symm y)
-- -- def etr₀ : β → α := eq.inv_fun
-- -- def etr₁ (f : β → β) (x : α) : α := eq.inv_fun (f $ eq.to_fun x)
-- -- def etr₂ (f : β → β → β) (x y : α) : α := eq.inv_fun $ f (eq.to_fun x) (eq.to_fun y)

-- -- @[simp]
-- -- lemma inv_fun_tr₀ (f : α) :
-- --   eq.inv_fun (tr₀ eq f) = f :=
-- -- by simp [tr₀,equiv.left_inv eq _]

-- -- @[simp]
-- -- lemma inv_fun_tr₁ (f : α → α) (x : β) :
-- --   eq.inv_fun (tr₁ eq f x) = f (eq.inv_fun x) :=
-- -- by simp [tr₁,equiv.left_inv eq _]

-- -- @[simp]
-- -- lemma inv_fun_tr₂ (f : α → α → α) (x y : β) :
-- --   eq.inv_fun (tr₂ eq f x y) = f (eq.inv_fun x) (eq.inv_fun y) :=
-- -- by simp [tr₂,equiv.left_inv eq _]

-- local attribute [simp] equiv.left_inv equiv.right_inv

-- -- @[simp]
-- -- lemma symm_inv_fun :
-- --   eq.symm.inv_fun = eq.to_fun :=
-- -- by cases eq ; refl

-- -- @[simp]
-- -- lemma symm_to_fun :
-- --   eq.symm.to_fun = eq.inv_fun :=
-- -- by cases eq ; refl

-- -- @[simp]
-- -- lemma inv_fun_etr₀ (f : β) :
-- --   eq.to_fun (etr₀ eq f) = f :=
-- -- by simp [etr₀,equiv.right_inv eq _]

-- -- @[simp]
-- -- lemma inv_fun_etr₁ (f : β → β) (x : α) :
-- --   eq.to_fun (etr₁ eq f x) = f (eq.to_fun x) :=
-- -- by simp [etr₁,equiv.left_inv eq _]

-- -- @[simp]
-- -- lemma inv_fun_etr₂ (f : α → α → α) (x y : β) :
-- --   eq.inv_fun (etr₂ eq f x y) = f (eq.inv_fun x) (eq.inv_fun y) :=
-- -- by simp [tr₂,equiv.left_inv eq _]

-- lemma inj {x y : β}
--   (h : eq.symm x = eq.symm y)
-- : x = y := sorry

-- -- @[simp]
-- -- def on_equiv.to_fun [group α] : group β :=
-- -- { one := tr₀ eq (one α)
-- -- , mul := tr₂ eq mul
-- -- , inv := tr₁ eq inv
-- -- , mul_left_inv := by { intros, apply inj eq, simp, apply mul_left_inv }
-- -- , one_mul := by { intros, apply inj eq, simp, apply one_mul }
-- -- , mul_one := by { intros, apply inj eq, simp [has_mul.mul], apply mul_one }
-- -- , mul_assoc := by { intros, apply inj eq, simp, apply mul_assoc }  }

-- -- @[simp]
-- -- def on_equiv.inv_fun [group β] : group α :=
-- -- { one := tr₀ eq.symm (one _)
-- -- , mul := tr₂ eq.symm mul
-- -- , inv := tr₁ eq.symm inv
-- -- , mul_left_inv := by { intros, apply inj eq.symm, simp, apply mul_left_inv }
-- -- , one_mul := by { intros, apply inj eq.symm, simp, apply one_mul }
-- -- , mul_one := by { intros, apply inj eq.symm, simp [has_mul.mul], apply mul_one }
-- -- , mul_assoc := by { intros, apply inj eq.symm, simp, apply mul_assoc }  }

-- -- def on_equiv' : group α ≃ group β :=
-- -- { to_fun := @on_equiv.to_fun _ _ eq,
-- --   inv_fun := @on_equiv.inv_fun _ _ eq,
-- --   right_inv :=
-- --   by { intro x, cases x, simp,
-- --        congr ;
-- --        funext ;
-- --        dsimp [mul,one,inv] ;
-- --        simp!, },
-- --   left_inv :=
-- --   by { intro x, cases x, simp,
-- --        congr ;
-- --        funext ;
-- --        dsimp [mul,one,inv] ;
-- --        simp!, } }

-- -- def transportable' : transportable group :=
-- -- begin
-- --   refine { on_equiv := @on_equiv', .. }
-- --   ; intros ; simp [on_equiv',equiv.refl,equiv.trans]
-- --   ; split ; funext x ; cases x ; refl,
-- -- end

-- -- set_option formatter.hide_full_terms false
-- set_option pp.all true
-- -- set_option trace.app_builder true
-- -- #check equiv.has_coe_to_fun

-- -- set_option profiler true

-- -- attribute [derive transportable] group monoid ring field --
-- -- attribute [derive transportable] monoid
-- -- attribute [derive transportable] has_add
-- -- ⊢ Π (α β : Type u), α ≃ β → group α → group β
-- -- α β : Type u,
-- -- eq : α ≃ β
-- -- ⊢ group α ≃ group β
-- -- on_equiv
-- -- 2 goals
-- -- case on_refl
-- -- ⊢ ∀ (α : Type u), on_equiv α α (equiv.refl α) = equiv.refl (group α)

-- -- case on_trans
-- -- ⊢ ∀ {α β γ : Type u} (d : α ≃ β) (e : β ≃ γ),
-- --     on_equiv α γ (equiv.trans d e) = equiv.trans (on_equiv α β d) (on_equiv β γ e)
-- -- [_field, on_refl]
-- -- [_field, on_trans]
-- -- def transportable' : transportable group :=


-- end group

-- -- #check derive_attr
-- instance group.transport {α β : Type u} [R : group α] [e : canonical_equiv α β] : group β :=
-- sorry
-- -- (@transportable.on_equiv group group.transportable _ _ e.to_equiv).to_fun R


-- -- class transportable (f : Type u → Type v) :=
-- -- (on_equiv : Π {α β : Type u} (e : equiv α β), equiv (f α) (f β))
-- -- (on_refl  : Π (α : Type u), on_equiv (equiv.refl α) = equiv.refl (f α))
-- -- (on_trans : Π {α β γ : Type u} (d : equiv α β) (e : equiv β γ), on_equiv (equiv.trans d e) = equiv.trans (on_equiv d) (on_equiv e))

-- -- -- Our goal is an automagic proof of the following
-- -- theorem group.transportable : transportable group := sorry

-- -- These we might need to define and prove by hand
-- def Const : Type u → Type v := λ α, punit
-- def Fun : Type u → Type v → Type (max u v) := λ α β, α → β
-- def Prod : Type u → Type v → Type (max u v) := λ α β, α × β
-- def Swap : Type u → Type v → Type (max u v) := λ α β, β × α

-- lemma Const.transportable (α : Type u) : (transportable Const) := sorry
-- lemma Fun.transportable (α : Type u) : (transportable (Fun α)) := sorry
-- lemma Prod.transportable (α : Type u) : (transportable (Prod α)) := sorry
-- lemma Swap.transportable (α : Type u) : (transportable (Swap α)) := sorry


-- -- And then we can define
-- def Hom1 (α : Type u) : Type v → Type (max u v) := λ β, α → β
-- def Hom2 (β : Type v) : Type u → Type (max u v) := λ α, α → β
-- def Aut : Type u → Type u := λ α, α → α

-- -- And hopefully automagically derive
-- lemma Hom1.transportable (α : Type u) : (transportable (Hom1 α)) := sorry
-- lemma Hom2.transportable (β : Type v) : (transportable (Hom1 β)) := sorry
-- lemma Aut.transportable (α : Type u) : (transportable Aut) := sorry

-- -- If we have all these in place...
-- -- A bit of magic might actually be able to derive `group.transportable` on line 11.
-- -- After all, a group just is a type plus some functions... and we can now transport functions.
