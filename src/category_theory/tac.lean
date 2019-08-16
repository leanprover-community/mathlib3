
import tactic
import category_theory.category

namespace tactic
open expr  list
meta def dep_vars : expr → tactic (list expr)
| (pi n bi d b) :=
  if b.has_var then
    do v ← mk_local' n bi d,
       cons v <$> dep_vars (b.instantiate_var v)
  else pure []
| _ := pure []

@[hole_command]
meta def my_cmd : hole_command :=
{ name := "introv",
  descr := "introv",
  action := λ xs,
    do t ← target,
       vs ← dep_vars t,
       let r : string := string.intercalate " " (vs.map (to_string ∘ local_pp_name)),
       pure [(sformat!"λ {r}, _","")] }

open interactive lean.parser category_theory

@[user_command]
meta def reassoc_cmd (_ : parse $ tk "reassoc_axiom") : lean.parser unit :=
do n ← ident,
   of_tactic' $
   do n ← resolve_constant n,
      d ← get_decl n,
      let ls := d.univ_params.map level.param,
      let c := @expr.const tt n ls,
      (vs,t) ← infer_type c >>= mk_local_pis,
      (vs',t) ← whnf t >>= mk_local_pis,
      let vs := vs ++ vs',
      (lhs,rhs) ← match_eq t,
      `(@category_struct.comp _ %%struct_inst _ _ _ _ _) ← pure lhs,
      `(@has_hom.hom _ %%hom_inst %%X %%Y) ← infer_type lhs,
      C ← infer_type X,
      X' ← mk_local' `X' binder_info.implicit C,
      ft ← to_expr ``(@has_hom.hom _ %%hom_inst %%Y %%X'),
      f' ← mk_local_def `f' ft,
      t' ← to_expr ``(@category_struct.comp _ %%struct_inst _ _ _%%lhs %%f' = @category_struct.comp _ %%struct_inst _ _ _ %%rhs %%f'),
      let c' := c.mk_app vs,
      (_,pr) ← solve_aux t' (rewrite_target c'; reflexivity),
      pr ← instantiate_mvars pr,
      s ← simp_lemmas.mk.add_simp ``category.assoc,
      (t'',pr') ← simplify s [] t',
      pr' ← mk_eq_mp pr' pr,
      t'' ← pis (vs ++ [X',f']) t'',
      pr' ← lambdas (vs ++ [X',f']) pr',
      let n' := n.append_suffix "_assoc",
      add_decl $ declaration.thm n' d.univ_params t'' (pure pr'),
      copy_attribute `simp n tt n'

end tactic
