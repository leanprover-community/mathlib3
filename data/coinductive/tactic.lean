import .basic

namespace tactic
open lean.parser interactive interactive.types
open tactic.interactive (generalize cases_arg_p)
local postfix `?`:9000 := optional

meta def lambdas : list expr → expr → tactic expr
| (v@(expr.local_const uniq pp info _) :: es) f := do
  t ← infer_type v,
  f' ← lambdas es f,
  return $ expr.lam pp info t $ expr.abstract_local f' uniq
| _ f := return f

meta def co_cases (pat : parse cases_arg_p) (ns : parse with_ident_list) : tactic unit :=
do ls ← local_context,
   e ← to_expr pat.2,
   ls ← ls.mfilter (λ h, do
     t ← infer_type h,
     return $ e.occurs t),
   n ← revert_lst ls,
   generalize e `p,
   p ← intro1,
   t ← target,
   lam ← lambdas [p] t,
   refine ``(@cofix.cases _ _ %%lam _ %%p),
   clear p,
   when (e.is_local_constant ∧ pat.1.is_none) (clear e),
   intro_lst $ ns.take 2,
   intron (2 - ns.length),
   target >>= head_beta >>= change,
   intron n

lemma cast_eq_of_heq {α β} {x : α} {y : β}
  (h : α = β)
  (h' : cast h x = y)
: x == y :=
by { subst β, subst y, symmetry, simp [cast_heq] }

run_cmd add_interactive [`co_cases]

end tactic
