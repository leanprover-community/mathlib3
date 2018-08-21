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

#check @cofix
meta def co_cases (pat : parse cases_arg_p) (ns : parse with_ident_list) : tactic unit :=
do ls ← local_context,
   e ← to_expr pat.2,
   ls ← ls.mfilter (λ h, do
     t ← infer_type h,
     return $ e.occurs t),
   n ← revert_lst ls,
   generalize e `p,
   -- generalize i `p,
   -- i ← intro1,
   p ← intro1,
   ι ← mk_mvar, α ← mk_mvar, β ← mk_mvar, γ ← mk_mvar, i ← mk_mvar,
   t ← infer_type p,
   to_expr ``(@cofix %%ι %%α %%β %%γ %%i) >>= unify t,
   t ← target,
   lam ← lambdas [i,p] t,
   refine ``(@cofix.cases _ _ _ _ _ _ _ %%p),
   clear p,
   when (e.is_local_constant ∧ pat.1.is_none) (clear e),
   i ← instantiate_mvars i,
   clear i,
   intro_lst $ ns.take 3,
   intron (3 - ns.length),
   target >>= head_beta >>= change,
   intron n

-- #check @cofix.cases

lemma cast_eq_of_heq {α β} {x : α} {y : β}
  (h : α = β)
  (h' : cast h x = y)
: x == y :=
by { subst β, subst y, symmetry, simp [cast_heq] }

run_cmd add_interactive [`co_cases]

end tactic

example {ι} {α : ι → Type*} {β : Π i, α i → Type*} {γ : Π i a, β i a → ι} (i : ι) (x : cofix γ i) : x = x :=
begin
  -- revert i,
  co_cases x,
  refl
end

#check @cofix
