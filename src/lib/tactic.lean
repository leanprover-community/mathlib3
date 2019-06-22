import tactic.basic

universe u

namespace expr
open tactic

meta def simp
  (t : expr) (cfg : simp_config := {}) (discharger : tactic unit := failed)
  (no_defaults := ff) (attr_names : list name := []) (hs : list simp_arg_type := []) :
  tactic (expr × expr) :=
do
  (s, to_unfold) ← mk_simp_set no_defaults attr_names hs,
  simplify s to_unfold t cfg `eq discharger

meta def dsimp
  (t : expr) (cfg : dsimp_config := {})
  (no_defaults := ff) (attr_names : list name := []) (hs : list simp_arg_type := []) :
  tactic expr :=
do
  (s, to_unfold) ← mk_simp_set no_defaults attr_names hs,
  s.dsimplify to_unfold t cfg

meta def is_eq_or_iff_after_binders : expr → bool
| (expr.pi n bi d b) := is_eq_or_iff_after_binders b
| `(%%a = %%b)       := tt
| `(%%a ↔ %%b)       := tt
| _                  := ff

end expr

namespace tactic

meta def type_cast (α : Type u) [reflected α] (n : name) : tactic α :=
  eval_expr α (expr.const n [])

-- FIXME doesn't `unify` do exactly this??
meta def attempt_refl (lhs rhs : expr) : tactic expr :=
lock_tactic_state $
do
  gs ← get_goals,
  m ← to_expr ``(%%lhs = %%rhs) >>= mk_meta_var,
  set_goals [m],
  refl ← mk_const `eq.refl,
  apply_core refl {new_goals := new_goals.non_dep_only},
  instantiate_mvars m

meta def mk_app_aux : expr → expr → expr → tactic expr
 | f (expr.pi n binder_info.default d b) arg := do
   infer_type arg >>= unify d,
   return $ f arg
 | f (expr.pi n binder_info.inst_implicit d b) arg := do
   infer_type arg >>= unify d,
   return $ f arg -- TODO use typeclass inference?
 | f (expr.pi n _ d b) arg := do
   v ← mk_meta_var d,
   t ← whnf (b.instantiate_var v),
   mk_app_aux (f v) t arg
 | e _ _ := failed

-- TODO check if just the first will suffice
meta def mk_app' (f arg : expr) : tactic expr :=
lock_tactic_state $
do r ← to_expr ``(%%f %%arg) /- FIXME too expensive -/ <|> (do infer_type f >>= whnf >>= λ t, mk_app_aux f t arg),
   instantiate_mvars r

/--
Given an expression `e` and  list of expressions `F`, builds all applications of `e` to elements of `F`.
`mk_apps` returns a list of all pairs ``(`(%%e %%f), f)`` which typecheck, for `f` in the list `F`.
-/
meta def mk_apps (e : expr) (F : list expr) : tactic (list (expr × expr)) :=
do
   l ← F.mmap $ λ f, (do r ← try_core (mk_app' e f >>= λ m, return (m, f)), return r.to_list),
   return l.join

end tactic
