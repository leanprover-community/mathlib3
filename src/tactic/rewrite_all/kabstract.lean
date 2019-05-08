-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Keeley Hoek
import tactic.rewrite_all.common

universes u

namespace tactic

meta def kabstract_no_new_goals (t e : expr) (md : transparency) : tactic expr :=
do gs ← get_goals,
   r ← kabstract t e md,
   ng ← num_goals,
   guard (ng = gs.length),
   return r

namespace rewrite_all

meta def kabstracter_aux
  (pattern : tactic (expr × expr × list expr))
  (lhs_replacer : list expr → tactic expr) :
  expr × list (expr × (list expr)) → tactic (expr × list (expr × (list expr)))
| p := do
  (t, L) ← pure p,
  (e, e_type, mvars) ← pattern,
  t' ← kabstract_no_new_goals t e semireducible,
  -- TODO use the discharger to clear remaining metavariables
  guard t'.has_var,
  w ← mk_meta_var e_type,
  let t'' := t'.instantiate_var w,
  mvars' ← mvars.mmap instantiate_mvars,
  return (t'', (w, mvars') :: L)

meta def kabstracter
  (pattern : tactic (expr × expr × list expr))
  (lhs_replacer : list expr → tactic expr) (t : expr) : mllist tactic (expr × list (expr × list expr)) :=
mllist.fix (kabstracter_aux pattern lhs_replacer) (t, [])

meta def get_lhs : expr -> bool → list expr -> tactic (expr × expr × list expr)
| (expr.pi n bi d b) symm mvars :=
do v <- mk_meta_var d,
   b' <- whnf $ b.instantiate_var v,
   get_lhs b' symm (v :: mvars)
| `(%%a = %%b) symm mvars :=
  do let (a, b) := if symm then (b, a) else (a, b),
     ty ← infer_type a,
     return (a, ty, mvars)
| _ _ _ := failed

meta def replacer : expr -> bool → list expr -> tactic expr
| (expr.pi n bi d b) symm values := replacer b symm values
| `(%%a = %%b) symm values :=
  do let (a, b) := if symm then (b, a) else (a, b),
     return (a.instantiate_vars values)
| _ _ _ := failed

meta def mvars_to_var (e : expr) : expr :=
e.replace (λ e n, if e.is_meta_var then some (expr.var n) else none)

meta def do_substitutions
  (eq : expr) (symm : bool)
  (t_original : expr)
  (lhs rhs : list expr → tactic expr)
  (t_abstracted : expr)
  (rewrite_mvar : expr × list expr)
  (restore_mvars : list (expr × list expr)) : tactic (tracked_rewrite × list expr) :=
lock_tactic_state $
do -- We first restore all the "other" metavariables to their original values.
  --  trace "do_substitutions",
   restore_mvars.mmap (λ p, do l ← lhs p.2, unify p.1 l),
   t_restored ← instantiate_mvars t_abstracted,

   -- r' is the value of the remaining metavariable, after applying the lemma.
   r' ← rhs rewrite_mvar.2,

   guard (¬ r'.has_meta_var),
   -- We now begin constructing the `eq.rec` proof of equality. In fact, we don't construct it here,
   -- we just construct a tactic that can produce it on demand!
   let proof_tactic : tactic expr := do {
    -- r is the original value of the remaining metavariable
    r ← lhs rewrite_mvar.2,

    -- The lemma itself proves `r = r'`.
    let inner_proof := rewrite_mvar.2.reverse.foldl (λ f x : expr, f x) eq,
    inner_proof ← if symm then mk_eq_symm inner_proof else return inner_proof,

    -- Next we compute the motive.
    let t_with_var := mvars_to_var t_restored,
    n ← mk_fresh_name,
    ty ← infer_type r,
    feq ← mk_const `eq,
    v ← mk_mvar,
    let C := expr.lam n binder_info.default ty (feq v t_original t_with_var),

    -- ... and prepare the actual proof.
    refl ← mk_eq_refl t_original,
    proof ← to_expr ```(@eq.rec _ %%r %%C %%refl _ %%inner_proof),
    infer_type proof, -- this is a sanity check (perhaps we should be doing this earlier?)
    return proof
   },
   -- Finally we finish rewriting the expression
   unify rewrite_mvar.1 r',
   result ← instantiate_mvars t_restored,

   metas : list expr ← rewrite_mvar.2.mfilter (λ m, do r ← is_assigned m <|> return tt, return ¬ r),
   return (⟨result, proof_tactic, none⟩, metas)

meta def all_rewrites_core (t eq : expr) (symm : bool) : mllist tactic (tracked_rewrite × list expr) :=
mllist.squash $
do ty ← infer_type eq,
   let matcher := get_lhs ty symm [],
   let lhs := replacer ty symm,
   let rhs := replacer ty ¬ symm,
   let L := kabstracter matcher lhs t,
   return $ L.mfilter_map (λ p, do_substitutions eq symm t lhs rhs p.1 p.2.head p.2.tail)

end rewrite_all

open rewrite_all

meta def rewrite_all_lazy (r : expr × bool) (t : expr) (cfg : rewrite_all.cfg := {}) : mllist tactic tracked_rewrite :=
(all_rewrites_core t r.1 r.2).filter_map (λ p, if p.2 = [] then some p.1 else none)

meta def rewrite_all (r : expr × bool) (t : expr) (cfg : rewrite_all.cfg := {}) : tactic (list tracked_rewrite) :=
mllist.force $ rewrite_all_lazy r t cfg

end tactic
