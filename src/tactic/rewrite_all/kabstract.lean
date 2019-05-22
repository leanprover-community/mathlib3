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

namespace rewrite_all.kabstract

open rewrite_all

meta mutual def try_mvarify_list, mvarify_one_var (e_type : expr)
with try_mvarify_list : list expr → tactic (list expr × option expr)
| (e :: rest) :=
  do (e, m) ← mvarify_one_var e,
    match m with
    | some m := return (e :: rest, m)
    | none := do (l, m) ← try_mvarify_list rest, return (e :: l, m)
    end
| [] := return ([], none)
with mvarify_one_var : expr → tactic (expr × option expr)
| (expr.var n) :=
  if n = 0 then do m ← mk_meta_var e_type, return (m, m)
  else return (expr.var n, none)
| (expr.local_const n n' bi t) :=
  do (t, ms) ← mvarify_one_var t,
    return (expr.local_const n n' bi t, ms)
| (expr.app f a) :=
  do ([f, a], m) ← try_mvarify_list [f, a],
    return (expr.app f a, m)
| (expr.lam n bi t v) :=
  do ([t, v], m) ← try_mvarify_list [t, v],
    return (expr.lam n bi t v, m)
| (expr.pi n bi t v) :=
  do ([t, v], m) ← try_mvarify_list [t, v],
    return (expr.pi n bi t v, m)
| (expr.elet n nt nv v) :=
  do ([t, v], m) ← try_mvarify_list [nt, nv, v],
    return (expr.elet n nt nv v, m)
| (expr.macro mc es) :=
  do (l, m) ← try_mvarify_list es,
    return (expr.macro mc l, m)
| e := return (e, none)

meta def mvarify_all_vars (e_type : expr) : expr → tactic (list (expr × expr))
| e := do (e, m) ← mvarify_one_var e_type e,
          match m with
          | none := return []
          | some m := list.cons (e, m) <$> mvarify_all_vars e
          end

meta def kabstracter_aux
  (pattern : tactic (expr × expr × list expr))
  (lhs_replacer : list expr → tactic expr) :
  expr × list (expr × (list expr)) →
  tactic ((expr × list (expr × (list expr))) × list (expr × list (expr × (list expr))))
| p := do
  (t, L) ← pure p,
  (e, e_type, mvars) ← pattern,
  t ← kabstract_no_new_goals t e semireducible,
  -- TODO use the discharger to clear remaining metavariables
  guard t.has_var,

  mvars ← mvars.mmap instantiate_mvars,

  l ← mvarify_all_vars e_type t,
  guard $ l.length > 0,

  let l := l.map $ λ p, (p.1.instantiate_var e, p.2),
  let ll := l.foldl (λ ll p, let (ll, L) := ll in
    let L' := list.cons (p.2, mvars) L in (ll ++ [(p.1, L')], L')
  ) ([], L),

  return (ll.1.ilast, ll.1)

meta def kabstracter
  (pattern : tactic (expr × expr × list expr))
  (lhs_replacer : list expr → tactic expr) (t : expr) : mllist tactic (expr × list (expr × list expr)) :=
mllist.fixl (λ a, kabstracter_aux pattern lhs_replacer a) (t, [])

meta def get_lhs : expr → bool → list expr → tactic (expr × expr × list expr)
| (expr.pi n bi d b) symm mvars :=
do v ← mk_meta_var d,
   b' ← whnf $ b.instantiate_var v,
   get_lhs b' symm (v :: mvars)
| `(%%a = %%b) symm mvars :=
  do let (a, b) := if symm then (b, a) else (a, b),
     ty ← infer_type a,
     return (a, ty, mvars)
| _ _ _ := failed

meta def replacer : expr → bool → list expr → tactic expr
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
   restore_mvars.mmap (λ p, do l ← lhs p.2, unify p.1 l),
   t_restored ← instantiate_mvars t_abstracted,

   -- r' is the value of the remaining metavariable, after applying the lemma.
   r' ← rhs rewrite_mvar.2,

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

meta def rewrite_all_lazy (t : expr) (r : expr × bool) (cfg : rewrite_all.cfg := {}) : mllist tactic tracked_rewrite :=
(all_rewrites_core t r.1 r.2).filter_map (λ p, if p.2 = [] then some p.1 else none)

meta def rewrite_all (t : expr) (r : expr × bool) (cfg : rewrite_all.cfg := {}) : tactic (list tracked_rewrite) :=
mllist.force $ rewrite_all_lazy t r cfg

end rewrite_all.kabstract

end tactic
