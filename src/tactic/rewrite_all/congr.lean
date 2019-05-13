-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Keeley Hoek
import tactic.rewrite_all.common

namespace tactic

-- Sometimes `mk_congr_arg` fails, when the function is 'superficially dependent'.
-- This hack `dsimp`s the function before building the `congr_arg` expression.
-- Unfortunately it creates some dummy hypotheses that I can't work out how to dispose of cleanly.
meta def mk_congr_arg_using_dsimp (G W : expr) (u : list name) : tactic expr :=
do s ← simp_lemmas.mk_default,
   t ← infer_type G,
   t' ← s.dsimplify u t {fail_if_unchanged := ff},
   definev `_mk_congr_arg_aux t' G,
   to_expr ```(congr_arg _mk_congr_arg_aux %%W)

namespace rewrite_all

meta inductive expr_lens
| app_fun : expr_lens → expr → expr_lens
| app_arg : expr_lens → expr → expr_lens
| entire  : expr_lens

open expr_lens

meta def expr_lens.to_sides : expr_lens → list side
| entire             := []
| (app_fun l _)      := l.to_sides.concat side.R
| (app_arg l _)      := l.to_sides.concat side.L

meta def expr_lens.replace : expr_lens → expr → expr
| entire        e := e
| (app_fun l f) x := expr_lens.replace l (expr.app f x)
| (app_arg l x) f := expr_lens.replace l (expr.app f x)

private meta def trace_congr_error (f : expr) (x_eq : expr) : tactic unit := do
  pp_f ← pp f,
  pp_f_t ← (infer_type f >>= λ t, pp t),
  pp_x_eq ← pp x_eq,
  pp_x_eq_t ← (infer_type x_eq >>= λ t, pp t),
  trace format!"expr_lens.congr failed on \n{pp_f} : {pp_f_t}\n{pp_x_eq} : {pp_x_eq_t}"

meta def expr_lens.congr : expr_lens → expr → tactic expr
| entire e_eq        := pure e_eq
| (app_fun l f) x_eq := do
  fx_eq ← try_core $
    mk_congr_arg f x_eq
    <|> mk_congr_arg_using_dsimp f x_eq [`has_coe_to_fun.F],
  match fx_eq with
  | (some fx_eq) := expr_lens.congr l fx_eq
  | none         := trace_congr_error f x_eq >> failed
  end
| (app_arg l x) f_eq := mk_congr_fun f_eq x >>= expr_lens.congr l

meta def expr_lens.to_tactic_string : expr_lens → tactic string
| entire := return "(entire)"
| (app_fun l f) := do
  pp ← pp f,
  rest ← l.to_tactic_string,
  return sformat!"(fun \"{pp}\" {rest})"
| (app_arg l x) := do
  pp ← pp x,
  rest ← l.to_tactic_string,
  return sformat!"(arg \"{pp}\" {rest})"

private meta def app_map_aux {α} (F : expr_lens → expr → tactic (list α)) :
  expr_lens → expr → tactic (list α)
| l (expr.app f x) := list.join <$> monad.sequence [
    F l (expr.app f x),
    app_map_aux (expr_lens.app_arg l x) f,
    app_map_aux (expr_lens.app_fun l f) x
  ] <|> pure []
| l e := F l e <|> pure []

meta def app_map {α} (F : expr_lens → expr → tactic (list α)) : expr → tactic (list α)
| e := app_map_aux F expr_lens.entire e

meta def rewrite_without_new_mvars (r : expr) (e : expr) (cfg : rewrite_all.cfg := {}) : tactic (expr × expr) :=
lock_tactic_state $ -- This makes sure that we forget everything in between rewrites;
                    -- otherwise we don't correctly find everything!
do (new_t, prf, metas) ← rewrite_core r e { cfg.to_rewrite_cfg with md := semireducible },
   try_apply_opt_auto_param cfg.to_apply_cfg metas,
   set_goals metas,
   all_goals (try cfg.discharger),
   done,
   prf ← instantiate_mvars prf, -- This is necessary because of the locked tactic state.
   return (new_t, prf)

-- This is a bit of a hack: we manually inspect the proof that `rewrite_core`
-- produced, and deduce from that whether or not the entire expression was rewritten.
meta def rewrite_is_of_entire : expr → bool
| `(@eq.rec _ %%term %%C %%p _ _) :=
  match C with
  | `(λ p, _ = p) := tt
  | _ := ff
  end
| _ := ff

meta def rewrite_at_lens
  (cfg : rewrite_all.cfg) (r : expr × bool) (l : expr_lens) (e : expr) :
  tactic (list tracked_rewrite) :=
do
  (v, pr) ← rewrite_without_new_mvars r.1 e {cfg with symm := r.2},
  -- Now we determine whether the rewrite transforms the entire expression or not:
  if ¬(rewrite_is_of_entire pr) then return []
  else do
    let w := l.replace v,
    qr ← l.congr pr,
    s ← try_core (cfg.simplifier w),
    (w, qr) ← match s with
              | none           := pure (w, qr)
              | some (w', qr') := do
                qr ← mk_eq_trans qr qr',
                return (w', qr)
              end,
    return [⟨w, pure qr, l.to_sides⟩]

end rewrite_all

open rewrite_all

meta def rewrite_all (e : expr) (r : expr × bool) (cfg : rewrite_all.cfg := {}) :
  tactic (list tracked_rewrite) :=
app_map (rewrite_at_lens cfg r) e

meta def rewrite_all_lazy (e : expr) (r : expr × bool) (cfg : rewrite_all.cfg := {}) :
  mllist tactic tracked_rewrite :=
mllist.squash $ mllist.of_list <$> rewrite_all e r cfg

end tactic
