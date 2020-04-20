/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Keeley Hoek
-/
import tactic.nth_rewrite.basic
import tactic.core

namespace tactic

/-- Sometimes `mk_congr_arg` fails, when the function is 'superficially dependent'.
This hack `dsimp`s the function before building the `congr_arg` expression.

Unfortunately it creates some dummy hypotheses that I can't work out how to dispose of cleanly. -/
meta def mk_congr_arg_using_dsimp' (G W : expr) (u : list name) : tactic expr :=
do s ← simp_lemmas.mk_default,
   t ← infer_type G,
   t' ← s.dsimplify u t {fail_if_unchanged := ff},
   definev `_mk_congr_arg_aux t' G,
   to_expr ```(congr_arg _mk_congr_arg_aux %%W)

namespace nth_rewrite.congr

open nth_rewrite

/-- A "lens" for looking into the subterms of an expression, tracking where we've been, so that
when we "zoom out" after making a change we know exactly which order of `congr_fun`s and
`congr_arg`s we need to make things work.

You're supposed to think of an `expr_lens` as a big set of nested applications with a single
hole which needs to be filled, either in a function spot or argument spot. `expr_lens.fill` can
fill this hole and turn your lens back into a real `expr`. -/
meta inductive expr_lens
| app_fun : expr_lens → expr → expr_lens
| app_arg : expr_lens → expr → expr_lens
| entire  : expr_lens

namespace expr_lens

/-- Convert an `expr_lens` into a list of instructions need to build it; repeatedly inspecting a
function or its argument a finite number of times. -/
meta def to_sides : expr_lens → list side
| entire        := []
| (app_fun l _) := l.to_sides.concat side.R
| (app_arg l _) := l.to_sides.concat side.L

/-- Fill the function or argument hole in this lens with the given `expr`. -/
meta def fill : expr_lens → expr → expr
| entire        e := e
| (app_fun l f) x := l.fill (expr.app f x)
| (app_arg l x) f := l.fill (expr.app f x)

private meta def trace_congr_error (f : expr) (x_eq : expr) : tactic unit :=
do pp_f ← pp f,
   pp_f_t ← (infer_type f >>= λ t, pp t),
   pp_x_eq ← pp x_eq,
   pp_x_eq_t ← (infer_type x_eq >>= λ t, pp t),
   trace format!"expr_lens.congr failed on \n{pp_f} : {pp_f_t}\n{pp_x_eq} : {pp_x_eq_t}"

/-- Turn an `e : expr_lens` and a proof that `a = b` into a series of `congr_arg` or `congr_fun`
applications showing that the expressions obtained from `e.fill a` and `e.fill b` are equal. -/
meta def congr : expr_lens → expr → tactic expr
| entire e_eq        := pure e_eq
| (app_fun l f) x_eq := do fx_eq ← try_core $ do {
                             mk_congr_arg f x_eq
                             <|> mk_congr_arg_using_dsimp' f x_eq [`has_coe_to_fun.F]
                           },
                           match fx_eq with
                           | (some fx_eq) := l.congr fx_eq
                           | none         := trace_congr_error f x_eq >> failed
                           end
| (app_arg l x) f_eq := mk_congr_fun f_eq x >>= l.congr

/-- Pretty print a lens. -/
meta def to_tactic_string : expr_lens → tactic string
| entire := return "(entire)"
| (app_fun l f) := do pp ← pp f,
                      rest ← l.to_tactic_string,
                      return sformat!"(fun \"{pp}\" {rest})"
| (app_arg l x) := do pp ← pp x,
                      rest ← l.to_tactic_string,
                      return sformat!"(arg \"{pp}\" {rest})"

end expr_lens

/-- The private internal function used by `app_map`, which "does the work". -/
private meta def app_map_aux {α} (F : expr_lens → expr → tactic (list α)) :
  expr_lens → expr → tactic (list α)
| l (expr.app f x) := list.join <$> monad.sequence [
    F l (expr.app f x),
    app_map_aux (expr_lens.app_arg l x) f,
    app_map_aux (expr_lens.app_fun l f) x
  ] <|> pure []
| l e := F l e <|> pure []

/-- Map a function `F` which understands `expr_lens`es over the given `e : expr` in the natural way;
that is, make holes in `e` everywhere where that is possible (generating `expr_lens`es in the
process), and at each stage call the function `F` passing both the `expr_lens` generated and the
`expr` which was removed to make the hole.

At each stage `F` returns a list of some type, and `app_map` collects these lists together and
returns a concatenation of them all. -/
meta def app_map {α} (F : expr_lens → expr → tactic (list α)) : expr → tactic (list α) :=
app_map_aux F expr_lens.entire

/-- Helper function which just tries to rewrite `e` using the equality `r` without assigning any
metavariables in the tactic state, and without creating any metavariables which cannot be
discharged by `cfg.discharger` in the process. -/
meta def rewrite_without_new_mvars
  (r : expr) (e : expr) (cfg : nth_rewrite.cfg := {}) : tactic (expr × expr) :=
lock_tactic_state $ -- This makes sure that we forget everything in between rewrites;
                    -- otherwise we don't correctly find everything!
do (new_t, prf, metas) ← rewrite_core r e { cfg.to_rewrite_cfg with md := semireducible },
   try_apply_opt_auto_param cfg.to_apply_cfg metas,
   set_goals metas,
   all_goals (try cfg.discharger),
   done,
   prf ← instantiate_mvars prf, -- This is necessary because of the locked tactic state.
   return (new_t, prf)

/-- Returns true if the argument is a proof that the entire expression was rewritten.

This is a bit of a hack: we manually inspect the proof that `rewrite_core` produced, and deduce from
that whether or not the entire expression was rewritten.-/
meta def rewrite_is_of_entire : expr → bool
| `(@eq.rec _ %%term %%C %%p _ _) :=
  match C with
  | `(λ p, _ = p) := tt
  | _ := ff
  end
| _ := ff

/-- Function which tries to perform the rewrite associated to the equality `r : expr × bool` (the
bool indicates whether we should flip the equality first), at the position pointed to by
`l : expr_lens`, by rewriting `e : expr`. If this succeeds, `rewrite_at_lens` computes (by unwinding
`l`) a proof that the entire expression represented by `l.fill e` is equal to the entire expression
`l.fill f`, where `f` is the `expr` which has replaced `e` due to the rewrite. It then returns the
singleton list containing this rewrite (and the tracking data needed to reconstruct it directly). If
it fails, it just returns the empty list. -/
meta def rewrite_at_lens
  (cfg : nth_rewrite.cfg) (r : expr × bool) (l : expr_lens) (e : expr) :
  tactic (list tracked_rewrite) :=
do
  (v, pr) ← rewrite_without_new_mvars r.1 e {cfg with symm := r.2},
  -- Now we determine whether the rewrite transforms the entire expression or not:
  if ¬(rewrite_is_of_entire pr) then return []
  else do
    let w := l.fill v,
    qr ← l.congr pr,
    s ← try_core (cfg.simplifier w),
    (w, qr) ← match s with
              | none           := pure (w, qr)
              | some (w', qr') := do
                qr ← mk_eq_trans qr qr',
                return (w', qr)
              end,
    return [⟨w, pure qr, l.to_sides⟩]

/-- List of all rewrites of an expression `e` by `r : expr × bool`.
Here `r.1` is the substituting expression and `r.2` flags the direction of the rewrite. -/
meta def nth_rewrite (e : expr) (r : expr × bool) (cfg : nth_rewrite.cfg := {}) :
  tactic (list tracked_rewrite) :=
app_map (rewrite_at_lens cfg r) e

/-- Lazy list of all rewrites of an expression `e` by `r : expr × bool`.
Here `r.1` is the substituting expression and `r.2` flags the direction of the rewrite. -/
meta def nth_rewrite_lazy (e : expr) (r : expr × bool) (cfg : nth_rewrite.cfg := {}) :
  mllist tactic tracked_rewrite :=
mllist.squash $ mllist.of_list <$> nth_rewrite e r cfg

end nth_rewrite.congr

end tactic
