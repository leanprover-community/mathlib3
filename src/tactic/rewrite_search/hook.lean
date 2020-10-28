/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/
import tactic.nth_rewrite
import tactic.rewrite_search.common

/-!
# FIXME: what is this?


open tactic
open tactic.nth_rewrite.congr

namespace tactic.rewrite_search

meta def rewrite_progress := mllist tactic rewrite

meta def progress_init (rs : list (expr × bool)) (exp : expr) (cfg : config) : rewrite_progress :=
(all_rewrites_lazy_of_list rs exp cfg.to_cfg).map $ λ t, ⟨t.1.exp, t.1.proof, how.rewrite t.2.1 t.2.2 t.1.addr⟩

meta def progress_next (prog : rewrite_progress) : tactic (rewrite_progress × option rewrite) :=
do u ← mllist.uncons prog,
   match u with
   | (some (r, p)) := return (p, (some r))
   | none          := return (mllist.nil, none)
   end

meta def simp_rewrite (exp : expr) : tactic rewrite := do
  (simp_exp, simp_prf) ← exp.simp,
  return ⟨simp_exp, pure simp_prf, how.simp⟩

meta def discover_more_rewrites
  (rs : list (expr × bool)) (exp : expr) (cfg : config) (_ : side)
  (prog : option rewrite_progress) :
  tactic (option rewrite_progress × list rewrite) :=
do
  (prog, head) ← match prog with
         | some prog := pure (prog, [])
         | none := do
          let prog := progress_init rs exp cfg,
          sl ← if cfg.try_simp then option.to_list <$> tactic.try_core (simp_rewrite exp)
                               else pure [],
          pure (prog, sl)
         end,
  (prog, rw) ← progress_next prog,
  return (some prog, head.append rw.to_list)

end tactic.rewrite_search
-/
