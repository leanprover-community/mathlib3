-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tactic
import tactic.auto_cases
import tactic.chain
import tactic.interactive

open tactic

meta def tidy_attribute : user_attribute := {
  name := `tidy,
  descr := "A tactic that should be called by `tidy`."
}

run_cmd attribute.register `tidy_attribute

meta def name_to_tactic (n : name) : tactic (tactic string) := 
do e ← mk_const n,
   (eval_expr (tactic string) e) <|> 
   (eval_expr (tactic unit) e) >>= (λ t, pure (t >> pure n.to_string))

meta def run_tidy_tactics : tactic string :=
do names ← attribute.get_instances `tidy,
   tactics ← names.mmap name_to_tactic,
   first tactics <|> fail "no @[tidy] tactics succeeded"

meta def default_tidy_tactics : list (tactic string) :=
[ reflexivity                                 >> pure "refl", 
  `[exact dec_trivial]                        >> pure "exact dec_trivial",
  propositional_goal >> assumption            >> pure "assumption",
  `[ext1]                                     >> pure "ext1",
  intro_at_least_once                         >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  auto_cases,
  `[apply_auto_param]                         >> pure "apply_auto_param",
  `[dsimp at *]                               >> pure "dsimp at *",
  `[simp at *]                                >> pure "simp at *",
  fsplit                                      >> pure "fsplit", 
  injections_and_clear                        >> pure "injections_and_clear",
  propositional_goal >> (`[solve_by_elim])    >> pure "solve_by_elim",
  `[unfold_aux]                               >> pure "unfold_aux",
  run_tidy_tactics ]

meta structure tidy_cfg extends chain_cfg :=
(trace_result : bool            := ff)
(trace_result_prefix : string   := "/- obviously says -/ ")
(tactics : list (tactic string) := default_tidy_tactics)

meta def tidy (cfg : tidy_cfg := {}) : tactic unit :=
do
  results ← chain cfg.to_chain_cfg cfg.tactics,
  if cfg.trace_result then
    trace (cfg.trace_result_prefix ++ (", ".intercalate results))
  else
    tactic.skip
