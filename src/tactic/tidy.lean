-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tactic
import tactic.auto_cases
import tactic.chain
import tactic.interactive

namespace tactic

namespace tidy
meta def tidy_attribute : user_attribute := {
  name := `tidy,
  descr := "A tactic that should be called by `tidy`."
}

run_cmd attribute.register ``tidy_attribute

meta def name_to_tactic (n : name) : tactic string :=
do d ← get_decl n,
   e ← mk_const n,
   let t := d.type,
   if (t =ₐ `(tactic unit)) then
     (eval_expr (tactic unit) e) >>= (λ t, t >> pure n.to_string)
   else if (t =ₐ `(tactic string)) then
     (eval_expr (tactic string) e) >>= (λ t, t)
   else fail "invalid type for @[tidy] tactic"

meta def run_tactics : tactic string :=
do names ← attribute.get_instances `tidy,
   first (names.map name_to_tactic) <|> fail "no @[tidy] tactics succeeded"

meta def ext1_wrapper : tactic string :=
do ng ← num_goals,
   ext1 [] {apply_cfg . new_goals := new_goals.all},
   ng' ← num_goals,
   return $ if ng' > ng then
     "tactic.ext1 [] {new_goals := tactic.new_goals.all}"
   else "ext1"

meta def default_tactics : list (tactic string) :=
[ reflexivity                                 >> pure "refl",
  `[exact dec_trivial]                        >> pure "exact dec_trivial",
  propositional_goal >> assumption            >> pure "assumption",
  ext1_wrapper,
  intros1                                     >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  auto_cases,
  `[apply_auto_param]                         >> pure "apply_auto_param",
  `[dsimp at *]                               >> pure "dsimp at *",
  `[simp at *]                                >> pure "simp at *",
  fsplit                                      >> pure "fsplit",
  injections_and_clear                        >> pure "injections_and_clear",
  propositional_goal >> (`[solve_by_elim])    >> pure "solve_by_elim",
  `[unfold_aux]                               >> pure "unfold_aux",
  tidy.run_tactics ]

meta structure cfg :=
(trace_result : bool            := ff)
(trace_result_prefix : string   := "/- `tidy` says -/ ")
(tactics : list (tactic string) := default_tactics)

declare_trace tidy

meta def core (cfg : cfg := {}) : tactic (list string) :=
do
  results ← chain cfg.tactics,
  when (cfg.trace_result ∨ is_trace_enabled_for `tidy) $
    trace (cfg.trace_result_prefix ++ (", ".intercalate results)),
  return results

end tidy

meta def tidy (cfg : tidy.cfg := {}) := tactic.tidy.core cfg >> skip

namespace interactive
open lean.parser interactive

meta def tidy (trace : parse $ optional (tk "?")) (cfg : tidy.cfg := {}) :=
tactic.tidy { trace_result := trace.is_some, ..cfg }
end interactive

@[hole_command] meta def tidy_hole_cmd : hole_command :=
{ name := "tidy",
  descr := "Use `tidy` to complete the goal.",
  action := λ _, do script ← tidy.core, return [("begin " ++ (", ".intercalate script) ++ " end", "by tidy")] }

end tactic
