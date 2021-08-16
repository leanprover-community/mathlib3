/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.auto_cases
import tactic.chain
import tactic.norm_cast

namespace tactic

namespace tidy
/-- Tag interactive tactics (locally) with `[tidy]` to add them to the list of default tactics
called by `tidy`. -/
@[user_attribute] meta def tidy_attribute : user_attribute := {
  name := `tidy,
  descr := "A tactic that should be called by `tidy`."
}

add_tactic_doc
{ name                     := "tidy",
  category                 := doc_category.attr,
  decl_names               := [`tactic.tidy.tidy_attribute],
  tags                     := ["search"] }

meta def run_tactics : tactic string :=
do names ← attribute.get_instances `tidy,
   first (names.map name_to_tactic) <|> fail "no @[tidy] tactics succeeded"

@[hint_tactic]
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
  intros1                                     >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  auto_cases,
  `[apply_auto_param]                         >> pure "apply_auto_param",
  `[dsimp at *]                               >> pure "dsimp at *",
  `[simp at *]                                >> pure "simp at *",
  ext1_wrapper,
  fsplit                                      >> pure "fsplit",
  injections_and_clear                        >> pure "injections_and_clear",
  propositional_goal >> (`[solve_by_elim])    >> pure "solve_by_elim",
  `[norm_cast]                                >> pure "norm_cast",
  `[unfold_coes]                              >> pure "unfold_coes",
  `[unfold_aux]                               >> pure "unfold_aux",
  tidy.run_tactics ]

meta structure cfg :=
(trace_result : bool            := ff)
(trace_result_prefix : string   := "Try this: ")
(tactics : list (tactic string) := default_tactics)

declare_trace tidy

meta def core (cfg : cfg := {}) : tactic (list string) :=
do
  results ← chain cfg.tactics,
  when (cfg.trace_result) $
    trace (cfg.trace_result_prefix ++ (", ".intercalate results)),
  return results

end tidy

meta def tidy (cfg : tidy.cfg := {}) := tactic.tidy.core cfg >> skip

namespace interactive
open lean.parser interactive

/-- Use a variety of conservative tactics to solve goals.

`tidy?` reports back the tactic script it found. As an example
```lean
example : ∀ x : unit, x = unit.star :=
begin
  tidy? -- Prints the trace message: "Try this: intros x, exact dec_trivial"
end
```

The default list of tactics is stored in `tactic.tidy.default_tidy_tactics`.
This list can be overridden using `tidy { tactics := ... }`.
(The list must be a `list` of `tactic string`, so that `tidy?`
can report a usable tactic script.)

Tactics can also be added to the list by tagging them (locally) with the
`[tidy]` attribute. -/
meta def tidy (trace : parse $ optional (tk "?")) (cfg : tidy.cfg := {}) :=
tactic.tidy { trace_result := trace.is_some, ..cfg }
end interactive

add_tactic_doc
{ name                     := "tidy",
  category                 := doc_category.tactic,
  decl_names               := [`tactic.interactive.tidy],
  tags                     := ["search", "Try this", "finishing"] }

/-- Invoking the hole command `tidy` ("Use `tidy` to complete the goal") runs the tactic of
the same name, replacing the hole with the tactic script `tidy` produces.
-/
@[hole_command] meta def tidy_hole_cmd : hole_command :=
{ name := "tidy",
  descr := "Use `tidy` to complete the goal.",
  action := λ _, do script ← tidy.core,
    return [("begin " ++ (", ".intercalate script) ++ " end", "by tidy")] }

add_tactic_doc
{ name                     := "tidy",
  category                 := doc_category.hole_cmd,
  decl_names               := [`tactic.tidy_hole_cmd],
  tags                     := ["search"] }

end tactic
