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
meta def tidy_attribute : user_attribute := {
  name := `tidy,
  descr := "A tactic that should be called by `tidy`."
}

add_tactic_doc
{ name                     := "tidy",
  category                 := doc_category.attr,
  decl_names               := [`tactic.tidy.tidy_attribute],
  tags                     := ["search"] }

run_cmd attribute.register ``tidy_attribute

/--
Find the first tactic with attribute `@[tidy]` that succeeds,
returning its return value.
-/
meta def run_tactics : tactic string :=
do names ← attribute.get_instances `tidy,
   first (names.map name_to_tactic) <|> fail "no @[tidy] tactics succeeded"

/--
When we run `ext1` as part of `tidy`, we want to use `{apply_cfg . new_goals := new_goals.all}`.
In order to avoid having to include this in the generated tactic script unless it is necessary,
we define here a wrapper for `ext1` that checks the number of new goals and produces
an appropriate tactic script.
-/
@[hint_tactic]
meta def ext1_wrapper : tactic string :=
do ng ← num_goals,
   ext1 [] {apply_cfg . new_goals := new_goals.all},
   ng' ← num_goals,
   return $ if ng' > ng then
     "tactic.ext1 [] {new_goals := tactic.new_goals.all}"
   else "ext1"

/--
The default list of tactics used by the `tidy` tactic.
This list can be overridden using `tidy { tactics := ... }`.

This is a list of `tactic string`s,
each of which is expected to report a tactic invocation which reproduces its effect.
-/
meta def default_tactics : list (tactic string) :=
[ /-
  We have mixed feelings about `refl`.
  On the one hand, including it near the top of `default_tactics` list saves
  about 60s in compiling mathlib (as of July 2020).
  On the other hand, it potentially makes `tidy` very slow, as it is willing to tackle "heavy `rfl`"
  problems, even when other tactics would be more advisable.

  As a compromise, we run `refl` inside a `try_for` wrapper.
  The time limit was chosen as a smallest value for which we get the full compilation time benefits
  (in fact a slight overall improvement).
  -/
  `[try_for 25 { refl }]                      >> pure "refl",
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

/--
The configuration settings for `tidy`.

The main use is overriding the list of tactics used, via `tidy { tactics := ... }`.
(The list must be a `list` of `tactic string`, so that `tidy?`
can report a usable tactic script.)
-/
meta structure cfg :=
(trace_result : bool            := ff)
(trace_result_prefix : string   := "Try this: ")
(tactics : list (tactic string) := default_tactics)

declare_trace tidy

/--
The non-interactive implementation of the `tidy` tactic,
returning a list of strings representing the discovered tactic script.
-/
meta def core (cfg : cfg := {}) : tactic (list string) :=
do
  results ← chain cfg.tactics,
  when (cfg.trace_result) $
    trace (cfg.trace_result_prefix ++ (", ".intercalate results)),
  return results

end tidy

/--
A non-interactive version of the tidy tactic, as a `tactic unit`,
suitable for use as an `auto_param`.
-/
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
