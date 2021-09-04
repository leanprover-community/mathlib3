/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Mario Carneiro
-/
import tactic.ext

open interactive

namespace tactic

/-
This file defines a `chain` tactic, which takes a list of tactics,
and exhaustively tries to apply them to the goals, until no tactic succeeds on any goal.

Along the way, it generates auxiliary declarations, in order to speed up elaboration time
of the resulting (sometimes long!) proofs.

This tactic is used by the `tidy` tactic.
-/

-- α is the return type of our tactics. When `chain` is called by `tidy`, this is string,
-- describing what that tactic did as an interactive tactic.
variable {α : Type}

inductive tactic_script (α : Type) : Type
| base : α → tactic_script
| work (index : ℕ) (first : α) (later : list tactic_script) (closed : bool) : tactic_script

meta def tactic_script.to_string : tactic_script string → string
| (tactic_script.base a) := a
| (tactic_script.work n a l c) :=  "work_on_goal " ++ (to_string n) ++
    " { " ++ (", ".intercalate (a :: l.map tactic_script.to_string)) ++ " }"

meta instance : has_to_string (tactic_script string) :=
{ to_string := λ s, s.to_string }

meta instance tactic_script_unit_has_to_string : has_to_string (tactic_script unit) :=
{ to_string := λ s, "[chain tactic]" }

meta def abstract_if_success (tac : expr → tactic α) (g : expr) : tactic α :=
do
  type ← infer_type g,
  is_lemma ← is_prop type,
  if is_lemma then -- there's no point making the abstraction, and indeed it's slower
    tac g
  else do
    m ← mk_meta_var type,
    a ← tac m,
    do {
      val ← instantiate_mvars m,
      guard (val.list_meta_vars = []),
      c  ← new_aux_decl_name,
      gs ← get_goals,
      set_goals [g],
      add_aux_decl c type val ff >>= unify g,
      set_goals gs }
    <|> unify m g,
    return a

/--
`chain_many tac` recursively tries `tac` on all goals, working depth-first on generated subgoals,
until it no longer succeeds on any goal. `chain_many` automatically makes auxiliary definitions.
-/
meta mutual def chain_single, chain_many, chain_iter {α} (tac : tactic α)
with chain_single : expr → tactic (α × list (tactic_script α)) | g :=
do set_goals [g],
  a ← tac,
  l ← get_goals >>= chain_many,
  return (a, l)
with chain_many : list expr → tactic (list (tactic_script α))
| [] := return []
| [g] := do {
  (a, l) ← chain_single g,
  return (tactic_script.base a :: l) } <|> return []
| gs := chain_iter gs []
with chain_iter : list expr → list expr → tactic (list (tactic_script α))
| [] _ := return []
| (g :: later_goals) stuck_goals := do {
  (a, l) ← abstract_if_success chain_single g,
  new_goals ← get_goals,
  let w := tactic_script.work stuck_goals.length a l (new_goals = []),
  let current_goals := stuck_goals.reverse ++ new_goals ++ later_goals,
  set_goals current_goals, -- we keep the goals up to date, so they are correct at the end
  l' ← chain_many current_goals,
  return (w :: l') } <|> chain_iter later_goals (g :: stuck_goals)

meta def chain_core {α : Type} [has_to_string (tactic_script α)] (tactics : list (tactic α)) :
  tactic (list string) :=
do results ← (get_goals >>= chain_many (first tactics)),
   when results.empty (fail "`chain` tactic made no progress"),
   return (results.map to_string)

variables [has_to_string (tactic_script α)] [has_to_format α]

declare_trace chain

meta def trace_output (t : tactic α) : tactic α :=
do tgt ← target,
   r ← t,
   name ← decl_name,
   trace format!"`chain` successfully applied a tactic during elaboration of {name}:",
   tgt ← pp tgt,
   trace format!"previous target: {tgt}",
   trace format!"tactic result: {r}",
   tgt ← try_core target,
   tgt ← match tgt with
          | (some tgt) := pp tgt
          | none       := return "no goals"
          end,
   trace format!"new target: {tgt}",
   pure r

meta def chain (tactics : list (tactic α)) : tactic (list string) :=
chain_core
  (if is_trace_enabled_for `chain then (tactics.map trace_output) else tactics)

end tactic
