/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/

namespace tactic

open tactic.interactive (casesm constructor_matching)
open list

meta def match_head (e : expr) : expr → tactic unit
| e' :=
    unify e e'
<|> do `(_ → %%e') ← whnf e',
       v ← mk_mvar,
       match_head (e'.instantiate_var v)

meta def find_matching_head : expr → list expr → tactic (list expr)
| e []         := return []
| e (H :: Hs) :=
  do t ← infer_type H,
     (cons H <$ match_head e t <|> pure id) <*> find_matching_head e Hs

/--
  `xassumption` looks for an assumption of the form `... → ∀ _, ... → head`
  where `head` matches the current goal.

  alternatively, when encountering an assumption of the form `sg₀ → ¬ sg₁`,
  after the main approach failed, the goal is dismissed and `sg₀` and `sg₁`
  are made into the new goal.

  optional arguments:
  - asms: list of rules to consider instead of the local constants
  - tac:  a tactic to run on each subgoals after applying an assumption; if
          this tactic fails, the corresponding assumption will be rejected and
          the next one will be attempted.
 -/
meta def xassumption
  (asms : option (list expr) := none)
  (tac : tactic unit := return ()) : tactic unit :=
do { ctx ← asms.to_monad <|> local_context,
     t   ← target,
     hs   ← find_matching_head t ctx,
     hs.any_of (λ H, () <$ tactic.apply H ; tac) } <|>
do { exfalso,
     ctx ← asms.to_monad <|> local_context,
     t   ← target,
     hs   ← find_matching_head t ctx,
     hs.any_of (λ H, () <$ tactic.apply H ; tac) }
<|> fail "assumption tactic failed"

open nat

/--
  `auto` calls `xassumption` on the main goal to find an assumption whose head matches
  and repeated calls `xassumption` on the generated subgoals until no subgoals remains
  or up to `depth` times.

  `auto` discharges the current goal or fails

  `auto` does some back-tracking if `xassumption` chooses an unproductive assumption

  optional arguments:
  - asms: list of assumptions / rules to consider instead of local constants
  - depth: number of attempts at discharging generated sub-goals
  -/
meta def auto (asms : option (list expr) := none)  : opt_param ℕ 3 → tactic unit
| 0 := done
| (succ n) :=
xassumption asms $ auto n

/--
  `tauto` breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`
  and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be discharged
  using `reflexivity` or `auto`
-/
meta def tauto : tactic unit :=
repeat (do
  gs ← get_goals,
  () <$ intros ;
  casesm (some ()) [``(_ ∧ _),``(_ ∨ _),``(Exists _)] ;
  constructor_matching (some ()) [``(_ ∧ _),``(_ ↔ _)],
  gs' ← get_goals,
  guard (gs ≠ gs') ) ;
repeat
(reflexivity <|> auto <|> constructor_matching none [``(_ ∧ _),``(_ ↔ _),``(Exists _)]) ;
done

run_cmd add_interactive [`auto,`xassumption,`tauto]

end tactic
