/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.definability
import tactic.auto_cases
import tactic.tidy
import tactic.with_local_reducibility
/-!
# Tactics for model theory
Currently we have one domain-specific tactic for model theory: `definability`.
This tactic is to a large extent a copy of the `continuity` tactic by Reid Barton and the
  `measurability` tactic by Rémy Degenne.

## TODO:
* Once definable functions are defined, port the `continuity`/`measurability` tactics for functions.
-/

open first_order.language

/-!
### `definability` tactic
Automatically solve goals of the form `L.definable A s`.
Mark lemmas with `@[definability]` to add them to the set of lemmas used by `definability`.
-/

/-- User attribute used to mark tactics used by `definability`. -/
@[user_attribute]
meta def definability : user_attribute :=
{ name := `definability,
  descr := "lemmas usable to prove definability" }

/- Mark some definability lemmas already defined in `model_theory.definability`. -/
attribute [definability]
  definable_empty
  definable_univ
  definable.inter
  definable.union
  definable_finset_inf
  definable_finset_sup
  definable_finset_bInter
  definable_finset_bUnion
  definable.compl
  definable.sdiff
  definable.preimage_comp
  definable.image_comp_equiv

namespace tactic

/--
We don't want the intro1 tactic to apply to a goal of the form `L.definable A s`. This tactic tests
the target to see if it matches that form.
 -/
meta def goal_is_not_definable : tactic unit :=
do t ← tactic.target,
  match t with
  | `(definable %%L %%A %%s) := failed
  | _ := skip
  end

/-- List of tactics used by `definability` internally. -/
meta def definability_tactics (md : transparency := semireducible) : list (tactic string) :=
[
  propositional_goal >> apply_assumption
                        >> pure "apply_assumption",
  goal_is_not_definable >> intro1
                        >>= λ ns, pure ("intro " ++ ns.to_string),
  apply_rules [``(definability)] 50 { md := md }
                        >> pure "apply_rules definability"
]

namespace interactive
setup_tactic_parser

/--
Solve goals of the form `definable f`, `ae_definable f μ` or `definable_set s`.
`definability?` reports back the proof term it found.
-/
meta def definability
  (bang : parse $ optional (tk "!")) (trace : parse $ optional (tk "?")) (cfg : tidy.cfg := {}) :
  tactic unit :=
let md                 := if bang.is_some then semireducible else reducible,
    definability_core := tactic.tidy { tactics := definability_tactics md, ..cfg },
    trace_fn           := if trace.is_some then show_term else id in
trace_fn definability_core

/-- Version of `definability` for use with auto_param. -/
meta def definability' : tactic unit := definability none none {}

/--
`definability` solves goals of the form `L.definable A s`
by applying lemmas tagged with the `definability` user attribute.
You can also use `definability!`, which applies lemmas with `{ md := semireducible }`.
The default behaviour is more conservative, and only unfolds `reducible` definitions
when attempting to match lemmas with the goal.
`definability?` reports back the proof term it found.
-/
add_tactic_doc
{ name := "definability / definability'",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.definability, `tactic.interactive.definability'],
  tags := ["lemma application"] }

end interactive

end tactic
