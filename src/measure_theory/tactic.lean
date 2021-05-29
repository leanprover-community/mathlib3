/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import tactic.auto_cases
import tactic.tidy
import tactic.with_local_reducibility
import tactic.show_term
import measure_theory.measure_space_0
/-!
# Tactics for measure theory

Currently we have one domain-specific tactic for measure theory: `measurability`.

This tactic is mostly a copy of the `continuity` tactic.
-/

/-!
### `measurability` tactic

Automatically solve goals of the form `measurable f` and `ae_measurable f μ`.

Mark lemmas with `@[measurability]` to add them to the set of lemmas
used by `measurability`. Note: `to_additive` doesn't know yet how to
copy the attribute to the additive version.
-/

/-- User attribute used to mark tactics used by `measurability`. -/
@[user_attribute]
meta def measurability : user_attribute :=
{ name := `measurability,
  descr := "lemmas usable to prove (ae)-measurability" }

/- Mark some measurability lemmas already defined in `measure_theory.measurable_space_0` and
`measure_theory.measure_space_0` -/
attribute [measurability]
  measurable_id
  measurable_const
  ae_measurable_const
  ae_measurable.measurable_mk

-- As we will be using `apply_rules` with `md := semireducible`,
-- we need another version of `measurable_id`.
@[measurability] lemma measurable_id' {α : Type*} [measurable_space α] : measurable (λ a : α, a) :=
measurable_id

namespace tactic

/--
Tactic to apply `measurable.comp` when appropriate.

Applying `measurable.comp` is not always a good idea, so we have some
extra logic here to try to avoid bad cases.

* If the function we're trying to prove measurable is actually
  constant, and that constant is a function application `f z`, then
  measurable.comp would produce new goals `measurable f`, `measurable
  (λ _, z)`, which is silly. We avoid this by failing if we could
  apply measurable_const.

* measurable.comp will always succeed on `measurable (λ x, f x)` and
  produce new goals `measurable (λ x, x)`, `measurable f`. We detect
  this by failing if a new goal can be closed by applying
  measurable_id.
-/
meta def apply_measurable.comp : tactic unit :=
`[fail_if_success { exact measurable_const };
  refine measurable.comp _ _;
  fail_if_success { exact measurable_id }]

/--
Tactic to apply `measurable.comp_ae_measurable` when appropriate.

Applying `measurable.comp_ae_measurable` is not always a good idea, so we have some
extra logic here to try to avoid bad cases.

* If the function we're trying to prove measurable is actually
  constant, and that constant is a function application `f z`, then
  `measurable.comp_ae_measurable` would produce new goals `measurable f`, `measurable
  (λ _, z)`, which is silly. We avoid this by failing if we could
  apply measurable_const.

* `measurable.comp_ae_measurable` will always succeed on `measurable (λ x, f x)` and
  produce new goals `measurable (λ x, x)`, `measurable f`. We detect
  this by failing if a new goal can be closed by applying
  `measurable_id`.
-/
meta def apply_measurable.comp_ae_measurable : tactic unit :=
`[fail_if_success { exact ae_measurable_const };
  refine measurable.comp_ae_measurable _ _;
  fail_if_success { exact measurable_id }]

/--
We don't want the intros1 tactic to apply to a goal of the form `measurable f`. This tactic tests
the target to see if it matches that form.
 -/
meta def intros_if_not_measurable : tactic unit :=
do t ← tactic.target,
  match t with
  | `(measurable %%l) := done
  | `(ae_measurable %%l %%r) := done
  | _ := skip
  end

/-- List of tactics used by `measurability` internally. -/
meta def measurability_tactics (md : transparency := semireducible) : list (tactic string) :=
[
  propositional_goal >> assumption
                        >> pure "assumption",
  intros_if_not_measurable >> intros1
                        >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  apply_rules [``(measurability)] 50 { md := md }
                        >> pure "apply_rules measurability",
  apply_measurable.comp >> pure "refine measurable.comp _ _",
  apply_measurable.comp_ae_measurable
                        >> pure "refine measurable.comp_ae_measurable _ _",
  `[ refine measurable.ae_measurable _ ]
                        >> pure "refine measurable.ae_measurable _"
]

namespace interactive
setup_tactic_parser

/--
Solve goals of the form `measurable f`. `measurability?` reports back the proof term it found.
-/
meta def measurability
  (bang : parse $ optional (tk "!")) (trace : parse $ optional (tk "?")) (cfg : tidy.cfg := {}) :
  tactic unit :=
let md                 := if bang.is_some then semireducible else reducible,
    measurability_core := tactic.tidy { tactics := measurability_tactics md, ..cfg },
    trace_fn           := if trace.is_some then show_term else id in
trace_fn measurability_core

/-- Version of `measurability` for use with auto_param. -/
meta def measurability' : tactic unit := measurability none none {}

/--
`measurability` solves goals of the form `measurable f` or `ae_measurable f μ` by applying
lemmas tagged with the `measurability` user attribute.

You can also use `measurability!`, which applies lemmas with `{ md := semireducible }`.
The default behaviour is more conservative, and only unfolds `reducible` definitions
when attempting to match lemmas with the goal.

`measurability?` reports back the proof term it found.
-/
add_tactic_doc
{ name := "measurability / measurability'",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.measurability, `tactic.interactive.measurability'],
  tags := ["lemma application"]
}

end interactive

end tactic
