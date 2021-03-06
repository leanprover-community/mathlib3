import tactic.auto_cases
import tactic.tidy
import tactic.with_local_reducibility
import tactic.show_term
import analysis.calculus.fderiv


/-- User attribute used to mark tactics used by `differentiability`. -/
@[user_attribute]
meta def differentiability : user_attribute :=
{ name := `differentiability,
  descr := "lemmas usable to prove differentiablility" }

-- Mark some differentiability lemmas already defined in `topology.basic`
attribute [differentiability]
  differentiable_at_id
  differentiable_at_const

-- As we will be using `apply_rules` with `md := semireducible`,
-- we need another version of `differentiable_id`.
@[differentiability] lemma differentiable_at_id_t
    {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
    {E : Type*} [normed_group E] [normed_space 𝕜 E] {x : E} : differentiable_at 𝕜 id x :=
(has_fderiv_at_id x).differentiable_at

namespace tactic

meta def apply_differentiability.comp : tactic unit :=
`[fail_if_success { exact differentiable_at_const };
  refine differentiable_at.comp _ _;
  fail_if_success { exact differentiable_at_id }]

/-- List of tactics used by `differentiability` internally. -/
meta def differentiability_tactics (md : transparency := reducible) : list (tactic string) :=
[
  intros1               >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  apply_rules [``(differentiability)] 50 { md := md }
                        >> pure "apply_rules differentiablity",
  apply_differentiability.comp >> pure "refine differentiable_at.comp _ _"
]

namespace interactive
setup_tactic_parser

/--
Solve goals of the form `differentiable f`. `differentiability?` reports back the proof term it found.
-/
meta def differentiability
  (bang : parse $ optional (tk "!")) (trace : parse $ optional (tk "?")) (cfg : tidy.cfg := {}) : tactic unit :=
let md              := if bang.is_some then semireducible else reducible,
    differentiability_core := tactic.tidy { tactics := differentiability_tactics md, ..cfg },
    trace_fn        := if trace.is_some then show_term else id in
trace_fn differentiability_core

/-- Version of `differentiability` for use with auto_param. -/
meta def differentiability' : tactic unit := differentiability none none {}

/--
`differentiability` solves goals of the form `differentiable f` by applying lemmas tagged with the
`differentiability` user attribute.

I have no idea what it does, I just stole Reid's code and changed a few things.

You can also use `differentiability!`, which applies lemmas with `{ md := semireducible }`.
The default behaviour is more conservative, and only unfolds `reducible` definitions
when attempting to match lemmas with the goal.

`differentiability?` reports back the proof term it found.
-/
add_tactic_doc
{ name := "differentiability / differentiability'",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.differentiability, `tactic.interactive.differentiability'],
  tags := ["lemma application"]
}

end interactive

end tactic
