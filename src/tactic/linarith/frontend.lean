/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import tactic.linarith.linarith

/-!
# The `linarith` frontend

This file contains the interactive frontend for `linarith` and the variant `nlinarith`.

## Tags

linarith, nlinarith, lra, nra, Fourier Motzkin, linear arithmetic, linear programming
-/

setup_tactic_parser
open linarith

/--
Tries to prove a goal of `false` by linear arithmetic on hypotheses.
If the goal is a linear (in)equality, tries to prove it by contradiction.
If the goal is not `false` or an inequality, applies `exfalso` and tries linarith on the
hypotheses.

* `linarith` will use all relevant hypotheses in the local context.
* `linarith [t1, t2, t3]` will add proof terms t1, t2, t3 to the local context.
* `linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
  `h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.
* `linarith!` will use a stronger reducibility setting to identify atoms.

Config options:
* `linarith {exfalso := ff}` will fail on a goal that is neither an inequality nor `false`
* `linarith {restrict_type := T}` will run only on hypotheses that are inequalities over `T`
* `linarith {discharger := tac}` will use `tac` instead of `ring` for normalization.
  Options: `ring2`, `ring SOP`, `simp`
* `linarith {split_hypotheses := ff}` will not destruct conjunctions in the context.
-/
meta def tactic.interactive.linarith (red : parse ((tk "!")?))
  (restr : parse ((tk "only")?)) (hyps : parse pexpr_list?)
  (cfg : linarith_config := {}) : tactic unit :=
tactic.linarith red.is_some restr.is_some (hyps.get_or_else []) cfg

add_hint_tactic "linarith"

/--
`linarith` attempts to find a contradiction between hypotheses that are linear (in)equalities.
Equivalently, it can prove a linear inequality by assuming its negation and proving `false`.

In theory, `linarith` should prove any goal that is true in the theory of linear arithmetic over
the rationals. While there is some special handling for non-dense orders like `nat` and `int`,
this tactic is not complete for these theories and will not prove every true goal.

An example:
```lean
example (x y z : ℚ) (h1 : 2*x  < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0)  : false :=
by linarith
```

`linarith` will use all appropriate hypotheses and the negation of the goal, if applicable.

`linarith [t1, t2, t3]` will additionally use proof terms `t1, t2, t3`.

`linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
`h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.

`linarith!` will use a stronger reducibility setting to try to identify atoms. For example,
```lean
example (x : ℚ) : id x ≥ x :=
by linarith
```
will fail, because `linarith` will not identify `x` and `id x`. `linarith!` will.
This can sometimes be expensive.

`linarith {discharger := tac, restrict_type := tp, exfalso := ff}` takes a config object with five
optional arguments:
* `discharger` specifies a tactic to be used for reducing an algebraic equation in the
  proof stage. The default is `ring`. Other options currently include `ring SOP` or `simp` for basic
  problems.
* `restrict_type` will only use hypotheses that are inequalities over `tp`. This is useful
  if you have e.g. both integer and rational valued inequalities in the local context, which can
  sometimes confuse the tactic.
* `transparency` controls how hard `linarith` will try to match atoms to each other. By default
  it will only unfold `reducible` definitions.
* If `split_hypotheses` is true, `linarith` will split conjunctions in the context into separate
  hypotheses.
* If `exfalso` is false, `linarith` will fail when the goal is neither an inequality nor `false`.
  (True by default.)

A variant, `nlinarith`, does some basic preprocessing to handle some nonlinear goals.
-/
add_tactic_doc
{ name       := "linarith",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.linarith],
  tags       := ["arithmetic", "decision procedure", "finishing"] }

/--
An extension of `linarith` with some preprocessing to allow it to solve some nonlinear arithmetic
problems. (Based on Coq's `nra` tactic.) See `linarith` for the available syntax of options,
which are inherited by `nlinarith`; that is, `nlinarith!` and `nlinarith only [h1, h2]` all work as
in `linarith`. The preprocessing is as follows:

* For every subterm `a ^ 2` or `a * a` in a hypothesis or the goal,
  the assumption `0 ≤ a ^ 2` or `0 ≤ a * a` is added to the context.
* For every pair of hypotheses `a1 R1 b1`, `a2 R2 b2` in the context, `R1, R2 ∈ {<, ≤, =}`,
  the assumption `0 R' (b1 - a1) * (b2 - a2)` is added to the context (non-recursively),
  where `R ∈ {<, ≤, =}` is the appropriate comparison derived from `R1, R2`.
-/
meta def tactic.interactive.nlinarith (red : parse ((tk "!")?))
  (restr : parse ((tk "only")?)) (hyps : parse pexpr_list?)
  (cfg : linarith_config := {}) : tactic unit :=
tactic.linarith red.is_some restr.is_some (hyps.get_or_else [])
  { cfg with preprocessors := some $
      cfg.preprocessors.get_or_else default_preprocessors ++ [nlinarith_extras] }

add_hint_tactic "nlinarith"

add_tactic_doc
{ name       := "nlinarith",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.nlinarith],
  tags       := ["arithmetic", "decision procedure", "finishing"] }
