/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import tactic.linarith.verification
import tactic.linarith.preprocessing

/-!
# `linarith`: solving linear arithmetic goals

`linarith` is a tactic for solving goals with linear arithmetic.

Suppose we have a set of hypotheses in `n` variables
`S = {a₁x₁ + a₂x₂ + ... + aₙxₙ R b₁x₁ + b₂x₂ + ... + bₙxₙ}`,
where `R ∈ {<, ≤, =, ≥, >}`.
Our goal is to determine if the inequalities in `S` are jointly satisfiable, that is, if there is
an assignment of values to `x₁, ..., xₙ` such that every inequality in `S` is true.

Specifically, we aim to show that they are *not* satisfiable. This amounts to proving a
contradiction. If our goal is also a linear inequality, we negate it and move it to a hypothesis
before trying to prove `false`.

When the inequalities are over a dense linear order, `linarith` is a decision procedure: it will
prove `false` if and only if the inequalities are unsatisfiable. `linarith` will also run on some
types like `ℤ` that are not dense orders, but it will fail to prove `false` on some unsatisfiable
problems. It will run over concrete types like `ℕ`, `ℚ`, and `ℝ`, as well as abstract types that
are instances of `linear_ordered_comm_ring`.

## Algorithm sketch

First, the inequalities in the set `S` are rearranged into the form `tᵢ Rᵢ 0`, where
`Rᵢ ∈ {<, ≤, =}` and each `tᵢ` is of the form `∑ cⱼxⱼ`.

`linarith` uses an untrusted oracle to search for a certificate of unsatisfiability.
The oracle searches for a list of natural number coefficients `kᵢ` such that `∑ kᵢtᵢ = 0`, where for
at least one `i`, `kᵢ > 0` and `Rᵢ = <`.

Given a list of such coefficients, `linarith` verifies that `∑ kᵢtᵢ = 0` using a normalization
tactic such as `ring`. It proves that `∑ kᵢtᵢ < 0` by transitivity, since each component of the sum
is either equal to, less than or equal to, or less than zero by hypothesis. This produces a
contradiction.

## Preprocessing

`linarith` does some basic preprocessing before running. Most relevantly, inequalities over natural
numbers are cast into inequalities about integers, and rational division by numerals is canceled
into multiplication. We do this so that we can guarantee the coefficients in the certificate are
natural numbers, which allows the tactic to solve goals over types that are not fields.

Preprocessors are allowed to branch, that is, to case split on disjunctions. `linarith` will succeed
overall if it succeeds in all cases. This leads to exponential blowup in the number of `linarith`
calls, and should be used sparingly. The default preprocessor set does not include case splits.

## Fourier-Motzkin elimination

The oracle implemented to search for certificates uses Fourier-Motzkin variable elimination.
This technique transorms a set of inequalities in `n` variables to an equisatisfiable set in `n - 1`
variables. Once all variables have been eliminated, we conclude that the original set was
unsatisfiable iff the comparison `0 < 0` is in the resulting set.

While performing this elimination, we track the history of each derived comparison. This allows us
to represent any comparison at any step as a positive combination of comparisons from the original
set. In particular, if we derive `0 < 0`, we can find our desired list of coefficients
by counting how many copies of each original comparison appear in the history.

## Implementation details

`linarith` homogenizes numerical constants: the expression `1` is treated as a variable `t₀`.

Often `linarith` is called on goals that have comparison hypotheses over multiple types. This
creates multiple `linarith` problems, each of which is handled separately; the goal is solved as
soon as one problem is found to be contradictory.

Disequality hypotheses `t ≠ 0` do not fit in this pattern. `linarith` will attempt to prove equality
goals by splitting them into two weak inequalities and running twice. But it does not split
disequality hypotheses, since this would lead to a number of runs exponential in the number of
disequalities in the context.

The Fourier-Motzkin oracle is very modular. It can easily be replaced with another function of type
`certificate_oracle := list comp → ℕ → tactic (rb_map ℕ ℕ)`,
which takes a list of comparisons and the largest variable
index appearing in those comparisons, and returns a map from comparison indices to coefficients.
An alternate oracle can be specified in the `linarith_config` object.

A variant, `nlinarith`, adds an extra preprocessing step to handle some basic nonlinear goals.
There is a hook in the `linarith_config` configuration object to add custom preprocessing routines.

The certificate checking step is *not* by reflection. `linarith` converts the certificate into a
proof term of type `false`.

Some of the behavior of `linarith` can be inspected with the option
`set_option trace.linarith true`.
Because the variable elimination happens outside the tactic monad, we cannot trace intermediate
steps there.

## File structure

The components of `linarith` are spread between a number of files for the sake of organization.

* `lemmas.lean` contains proofs of some arithmetic lemmas that are used in preprocessing and in
  verification.
* `datatypes.lean` contains data structures that are used across multiple files, along with some
  useful auxiliary functions.
* `preprocessing.lean` contains functions used at the beginning of the tactic to transform
  hypotheses into a shape suitable for the main routine.
* `parsing.lean` contains functions used to compute the linear structure of an expression.
* `elimination.lean` contains the Fourier-Motzkin elimination routine.
* `verification.lean` contains the certificate checking functions that produce a proof of `false`.
* `frontend.lean` contains the control methods and user-facing components of the tactic.

## Tags

linarith, nlinarith, lra, nra, Fourier Motzkin, linear arithmetic, linear programming
-/

open tactic native

namespace linarith

/-! ### Control -/

/--
If `e` is a comparison `a R b` or the negation of a comparison `¬ a R b`, found in the target,
`get_contr_lemma_name_and_type e` returns the name of a lemma that will change the goal to an
implication, along with the type of `a` and `b`.

For example, if `e` is `(a : ℕ) < b`, returns ``(`lt_of_not_ge, ℕ)``.
-/
meta def get_contr_lemma_name_and_type : expr → option (name × expr)
| `(@has_lt.lt %%tp %%_ _ _) := return (`lt_of_not_ge, tp)
| `(@has_le.le %%tp %%_ _ _) := return (`le_of_not_gt, tp)
| `(@eq %%tp _ _) := return (``eq_of_not_lt_of_not_gt, tp)
| `(@ne %%tp _ _) := return (`not.intro, tp)
| `(@ge %%tp %%_ _ _) := return (`le_of_not_gt, tp)
| `(@gt %%tp %%_ _ _) := return (`lt_of_not_ge, tp)
| `(¬ @has_lt.lt %%tp %%_ _ _) := return (`not.intro, tp)
| `(¬ @has_le.le %%tp %%_ _ _) := return (`not.intro, tp)
| `(¬ @eq %%tp _ _) := return (``not.intro, tp)
| `(¬ @ge %%tp %%_ _ _) := return (`not.intro, tp)
| `(¬ @gt %%tp %%_ _ _) := return (`not.intro, tp)
| _ := none

/--
`apply_contr_lemma` inspects the target to see if it can be moved to a hypothesis by negation.
For example, a goal `⊢ a ≤ b` can become `a > b ⊢ false`.
If this is the case, it applies the appropriate lemma and introduces the new hypothesis.
It returns the type of the terms in the comparison (e.g. the type of `a` and `b` above) and the
newly introduced local constant.
Otherwise returns `none`.
-/
meta def apply_contr_lemma : tactic (option (expr × expr)) :=
do t ← target,
   match get_contr_lemma_name_and_type t with
   | some (nm, tp) :=
     do refine ((expr.const nm []) pexpr.mk_placeholder), v ← intro1, return $ some (tp, v)
   | none := return none
   end

/--
`partition_by_type l` takes a list `l` of proofs of comparisons. It sorts these proofs by
the type of the variables in the comparison, e.g. `(a : ℚ) < 1` and `(b : ℤ) > c` will be separated.
Returns a map from a type to a list of comparisons over that type.
-/
meta def partition_by_type (l : list expr) : tactic (rb_lmap expr expr) :=
l.mfoldl (λ m h, do tp ← ineq_prf_tp h, return $ m.insert tp h) mk_rb_map

/--
Given a list `ls` of lists of proofs of comparisons, `try_linarith_on_lists cfg ls` will try to
prove `false` by calling `linarith` on each list in succession. It will stop at the first proof of
`false`, and fail if no contradiction is found with any list.
-/
meta def try_linarith_on_lists (cfg : linarith_config) (ls : list (list expr)) : tactic expr :=
(first $ ls.map $ prove_false_by_linarith cfg) <|> fail "linarith failed to find a contradiction"

/--
Given a list `hyps` of proofs of comparisons, `run_linarith_on_pfs cfg hyps pref_type`
preprocesses `hyps` according to the list of preprocessors in `cfg`.
This results in a list of branches (typically only one),
each of which must succeed in order to close the goal.

In each branch, we partition the  list of hypotheses by type, and run `linarith` on each class
in the partition; one of these must succeed in order for `linarith` to succeed on this branch.
If `pref_type` is given, it will first use the class of proofs of comparisons over that type.
-/
meta def run_linarith_on_pfs (cfg : linarith_config) (hyps : list expr) (pref_type : option expr) :
  tactic unit :=
let single_process := λ hyps : list expr, do
   linarith_trace_proofs
     ("after preprocessing, linarith has " ++ to_string hyps.length ++ " facts:") hyps,
   hyp_set ← partition_by_type hyps,
   linarith_trace format!"hypotheses appear in {hyp_set.size} different types",
   match pref_type with
   | some t := prove_false_by_linarith cfg (hyp_set.ifind t) <|>
               try_linarith_on_lists cfg (rb_map.values (hyp_set.erase t))
   | none := try_linarith_on_lists cfg (rb_map.values hyp_set)
   end in
let preprocessors := cfg.preprocessors.get_or_else default_preprocessors,
    preprocessors := if cfg.split_ne then linarith.remove_ne::preprocessors else preprocessors in
do hyps ← preprocess preprocessors hyps,
hyps.mmap' $ λ hs, do set_goals [hs.1], single_process hs.2 >>= exact

/--
`filter_hyps_to_type restr_type hyps` takes a list of proofs of comparisons `hyps`, and filters it
to only those that are comparisons over the type `restr_type`.
-/
meta def filter_hyps_to_type (restr_type : expr) (hyps : list expr) : tactic (list expr) :=
hyps.mfilter $ λ h, do
  ht ← infer_type h,
  match get_contr_lemma_name_and_type ht with
  | some (_, htype) := succeeds $ unify htype restr_type
  | none := return ff
  end

/-- A hack to allow users to write `{restr_type := ℚ}` in configuration structures. -/
meta def get_restrict_type (e : expr) : tactic expr :=
do m ← mk_mvar,
   unify `(some %%m : option Type) e,
   instantiate_mvars m

end linarith

/-! ### User facing functions -/

open linarith

/--
`linarith reduce_semi only_on hyps cfg` tries to close the goal using linear arithmetic. It fails
if it does not succeed at doing this.

* If `reduce_semi` is true, it will unfold semireducible definitions when trying to match atomic
expressions.
* `hyps` is a list of proofs of comparisons to include in the search.
* If `only_on` is true, the search will be restricted to `hyps`. Otherwise it will use all
  comparisons in the local context.
-/
meta def tactic.linarith (reduce_semi : bool) (only_on : bool) (hyps : list pexpr)
  (cfg : linarith_config := {}) : tactic unit :=
focus1 $
do t ← target,
-- if the target is an equality, we run `linarith` twice, to prove ≤ and ≥.
if t.is_eq.is_some then
  linarith_trace "target is an equality: splitting" >>
    seq' (applyc ``eq_of_not_lt_of_not_gt) tactic.linarith else
do hyps ← hyps.mmap $ λ e, i_to_expr e >>= note_anon none,
   when cfg.split_hypotheses (linarith_trace "trying to split hypotheses" >> try auto.split_hyps),
/- If we are proving a comparison goal (and not just `false`), we consider the type of the
   elements in the comparison to be the "preferred" type. That is, if we find comparison
   hypotheses in multiple types, we will run `linarith` on the goal type first.
   In this case we also recieve a new variable from moving the goal to a hypothesis.
   Otherwise, there is no preferred type and no new variable; we simply change the goal to `false`.
-/
   pref_type_and_new_var_from_tgt ← apply_contr_lemma,
   when pref_type_and_new_var_from_tgt.is_none $
     if cfg.exfalso then linarith_trace "using exfalso" >> exfalso
     else fail "linarith failed: target is not a valid comparison",
   let cfg := cfg.update_reducibility reduce_semi,
   let (pref_type, new_var) :=
     pref_type_and_new_var_from_tgt.elim (none, none) (λ ⟨a, b⟩, (some a, some b)),
   -- set up the list of hypotheses, considering the `only_on` and `restrict_type` options
   hyps ← if only_on then return (new_var.elim [] singleton ++ hyps)
          else (++ hyps) <$> local_context,
   hyps ← (do t ← get_restrict_type cfg.restrict_type_reflect, filter_hyps_to_type t hyps) <|>
     return hyps,
   linarith_trace_proofs "linarith is running on the following hypotheses:" hyps,
   run_linarith_on_pfs cfg hyps pref_type

setup_tactic_parser

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
this tactic is not complete for these theories and will not prove every true goal. It will solve
goals over arbitrary types that instantiate `linear_ordered_comm_ring`.

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

The option `set_option trace.linarith true` will trace certain intermediate stages of the `linarith`
routine.
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
