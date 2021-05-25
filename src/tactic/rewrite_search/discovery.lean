/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/
import tactic.nth_rewrite
import tactic.rewrite_search.types

/-!
# Generating a list of rewrites to use as steps in rewrite search.
-/

namespace tactic.rewrite_search

open tactic tactic.interactive tactic.rewrite_search

/--
Convert a list of expressions into a list of rules. The difference is that a rule
includes a flag for direction, so this simply includes each expression twice,
once in each direction.
-/
private meta def rules_from_exprs (l : list expr) : list (expr × bool) :=
l.map (λ e, (e, ff)) ++ l.map (λ e, (e, tt))

/-- Returns true if expression is an equation or iff. -/
private meta def is_acceptable_rewrite : expr → bool
| (expr.pi n bi d b) := is_acceptable_rewrite b
| `(%%a = %%b)       := tt
| `(%%a ↔ %%b)       := tt
| _                  := ff

/-- Returns true if the expression is an equation or iff and has no metavariables. -/
private meta def is_acceptable_hyp (r : expr) : tactic bool :=
do t ← infer_type r >>= whnf, return $ is_acceptable_rewrite t ∧ ¬t.has_meta_var

/-- Collect all hypotheses in the local context that are usable as rewrite rules. -/
private meta def rules_from_hyps : tactic (list (expr × bool)) :=
do hyps ← local_context,
  rules_from_exprs <$> hyps.mfilter is_acceptable_hyp

/-- Use this attribute to make `rewrite_search` use this definition during search. -/
@[user_attribute]
meta def rewrite_search_attr : user_attribute :=
{ name := `rewrite,
  descr := "declare that this definition should be considered by `rewrite_search`" }

/-- Gather rewrite rules from lemmas explicitly tagged with `rewrite. -/
private meta def rules_from_rewrite_attr : tactic (list (expr × bool)) :=
do names ← attribute.get_instances `rewrite,
  rules_from_exprs <$> names.mmap mk_const

/--
Collect rewrite rules to use from the environment.
-/
meta def collect_rules : tactic (list (expr × bool)) :=
do from_attr    ← rules_from_rewrite_attr,
  from_hyps     ← rules_from_hyps,
  return $ from_attr ++ from_hyps

open tactic.nth_rewrite tactic.nth_rewrite.congr

/--
Constructing our rewrite structure from the `tracked_rewrite` provided by `nth_rewrite`.
rule_index is the index of the rule used from the rules provided.
tracked is an (index, tracked_rewrite) pair for the element of `all_rewrites exp rule` we used.
-/
private meta def from_tracked (rule_index : ℕ) (tracked : ℕ × tracked_rewrite) : rewrite :=
do let (rw_index, rw) := tracked,
  let h : how := ⟨rule_index, rw_index, rw.addr⟩,
  ⟨rw.exp, rw.proof, h⟩

/--
Get all rewrites that start at the given expression and use the given rewrite rule.
-/
private meta def rewrites_for_rule (exp : expr) (cfg : config) (numbered_rule: ℕ × expr × bool) :
  tactic (list rewrite) :=
do let (rule_index, rule) := numbered_rule,
  tracked ← all_rewrites exp rule cfg.to_cfg,
  return (list.map (from_tracked rule_index) tracked.enum)

/--
Get all rewrites that start at the given expression and use one of the given rewrite rules.
-/
meta def get_rewrites (rules : list (expr × bool)) (exp : expr) (cfg : config) :
  tactic (buffer rewrite) :=
do lists ← list.mmap (rewrites_for_rule exp cfg) rules.enum,
  return (list.foldl buffer.append_list buffer.nil lists)

end tactic.rewrite_search
