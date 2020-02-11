/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

The `simp_rw` tactic, a mix of `simp` and `rewrite`.
-/
import tactic.core

/-!
# The `simp_rw` tactic

This module defines a tactic `simp_rw` which functions as a mix of `simp` and
`rw`. Like `rw`, it applies each rewrite rule in the given order, but like
`simp` it repeatedly applies these rules and also under binders like `∀ x, ...`,
`∃ x, ...` and `λ x, ...`.

## Implementation notes

The tactic works by taking each rewrite rule in turn and applying `simp only` to
it. It should be possible to support backwards rewriting in the tactic, i.e.
`simp_rw [←lemma]`, but it will be more useful and not much more work to add
support for this directly to `simp`.
-/

namespace tactic.interactive
open interactive interactive.types tactic

/-- `simp_rw` is a mix of `simp` and `rw`: it applies rewrite rules in the given order repeatedly,
  and can also rewrite under binders like `λ x, ...`

  Usage:
    - `simp_rw [l₁, ..., lₙ]` will rewrite the goal by applying lemmas `l₁, ..., lₙ` in that order.
    - `simp_rw [l₁, ..., lₙ] at h₁ ... hₙ` will rewrite hypotheses `h₁, ..., hₙ` in that order.
      Include `⊢` to also rewrite the goal.
    - `simp_rw [l₁, ..., lₙ] at *` will rewrite in the whole context.

  Lemmas passed to `simp_rw` must be expressions that are valid arguments to `simp`.
-/
meta def simp_rw (q : parse rw_rules) (l : parse location) : tactic unit :=
q.rules.mmap' (λ rule, if rule.symm
  then fail "simp_rw [← ...] not supported: can only rewrite in forward direction"
  else do
    save_info rule.pos,
    simp none tt [simp_arg_type.expr rule.rule] [] l) -- equivalent to `simp only [rule] at l`

end tactic.interactive
