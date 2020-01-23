/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

The `simp_rw` tactic, a mix of `simp` and `rewrite`.
-/
import tactic.core

namespace tactic.interactive
open interactive interactive.types tactic

/-- `simp_rw` is a version of `simp` which performs rewriting in the given order.
  Conversely, `simp_rw` is a version of `rw` that applies rewrite rules repeatedly and
  also under binders like `∀ x, ...`, `∃ x, ...` and `λ x, ...`.

  Usage:
    - `simp_rw [lemma_1, ..., lemma_n]` will rewrite the goal by applying the lemmas in that order.
    - `simp_rw [lemma] at h` will rewrite hypothesis `h` using the given lemma.

  Lemmas passed to `simp_rw` must be expressions that are valid arguments to `simp`.
  Backwards rewriting, i.e. `simp_rw [←lemma]`, is not supported (yet).
-/
meta def simp_rw (q : parse rw_rules) (l : parse location) : tactic unit :=
q.rules.mmap' (λ rule, if rule.symm
  then fail "simp_rw can only rewrite in forward direction"
  else do
    save_info rule.pos,
    simp none tt [simp_arg_type.expr rule.rule] [] l) -- equivalent to `simp only [rule] at l`

end tactic.interactive
