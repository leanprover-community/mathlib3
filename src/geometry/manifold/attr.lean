/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import tactic.core

/-!
# Manifold simplifications attribute

In this file we define `mfld_simps` attribute and add it to some lemmas.
-/

mk_simp_attribute mfld_simps "The simpset `mfld_simps` records several simp lemmas that are
especially useful in manifolds. It is a subset of the whole set of simp lemmas, but it makes it
possible to have quicker proofs (when used with `squeeze_simp` or `simp only`) while retaining
readability.

The typical use case is the following, in a file on manifolds:
If `simp [foo, bar]` is slow, replace it with `squeeze_simp [foo, bar] with mfld_simps` and paste
its output. The list of lemmas should be reasonable (contrary to the output of
`squeeze_simp [foo, bar]` which might contain tens of lemmas), and the outcome should be quick
enough.
"

attribute [mfld_simps]
  -- Functions
  id.def function.comp.left_id function.comp_app function.comp.right_id
  -- Sets
  set.mem_set_of_eq
  -- Logic
  true_or or_true true_and and_true eq_self_iff_true and_imp forall_const forall_true_iff
  not_false_iff heq_iff_eq and_self
