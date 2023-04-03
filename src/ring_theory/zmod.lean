/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import algebra.squarefree
import data.zmod.basic
import ring_theory.int.basic

/-!
# Ring theoretic facts about `zmod n`

We collect a few facts about `zmod n` that need some ring theory to be proved/stated

## Main statements

* `is_reduced_zmod` - `zmod n` is reduced for all squarefree `n`.
-/

@[simp] lemma is_reduced_zmod {n : ℕ} : is_reduced (zmod n) ↔ squarefree n ∨ n = 0 :=
by rw [← ring_hom.ker_is_radical_iff_reduced_of_surjective
    (zmod.ring_hom_surjective $ int.cast_ring_hom $ zmod n),
  zmod.ker_int_cast_ring_hom, ← is_radical_iff_span_singleton,
  is_radical_iff_squarefree_or_zero, int.squarefree_coe_nat, nat.cast_eq_zero]

instance {n : ℕ} [fact $ squarefree n] : is_reduced (zmod n) :=
is_reduced_zmod.2 $ or.inl $ fact.out _
