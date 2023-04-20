/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.big_operators.order
import algebra.module.basic
import combinatorics.simple_graph.density

/-!
# Energy of a partition

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the energy of a partition.

The energy is the auxiliary quantity that drives the induction process in the proof of Szemerédi's
Regularity Lemma. As long as we do not have a suitable equipartition, we will find a new one that
has an energy greater than the previous one plus some fixed constant.
-/

open finset
open_locale big_operators

variables {α : Type*} [decidable_eq α] {s : finset α} (P : finpartition s) (G : simple_graph α)
  [decidable_rel G.adj]

namespace finpartition

/-- The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity
lemma.  -/
def energy : ℚ := (∑ uv in P.parts.off_diag, G.edge_density uv.1 uv.2 ^ 2) / P.parts.card ^ 2

lemma energy_nonneg : 0 ≤ P.energy G :=
div_nonneg (finset.sum_nonneg $ λ _ _, sq_nonneg _) $ sq_nonneg _

lemma energy_le_one : P.energy G ≤ 1 :=
div_le_of_nonneg_of_le_mul (sq_nonneg _) zero_le_one $
  calc ∑ uv in P.parts.off_diag, G.edge_density uv.1 uv.2^2
        ≤ P.parts.off_diag.card • 1
        : sum_le_card_nsmul _ _ 1 $ λ uv _, (sq_le_one_iff $ G.edge_density_nonneg _ _).2 $
            G.edge_density_le_one _ _
    ... = P.parts.off_diag.card : nat.smul_one_eq_coe _
    ... ≤ _ : by { rw [off_diag_card, one_mul, ←nat.cast_pow, nat.cast_le, sq], exact tsub_le_self }

end finpartition
