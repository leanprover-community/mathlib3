/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .uniform

/-!
# Energy of a partition

This file defines the energy of a partition. The energy is the auxiliary quantity that drives the
induction process in the proof of Szemerédi's Regularity Lemma (see `increment`). As long as we do
not have a suitable equipartition, we will find a new one that has an energy greater than the
previous one plus some fixed constant.
-/

open finset
open_locale big_operators

variables {α : Type*} [decidable_eq α] {s : finset α} (P : finpartition s) (G : simple_graph α)
  [decidable_rel G.adj]

namespace finpartition

/-- The energy of a partition. -/
def energy (P : finpartition s) : ℚ :=
(∑ UV in P.parts.off_diag, G.edge_density UV.1 UV.2^2)/P.parts.card^2

lemma energy_nonneg (P : finpartition s) : 0 ≤ P.energy G :=
div_nonneg (finset.sum_nonneg (λ _ _, sq_nonneg _)) (sq_nonneg _)

lemma energy_le_one (P : finpartition s) : P.energy G ≤ 1 :=
begin
  refine div_le_of_nonneg_of_le_mul (sq_nonneg _) zero_le_one _,
  suffices h : ∑ UV in P.parts.off_diag, G.edge_density UV.1 UV.2^2 ≤ P.parts.off_diag.card,
  { apply h.trans,
    rw [off_diag_card, one_mul, ←nat.cast_pow, nat.cast_le, sq],
    apply tsub_le_self },
  rw ←nat.smul_one_eq_coe,
  refine sum_le_card_nsmul _ _ 1 (λ UV _, _),
  rw sq_le_one_iff (G.edge_density_nonneg _ _),
  exact G.edge_density_le_one _ _,
end

end finpartition
