/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.regularity.increment

/-!
# Szemerédi's Regularity Lemma

In this file, we prove Szemerédi's Regularity Lemma. This is a landmark result in combinatorics
roughly stating that any sufficiently big graph behaves like a random graph. This is useful because
random graphs are well-behaved in many aspects.

This file only contains the proof of the final result. The supporting material is spread across the
`combinatorics.simple_graph.regularity` folder.

## TODO

We currently only prove the equipartition version of SRL.

* Prove the diagonal version.
* Prove the degree version.
* Define the regularity of a partition and prove the corresponding version.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

open_locale classical
open finpartition finset fintype function szemeredi_regularity

variables {α : Type*} [fintype α] {P : finpartition (univ : finset α)} (hP : P.is_equipartition)
  (G : simple_graph α) (ε : ℝ) (l : ℕ)

/-- Effective **Szemerédi Regularity Lemma**: For any sufficiently large graph, there is an
`ε`-uniform equipartition of bounded size (where the bound does not depend on the graph). -/
theorem szemeredi_regularity {ε : ℝ} (l : ℕ) (hε : 0 < ε) (hl : l ≤ card α) :
  ∃ (P : finpartition univ),
    P.is_equipartition ∧ l ≤ P.parts.card ∧ P.parts.card ≤ bound ε l ∧ P.is_uniform G ε :=
begin
  obtain hα | hα := le_total (card α) (bound ε l),
  { refine ⟨⊥, bot_is_equipartition _, _⟩,
    rw [card_bot, card_univ],
    exact ⟨hl, hα, bot_is_uniform _ hε⟩ },
  let t := initial_bound ε l,
  have htα : t ≤ (univ : finset α).card :=
    (initial_bound_le_bound _ _).trans (by rwa finset.card_univ),
  obtain ⟨dum, hdum₁, hdum₂⟩ := exists_equipartition_card_eq (univ : finset α)
    (initial_bound_pos _ _).ne' htα,
  obtain hε₁ | hε₁ := le_total 1 ε,
  { exact ⟨dum, hdum₁, (le_initial_bound ε l).trans hdum₂.ge,
      hdum₂.le.trans (initial_bound_le_bound ε l), (dum.is_uniform_one G).mono hε₁⟩ },
  haveI : nonempty α,
  { rw ←fintype.card_pos_iff,
    exact (bound_pos _ _).trans_le hα },
  suffices h : ∀ i, ∃ P : finpartition (univ : finset α), P.is_equipartition ∧
    t ≤ P.parts.card ∧ P.parts.card ≤ (step_bound^[i]) t ∧
      (P.is_uniform G ε ∨ ε^5 / 4 * i ≤ P.energy G),
  { obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := h (⌊4 / ε^5⌋₊ + 1),
    refine ⟨P, hP₁, (le_initial_bound _ _).trans hP₂, hP₃.trans _,
      hP₄.resolve_right $ λ hPenergy, lt_irrefl (1 : ℝ) _⟩,
    { rw function.iterate_succ_apply',
      exact mul_le_mul_left' (pow_le_pow_of_le_left (by norm_num) (by norm_num) _) _ },
    calc
      1 = ε ^ 5 / 4 * (4 / ε ^ 5)
          : by { rw [mul_comm, div_mul_div_cancel 4 (pow_pos hε 5).ne'], norm_num }
      ... < ε ^ 5 / 4 * (⌊4 / ε ^ 5⌋₊ + 1)
          : (mul_lt_mul_left (div_pos (pow_pos hε 5) (by norm_num))).2 (nat.lt_floor_add_one _)
      ... ≤ (P.energy G : ℝ) : by rwa ←nat.cast_add_one
      ... ≤ 1 : by exact_mod_cast P.energy_le_one G },
  intro i,
  induction i with i ih,
  { refine ⟨dum, hdum₁, hdum₂.ge, hdum₂.le, or.inr _⟩,
    rw [nat.cast_zero, mul_zero],
    exact_mod_cast dum.energy_nonneg G },
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := ih,
  by_cases huniform : P.is_uniform G ε,
  { refine ⟨P, hP₁, hP₂, _, or.inl huniform⟩,
    rw function.iterate_succ_apply',
    exact hP₃.trans (le_step_bound _) },
  replace hP₄ := hP₄.resolve_left huniform,
  have hεl' : 100 < 4 ^ P.parts.card * ε ^ 5,
  { exact (hundred_lt_pow_initial_bound_mul hε l).trans_le
      (mul_le_mul_of_nonneg_right (pow_le_pow (by norm_num) hP₂) $ by positivity) },
  have hi : (i : ℝ) ≤ 4 / ε^5,
  { have hi : ε ^ 5 / 4 * ↑i ≤ 1 := hP₄.trans (by exact_mod_cast P.energy_le_one G),
    rw [div_mul_eq_mul_div, div_le_iff (show (0:ℝ) < 4, by norm_num)] at hi,
    norm_num at hi,
    rwa le_div_iff' (pow_pos hε _) },
  have hsize : P.parts.card ≤ (step_bound^[⌊4 / ε^5⌋₊] t) :=
    hP₃.trans (monotone_iterate_of_id_le le_step_bound (nat.le_floor hi) _),
  have hPα : P.parts.card * 16^P.parts.card ≤ card α :=
    (nat.mul_le_mul hsize (nat.pow_le_pow_of_le_right (by norm_num) hsize)).trans hα,
  refine ⟨increment hP₁ G ε, increment_is_equipartition hP₁ G ε, _, _,
    or.inr $ le_trans _ $ energy_increment hP₁ ((seven_le_initial_bound ε l).trans hP₂)
      hεl' hPα huniform hε₁⟩,
  { rw card_increment hPα huniform,
    exact hP₂.trans (le_step_bound _) },
  { rw [card_increment hPα huniform, function.iterate_succ_apply'],
    exact step_bound_mono hP₃ },
  { rw [nat.cast_succ, mul_add, mul_one],
    exact add_le_add_right hP₄ _ }
end
