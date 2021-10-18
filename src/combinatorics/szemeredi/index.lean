/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib
import combinatorics.choose.bounds
import data.sym.card

/-!
# Index
-/

open_locale big_operators
open finset fintype function relation

variables {α : Type*}

namespace finset
variable [decidable_eq α]

@[simp] lemma off_diag_empty : (∅ : finset α).off_diag = ∅ :=
by rw [off_diag, empty_product, filter_empty]

end finset

/-! ## finpartition.is_uniform -/

variables [decidable_eq α] {s : finset α} (P : finpartition s) (G : simple_graph α)

namespace finpartition
open_locale classical
open finset

noncomputable def non_uniform_pairs (ε : ℝ) :
  finset (finset α × finset α) :=
P.parts.off_diag.filter (λ UV, ¬G.is_uniform ε UV.1 UV.2)

lemma mem_non_uniform_pairs (U V : finset α) (ε : ℝ) :
  (U, V) ∈ P.non_uniform_pairs G ε ↔ U ∈ P.parts ∧ V ∈ P.parts ∧ U ≠ V ∧ ¬G.is_uniform ε U V :=
by rw [non_uniform_pairs, mem_filter, mem_off_diag, and_assoc, and_assoc]

/-- An finpartition is `ε-uniform` iff at most a proportion of `ε` of its pairs of parts are not
`ε-uniform`. -/
def is_uniform (ε : ℝ) : Prop :=
((P.non_uniform_pairs G ε).card : ℝ) ≤ (P.size * (P.size - 1) : ℕ) * ε

lemma empty_is_uniform {P : finpartition s} {G : simple_graph α} {ε : ℝ} (hP : P.parts = ∅) :
  P.is_uniform G ε :=
begin
  rw [finpartition.is_uniform, finpartition.non_uniform_pairs, finpartition.size, hP],
  simp,
end

lemma nonempty_of_not_uniform {P : finpartition s} {G : simple_graph α} {ε : ℝ}
  (h : ¬ P.is_uniform G ε) : P.parts.nonempty :=
begin
  rw nonempty_iff_ne_empty,
  intro h₁,
  apply h (empty_is_uniform h₁),
end

/-- The index is the auxiliary quantity that drives the induction process in the proof of
Szemerédi's Regularity Lemma (see `increment`). As long as we do not have a suitable equipartition,
we will find a new one that has an index greater than the previous one plus some fixed constant.
Then `index_le_one` ensures this process only happens finitely many times. -/
noncomputable def index (P : finpartition s) : ℝ :=
(∑ UV in P.parts.off_diag, G.edge_density UV.1 UV.2^2)/P.size^2

lemma index_nonneg (P : finpartition s) :
  0 ≤ P.index G :=
div_nonneg (finset.sum_nonneg (λ _ _, sq_nonneg _)) (sq_nonneg _)

lemma index_le_one (P : finpartition s) :
  P.index G ≤ 1 :=
begin
  rw finpartition.index,
  refine div_le_of_nonneg_of_le_mul (sq_nonneg _) zero_le_one _,
  suffices h : (∑ UV in P.parts.off_diag, G.edge_density UV.1 UV.2^2) ≤ P.parts.off_diag.card,
  { apply h.trans,
    rw [off_diag_card, one_mul, size_eq_card_parts, ←nat.cast_pow, nat.cast_le, sq],
    apply sub_le_self' },
  refine (sum_le_of_forall_le _ _ 1 _).trans _,
  { rintro UV _,
    rw sq_le_one_iff (G.edge_density_nonneg _ _),
    apply G.edge_density_le_one },
  rw nat.smul_one_eq_coe,
end

end finpartition

namespace discrete_finpartition

lemma non_uniform_pairs {ε : ℝ} (hε : 0 < ε) :
  (discrete_finpartition s).non_uniform_pairs G ε = ∅ :=
begin
  rw eq_empty_iff_forall_not_mem,
  rintro ⟨U, V⟩,
  simp only [finpartition.mem_non_uniform_pairs, discrete_finpartition_parts, mem_map,
    not_and, not_not, embedding.coe_fn_mk, exists_imp_distrib],
  rintro x hx rfl y hy rfl h U' hU' V' hV' hU hV,
  rw [card_singleton, nat.cast_one, one_mul] at hU hV,
  obtain rfl | rfl := finset.subset_singleton_iff.1 hU',
  { rw [finset.card_empty] at hU,
    exact (hε.not_le hU).elim },
  obtain rfl | rfl := finset.subset_singleton_iff.1 hV',
  { rw [finset.card_empty] at hV,
    exact (hε.not_le hV).elim },
  rwa [sub_self, abs_zero],
end

lemma is_uniform {ε : ℝ} (hε : 0 < ε) :
  (discrete_finpartition s).is_uniform G ε :=
begin
  rw [finpartition.is_uniform, discrete_finpartition.size, non_uniform_pairs _ hε,
    finset.card_empty, nat.cast_zero],
  apply mul_nonneg (nat.cast_nonneg _) hε.le ,
end

end discrete_finpartition
