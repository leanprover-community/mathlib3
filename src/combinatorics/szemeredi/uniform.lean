/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib

/-!
# Graph and partition uniformity

In this file we define
-/

open_locale big_operators
open finset fintype function relation

variables {α 𝕜 : Type*} [linear_ordered_field 𝕜]

/-! ###  Uniform graphs -/

namespace simple_graph
variables (G : simple_graph α) [decidable_rel G.adj] (ε : 𝕜) {s t : finset α} {a b : α}

/-- A pair of finsets of vertices is `ε`-uniform iff their edge density is close to the density of
any big enough pair of subsets. Intuitively, the edges between them are random-like. -/
def is_uniform (s t : finset α) : Prop :=
∀ ⦃s'⦄, s' ⊆ s → ∀ ⦃t'⦄, t' ⊆ t → (s.card : 𝕜) * ε ≤ s'.card → (t.card : 𝕜) * ε ≤ t'.card →
  |(edge_density G s' t' : 𝕜) - (edge_density G s t : 𝕜)| < ε

variables {G ε}

/-- If the pair `(s, t)` is `ε`-uniform and `ε ≤ ε'`, then it is `ε'`-uniform. -/
lemma is_uniform.mono {ε' : 𝕜} (hε : is_uniform G ε s t) (h : ε ≤ ε') : is_uniform G ε' s t :=
λ s' hs' t' ht' hs ht, by refine (hε hs' ht' (le_trans _ hs) (le_trans _ ht)).trans_le h;
  exact mul_le_mul_of_nonneg_left h (nat.cast_nonneg _)

lemma is_uniform.symm : symmetric (is_uniform G ε) :=
λ s t h t' ht' s' hs' ht hs,
  by { rw [edge_density_comm _ t', edge_density_comm _ t], exact h hs' ht' hs ht }

variables (G)

lemma is_uniform_comm : is_uniform G ε s t ↔ is_uniform G ε t s := ⟨λ h, h.symm, λ h, h.symm⟩

lemma is_uniform_singleton (hε : 0 < ε) : G.is_uniform ε {a} {b} :=
begin
  intros s' hs' t' ht' hs ht,
  rw [card_singleton, nat.cast_one, one_mul] at hs ht,
  obtain rfl | rfl := finset.subset_singleton_iff.1 hs',
  { exact (hε.not_le hs).elim },
  obtain rfl | rfl := finset.subset_singleton_iff.1 ht',
  { exact (hε.not_le ht).elim },
  { rwa [sub_self, abs_zero] }
end

lemma not_is_uniform_zero : ¬ G.is_uniform (0 : 𝕜) s t :=
λ h, (abs_nonneg _).not_lt $ h (empty_subset _) (empty_subset _) (by simp) (by simp)

lemma is_uniform_of_one_le (hε : 1 ≤ ε) : G.is_uniform ε s t :=
begin
  intros s' hs' t' ht' hs ht,
  have h : ∀ n : ℕ, (n : 𝕜) ≤ n * ε := λ n, le_mul_of_one_le_right n.cast_nonneg hε,
  rw [eq_of_subset_of_card_le hs' (nat.cast_le.1 ((h _).trans hs)),
    eq_of_subset_of_card_le ht' (nat.cast_le.1 ((h _).trans ht)), sub_self, abs_zero],
  exact zero_lt_one.trans_le hε,
end

end simple_graph

/-! ## Uniform partitions -/

variables [decidable_eq α] {s : finset α} (P : finpartition s)
variables (G : simple_graph α) [decidable_rel G.adj]

namespace finpartition
open_locale classical

/-- -/
noncomputable def non_uniform_pairs (ε : 𝕜) : finset (finset α × finset α) :=
P.parts.off_diag.filter (λ UV, ¬G.is_uniform ε UV.1 UV.2)

lemma mem_non_uniform_pairs (U V : finset α) (ε : 𝕜) :
  (U, V) ∈ P.non_uniform_pairs G ε ↔ U ∈ P.parts ∧ V ∈ P.parts ∧ U ≠ V ∧ ¬G.is_uniform ε U V :=
by rw [non_uniform_pairs, mem_filter, mem_off_diag, and_assoc, and_assoc]

/-- An finpartition is `ε-uniform` iff at most a proportion of `ε` of its pairs of parts are not
`ε-uniform`. -/
def is_uniform (ε : 𝕜) : Prop :=
((P.non_uniform_pairs G ε).card : 𝕜) ≤ (P.parts.card * (P.parts.card - 1) : ℕ) * ε

lemma empty_is_uniform {P : finpartition s} {G : simple_graph α} {ε : 𝕜} (hP : P.parts = ∅) :
  P.is_uniform G ε :=
by simp [is_uniform, hP, non_uniform_pairs]

lemma nonempty_of_not_uniform {P : finpartition s} {G : simple_graph α} {ε : 𝕜}
  (h : ¬ P.is_uniform G ε) : P.parts.nonempty :=
nonempty_of_ne_empty (λ h₁, h (empty_is_uniform h₁))

lemma is_uniform_of_one_le {ε : 𝕜} (hε : 1 ≤ ε) : P.is_uniform G ε :=
begin
  apply le_trans _ (mul_le_mul_of_nonneg_left hε (nat.cast_nonneg _)),
  rw [mul_one, nat.cast_le],
  apply le_trans (card_filter_le _ _),
  rw [off_diag_card, nat.mul_sub_left_distrib, mul_one],
end

lemma non_uniform_pairs_bot {ε : 𝕜} (hε : 0 < ε) : (⊥ : finpartition s).non_uniform_pairs G ε = ∅ :=
begin
  rw eq_empty_iff_forall_not_mem,
  rintro ⟨U, V⟩,
  simp only [finpartition.mem_non_uniform_pairs, finpartition.parts_bot, mem_map,
    not_and, not_not, embedding.coe_fn_mk, exists_imp_distrib],
  rintro x hx rfl y hy rfl h,
  exact G.is_uniform_singleton hε,
end

lemma bot_is_uniform {ε : 𝕜} (hε : 0 < ε) : (⊥ : finpartition s).is_uniform G ε :=
begin
  rw [finpartition.is_uniform, finpartition.card_bot, non_uniform_pairs_bot _ hε,
    finset.card_empty, nat.cast_zero],
  exact mul_nonneg (nat.cast_nonneg _) hε.le,
end

end finpartition
