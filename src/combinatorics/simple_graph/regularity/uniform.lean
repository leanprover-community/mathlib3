/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.density

/-!
# Graph uniformity and uniform partitions

In this file we define uniformity of a pair of vertices in a graph and uniformity of a partition of
vertices of a graph. Both are also known as ε-regularity.

Finsets of vertices `s` and `t` are `ε`-uniform in a graph `G` if their edge density is at most
`ε`-far from the density of any big enough `s'` and `t'` where `s' ⊆ s`, `t' ⊆ t`.
The definition is pretty technical, but it amounts to the edges between `s` and `t` being "random"
The literature contains several definitions which are equivalent up to scaling `ε` by some constant
when the partition is equitable.

A partition `P` of the vertices is `ε`-uniform if the proportion of non `ε`-uniform pairs of parts
is less than `ε`.

## Main declarations

* `simple_graph.is_uniform`: Graph uniformity of a pair of finsets of vertices.
* `finpartition.non_uniforms`: Non uniform pairs of parts of a partition.
* `finpartition.is_uniform`: Uniformity of a partition.
-/

open finset

variables {α 𝕜 : Type*} [linear_ordered_field 𝕜]

/-! ###  Graph uniformity -/

namespace simple_graph
variables (G : simple_graph α) [decidable_rel G.adj] (ε : 𝕜) {s t : finset α} {a b : α}

/-- A pair of finsets of vertices is `ε`-uniform (aka `ε`-regular) iff their edge density is close
to the density of any big enough pair of subsets. Intuitively, the edges between them are
random-like. -/
def is_uniform (s t : finset α) : Prop :=
∀ ⦃s'⦄, s' ⊆ s → ∀ ⦃t'⦄, t' ⊆ t → (s.card : 𝕜) * ε ≤ s'.card → (t.card : 𝕜) * ε ≤ t'.card →
  |(G.edge_density s' t' : 𝕜) - (G.edge_density s t : 𝕜)| < ε

variables {G ε}

lemma is_uniform.mono {ε' : 𝕜} (h : ε ≤ ε') (hε : is_uniform G ε s t) : is_uniform G ε' s t :=
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

lemma is_uniform_one : G.is_uniform (1 : 𝕜) s t :=
begin
  intros s' hs' t' ht' hs ht,
  rw mul_one at hs ht,
  rw [eq_of_subset_of_card_le hs' (nat.cast_le.1 hs),
    eq_of_subset_of_card_le ht' (nat.cast_le.1 ht), sub_self, abs_zero],
  exact zero_lt_one,
end

end simple_graph

/-! ### Uniform partitions -/

variables [decidable_eq α] {s : finset α} (P : finpartition s) (G : simple_graph α)
  [decidable_rel G.adj] {ε : 𝕜}

namespace finpartition
open_locale classical

/-- The pairs of parts of a partition `P` which are not `ε`-uniform in a graph `G`. Note that we
dismiss the diagonal. We do not care whether `s` is `ε`-uniform with itself. -/
noncomputable def non_uniforms (ε : 𝕜) : finset (finset α × finset α) :=
P.parts.off_diag.filter $ λ uv, ¬G.is_uniform ε uv.1 uv.2

lemma mk_mem_non_uniforms_iff (u v : finset α) (ε : 𝕜) :
  (u, v) ∈ P.non_uniforms G ε ↔ u ∈ P.parts ∧ v ∈ P.parts ∧ u ≠ v ∧ ¬G.is_uniform ε u v :=
by rw [non_uniforms, mem_filter, mem_off_diag, and_assoc, and_assoc]

/-- A finpartition is `ε`-uniform (aka `ε`-regular) iff at most a proportion of `ε` of its pairs of
parts are not `ε-uniform`. -/
def is_uniform (ε : 𝕜) : Prop :=
((P.non_uniforms G ε).card : 𝕜) ≤ (P.parts.card * (P.parts.card - 1) : ℕ) * ε

lemma non_uniforms_bot (hε : 0 < ε) : (⊥ : finpartition s).non_uniforms G ε = ∅ :=
begin
  rw eq_empty_iff_forall_not_mem,
  rintro ⟨u, v⟩,
  simp only [finpartition.mk_mem_non_uniforms_iff, finpartition.parts_bot, mem_map, not_and,
    not_not, exists_imp_distrib],
  rintro x hx rfl y hy rfl h,
  exact G.is_uniform_singleton hε,
end

lemma bot_is_uniform (hε : 0 < ε) : (⊥ : finpartition s).is_uniform G ε :=
begin
  rw [finpartition.is_uniform, finpartition.card_bot, non_uniforms_bot _ hε,
    finset.card_empty, nat.cast_zero],
  exact mul_nonneg (nat.cast_nonneg _) hε.le,
end

lemma is_uniform_one : P.is_uniform G (1 : 𝕜) :=
begin
  rw [is_uniform, mul_one, nat.cast_le],
  refine (card_filter_le _ _).trans _,
  rw [off_diag_card, nat.mul_sub_left_distrib, mul_one],
end

variables {P G}

lemma is_uniform_of_empty (hP : P.parts = ∅) : P.is_uniform G ε :=
by simp [is_uniform, hP, non_uniforms]

lemma nonempty_of_not_uniform (h : ¬ P.is_uniform G ε) : P.parts.nonempty :=
nonempty_of_ne_empty $ λ h₁, h $ is_uniform_of_empty h₁

end finpartition
