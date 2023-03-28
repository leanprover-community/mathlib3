/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.density
import set_theory.ordinal.basic

/-!
# Graph uniformity and uniform partitions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
* `simple_graph.nonuniform_witness`: `G.nonuniform_witness ε s t` and `G.nonuniform_witness ε t s`
  together witness the non-uniformity of `s` and `t`.
* `finpartition.non_uniforms`: Non uniform pairs of parts of a partition.
* `finpartition.is_uniform`: Uniformity of a partition.
* `finpartition.nonuniform_witnesses`: For each non-uniform pair of parts of a partition, pick
  witnesses of non-uniformity and dump them all together.
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
  { replace hs : ε ≤ 0 := by simpa using hs,
    exact (hε.not_le hs).elim },
  obtain rfl | rfl := finset.subset_singleton_iff.1 ht',
  { replace ht : ε ≤ 0 := by simpa using ht,
    exact (hε.not_le ht).elim },
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

variables {G}

lemma not_is_uniform_iff :
  ¬ G.is_uniform ε s t ↔ ∃ s', s' ⊆ s ∧ ∃ t', t' ⊆ t ∧ ↑s.card * ε ≤ s'.card ∧
    ↑t.card * ε ≤ t'.card ∧  ε ≤ |G.edge_density s' t' - G.edge_density s t| :=
by { unfold is_uniform, simp only [not_forall, not_lt, exists_prop] }

open_locale classical
variables (G)

/-- An arbitrary pair of subsets witnessing the non-uniformity of `(s, t)`. If `(s, t)` is uniform,
returns `(s, t)`. Witnesses for `(s, t)` and `(t, s)` don't necessarily match. See
`simple_graph.nonuniform_witness`. -/
noncomputable def nonuniform_witnesses (ε : 𝕜) (s t : finset α) : finset α × finset α :=
if h : ¬ G.is_uniform ε s t
  then ((not_is_uniform_iff.1 h).some, (not_is_uniform_iff.1 h).some_spec.2.some)
  else (s, t)

lemma left_nonuniform_witnesses_subset (h : ¬ G.is_uniform ε s t) :
  (G.nonuniform_witnesses ε s t).1 ⊆ s :=
by { rw [nonuniform_witnesses, dif_pos h], exact (not_is_uniform_iff.1 h).some_spec.1 }

lemma left_nonuniform_witnesses_card (h : ¬ G.is_uniform ε s t) :
  (s.card : 𝕜) * ε ≤ (G.nonuniform_witnesses ε s t).1.card :=
by { rw [nonuniform_witnesses, dif_pos h],
  exact (not_is_uniform_iff.1 h).some_spec.2.some_spec.2.1 }

lemma right_nonuniform_witnesses_subset (h : ¬ G.is_uniform ε s t) :
  (G.nonuniform_witnesses ε s t).2 ⊆ t :=
by { rw [nonuniform_witnesses, dif_pos h], exact (not_is_uniform_iff.1 h).some_spec.2.some_spec.1 }

lemma right_nonuniform_witnesses_card (h : ¬ G.is_uniform ε s t) :
  (t.card : 𝕜) * ε ≤ (G.nonuniform_witnesses ε s t).2.card :=
by { rw [nonuniform_witnesses, dif_pos h],
  exact (not_is_uniform_iff.1 h).some_spec.2.some_spec.2.2.1 }

lemma nonuniform_witnesses_spec (h : ¬ G.is_uniform ε s t) :
  ε ≤ |G.edge_density (G.nonuniform_witnesses ε s t).1 (G.nonuniform_witnesses ε s t).2
    - G.edge_density s t| :=
by { rw [nonuniform_witnesses, dif_pos h],
  exact (not_is_uniform_iff.1 h).some_spec.2.some_spec.2.2.2 }

/-- Arbitrary witness of non-uniformity. `G.nonuniform_witness ε s t` and
`G.nonuniform_witness ε t s` form a pair of subsets witnessing the non-uniformity of `(s, t)`. If
`(s, t)` is uniform, returns `s`. -/
noncomputable def nonuniform_witness (ε : 𝕜) (s t : finset α) : finset α :=
if well_ordering_rel s t then (G.nonuniform_witnesses ε s t).1 else (G.nonuniform_witnesses ε t s).2

lemma nonuniform_witness_subset (h : ¬ G.is_uniform ε s t) : G.nonuniform_witness ε s t ⊆ s :=
begin
  unfold nonuniform_witness,
  split_ifs,
  { exact G.left_nonuniform_witnesses_subset h },
  { exact G.right_nonuniform_witnesses_subset (λ i, h i.symm) }
end

lemma nonuniform_witness_card_le (h : ¬ G.is_uniform ε s t) :
  (s.card : 𝕜) * ε ≤ (G.nonuniform_witness ε s t).card :=
begin
  unfold nonuniform_witness,
  split_ifs,
  { exact G.left_nonuniform_witnesses_card h },
  { exact G.right_nonuniform_witnesses_card (λ i, h i.symm) }
end

lemma nonuniform_witness_spec (h₁ : s ≠ t) (h₂ : ¬ G.is_uniform ε s t) :
  ε ≤ |G.edge_density (G.nonuniform_witness ε s t) (G.nonuniform_witness ε t s)
    - G.edge_density s t| :=
begin
  unfold nonuniform_witness,
  rcases trichotomous_of well_ordering_rel s t with lt | rfl | gt,
  { rw [if_pos lt, if_neg (asymm lt)],
    exact G.nonuniform_witnesses_spec h₂ },
  { cases h₁ rfl },
  { rw [if_neg (asymm gt), if_pos gt, edge_density_comm, edge_density_comm _ s],
    apply G.nonuniform_witnesses_spec (λ i, h₂ i.symm) }
end

end simple_graph

/-! ### Uniform partitions -/

variables [decidable_eq α] {A : finset α} (P : finpartition A) (G : simple_graph α)
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

lemma non_uniforms_mono {ε ε' : 𝕜} (h : ε ≤ ε') : P.non_uniforms G ε' ⊆ P.non_uniforms G ε :=
monotone_filter_right _ $ λ uv, mt $ simple_graph.is_uniform.mono h

lemma non_uniforms_bot (hε : 0 < ε) : (⊥ : finpartition A).non_uniforms G ε = ∅ :=
begin
  rw eq_empty_iff_forall_not_mem,
  rintro ⟨u, v⟩,
  simp only [finpartition.mk_mem_non_uniforms_iff, finpartition.parts_bot, mem_map, not_and,
    not_not, exists_imp_distrib],
  rintro x hx rfl y hy rfl h,
  exact G.is_uniform_singleton hε,
end

/-- A finpartition of a graph's vertex set is `ε`-uniform (aka `ε`-regular) iff the proportion of
its pairs of parts that are not `ε`-uniform is at most `ε`. -/
def is_uniform (ε : 𝕜) : Prop :=
((P.non_uniforms G ε).card : 𝕜) ≤ (P.parts.card * (P.parts.card - 1) : ℕ) * ε

lemma bot_is_uniform (hε : 0 < ε) : (⊥ : finpartition A).is_uniform G ε :=
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

lemma is_uniform.mono {ε ε' : 𝕜} (hP : P.is_uniform G ε) (h : ε ≤ ε') : P.is_uniform G ε' :=
((nat.cast_le.2 $ card_le_of_subset $ P.non_uniforms_mono G h).trans hP).trans $
  mul_le_mul_of_nonneg_left h $ nat.cast_nonneg _

lemma is_uniform_of_empty (hP : P.parts = ∅) : P.is_uniform G ε :=
by simp [is_uniform, hP, non_uniforms]

lemma nonempty_of_not_uniform (h : ¬ P.is_uniform G ε) : P.parts.nonempty :=
nonempty_of_ne_empty $ λ h₁, h $ is_uniform_of_empty h₁

variables (P G ε) (s : finset α)

/-- A choice of witnesses of non-uniformity among the parts of a finpartition. -/
noncomputable def nonuniform_witnesses : finset (finset α) :=
(P.parts.filter $ λ t, s ≠ t ∧ ¬ G.is_uniform ε s t).image (G.nonuniform_witness ε s)

variables {P G ε s} {t : finset α}

lemma nonuniform_witness_mem_nonuniform_witnesses (h : ¬ G.is_uniform ε s t) (ht : t ∈ P.parts)
  (hst : s ≠ t) :
  G.nonuniform_witness ε s t ∈ P.nonuniform_witnesses G ε s :=
mem_image_of_mem _ $ mem_filter.2 ⟨ht, hst, h⟩

end finpartition
