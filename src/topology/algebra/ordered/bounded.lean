/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.algebra.ordered.basic

/-!
# Convergent sequence is bounded above and below

In this file we prove that a convergent sequence is bounded above and below. We prove it for any
function that converges along `filter.cofinite`, then specialize to sequences.
-/

open_locale topological_space
open set filter

variables {α ι : Type*} [linear_order α] [topological_space α] [order_closed_topology α]
  {f : ι → α} {l : filter ι} {a : α}

lemma filter.tendsto.exists_ge_eventually_le (h : tendsto f l (𝓝 a)) :
  ∃ b ≥ a, ∀ᶠ x in l, f x ≤ b :=
(exists_ge_Iic_mem_nhds a).imp $ λ b hb, ⟨hb.fst, h hb.snd⟩

lemma filter.tendsto.exists_le_eventually_ge (h : tendsto f l (𝓝 a)) :
  ∃ b ≤ a, ∀ᶠ x in l, b ≤ f x :=
(exists_le_Ici_mem_nhds a).imp $ λ b hb, ⟨hb.fst, h hb.snd⟩

lemma bdd_above_range_of_tendsto_cofinite (h : tendsto f cofinite (𝓝 a)) :
  bdd_above (range f) :=
begin
  haveI : nonempty α := ⟨a⟩,
  rcases h.exists_ge_eventually_le with ⟨b, hab, hfb⟩,
  rw [← image_univ, ← union_compl_self {i | f i ≤ b}, image_union, bdd_above_union],
  exact ⟨⟨b, ball_image_iff.2 $ λ i, id⟩, (hfb.image f).bdd_above⟩,
end

lemma bdd_below_range_of_tendsto_cofinite (h : tendsto f cofinite (𝓝 a)) :
  bdd_below (range f) :=
@bdd_above_range_of_tendsto_cofinite (order_dual α) _ _ _ _ _ _ h

lemma filter.tendsto.bdd_above_range {f : ℕ → α} (hf : tendsto f at_top (𝓝 a)) :
  bdd_above (range f) :=
bdd_above_range_of_tendsto_cofinite $ by rwa nat.cofinite_eq_at_top

lemma filter.tendsto.bdd_below_range {f : ℕ → α} (hf : tendsto f at_top (𝓝 a)) :
  bdd_below (range f) :=
bdd_below_range_of_tendsto_cofinite $ by rwa nat.cofinite_eq_at_top
