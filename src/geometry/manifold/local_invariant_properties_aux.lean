/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.local_invariant_properties

/-! # Further facts about of `local_invariant_prop` -/

open_locale manifold topology
open set topological_space structure_groupoid structure_groupoid.local_invariant_prop

variables {H : Type*} [topological_space H]
  {H' : Type*} [topological_space H']
  {G : structure_groupoid H} {G' : structure_groupoid H'}
  {M : Type*} [topological_space M] [charted_space H M]
  {M' : Type*} [topological_space M'] [charted_space H' M']
  {P : (H → H') → (set H) → H → Prop}

namespace structure_groupoid.local_invariant_prop

lemma lift_prop_at_iff_comp_inclusion (hG : local_invariant_prop G G' P) {U V : opens M}
  (hUV : U ≤ V) (f : V → M') (x : U) :
  lift_prop_at P f (set.inclusion hUV x) ↔ lift_prop_at P (f ∘ set.inclusion hUV : U → M') x :=
begin
  congrm _ ∧ _,
  { simp [continuous_within_at_univ,
      (topological_space.opens.open_embedding_of_le hUV).continuous_at_iff] },
  { apply hG.congr_iff,
    exact (topological_space.opens.chart_at_inclusion_eventually_eq hUV).fun_comp
      (chart_at H' (f (set.inclusion hUV x)) ∘ f) },
end

lemma lift_prop_inclusion {Q : (H → H) → (set H) → H → Prop} (hG : local_invariant_prop G G Q)
  (hQ : ∀ y, Q id univ y) {U V : opens M} (hUV : U ≤ V) :
  lift_prop Q (set.inclusion hUV : U → V) :=
begin
  intro x,
  show lift_prop_at Q (id ∘ inclusion hUV) x,
  rw ← hG.lift_prop_at_iff_comp_inclusion hUV,
  apply hG.lift_prop_id hQ,
end

end structure_groupoid.local_invariant_prop
