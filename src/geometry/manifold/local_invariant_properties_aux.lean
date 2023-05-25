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
  {G : structure_groupoid H} [_iG : closed_under_restriction G] {G' : structure_groupoid H'}
  {M : Type*} [topological_space M] [charted_space H M] [_iMG: has_groupoid M G]
  {M' : Type*} [topological_space M'] [charted_space H' M']
  {P : (H → H') → (set H) → H → Prop}

lemma baz (e : local_homeomorph M H) {U : opens M} [nonempty U] (x : U) (hxe : (x:M) ∈ e.source) :
  e x ∈ (e.subtype_restr U).target :=
begin
  refine ⟨e.map_source hxe, _⟩,
  rw [U.local_homeomorph_subtype_coe_target, mem_preimage, e.left_inv_on hxe],
  exact x.prop
end

lemma bop {U V : opens M} [nonempty U] [nonempty V] (hUV : U ≤ V)
  (e : local_homeomorph M H) :
  eq_on (e.subtype_restr V).symm (set.inclusion hUV ∘ (e.subtype_restr U).symm)
    (e.subtype_restr U).target :=
begin
  set i := set.inclusion hUV,
  intros y hy,
  dsimp [local_homeomorph.subtype_restr_def] at ⊢ hy,
  have hyV : e.symm y ∈ V.local_homeomorph_subtype_coe.target,
  { rw opens.local_homeomorph_subtype_coe_target at ⊢ hy,
    exact hUV hy.2 },
  refine V.local_homeomorph_subtype_coe.inj_on _ trivial _,
  { rw ←local_homeomorph.symm_target,
    apply local_homeomorph.map_source,
    rw local_homeomorph.symm_source,
    exact hyV },
  { rw V.local_homeomorph_subtype_coe.right_inv hyV,
    show _ = U.local_homeomorph_subtype_coe _,
    rw U.local_homeomorph_subtype_coe.right_inv hy.2 }
end

namespace structure_groupoid.local_invariant_prop

lemma foo₂ {U V : opens M} {hUV : U ≤ V} (f : V → H') {x : U} :
  let i := set.inclusion hUV in
  (chart_at H (i x)).symm =ᶠ[𝓝 (chart_at H (i x) (i x))] i ∘ (chart_at H x).symm :=
begin
  intro i,
  set e := chart_at H (x:M),
  haveI : nonempty U := ⟨x⟩,
  haveI : nonempty V := ⟨i x⟩,
  have heUx_nhds : (e.subtype_restr U).target ∈ 𝓝 (e x),
  { apply (e.subtype_restr U).open_target.mem_nhds,
    exact baz e x (mem_chart_source _ _) },
  exact filter.eventually_eq_of_mem heUx_nhds (bop hUV e),
end

lemma lift_prop_at_iff_comp_inclusion (hG : local_invariant_prop G G' P) {U V : opens M}
  (hUV : U ≤ V) (f : V → M') (x : U) :
  lift_prop_at P f (set.inclusion hUV x) ↔ lift_prop_at P (f ∘ set.inclusion hUV : U → M') x :=
begin
  congrm _ ∧ _,
  { simp [continuous_within_at_univ,
      (topological_space.opens.open_embedding_of_le hUV).continuous_at_iff] },
  { apply hG.congr_iff,
    convert filter.eventually_eq.fun_comp _ (chart_at H' (f (set.inclusion hUV x)) ∘ f) using 1,
    dsimp,
    apply foo₂ (chart_at H' (f (set.inclusion hUV x)) ∘ f), },
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
