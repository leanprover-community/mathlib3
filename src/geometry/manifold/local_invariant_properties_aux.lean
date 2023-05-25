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

namespace structure_groupoid.local_invariant_prop

-- this should be a lot shorter!!! clean up with `mfld_set_tac` and/or better simp-lemmas
lemma foo₂ {U V : opens M} {hUV : U ≤ V} (f : V → H') {x : U} :
  let i := set.inclusion hUV in
  (chart_at H (i x)).symm =ᶠ[𝓝 (chart_at H (i x) (i x))] i ∘ (chart_at H x).symm :=
begin
  intro i,
  set e := chart_at H (x:M),
  haveI : nonempty U := ⟨x⟩,
  haveI : nonempty V := ⟨i x⟩,
  have heUx_nhds : (e.subtype_restr U).symm.source ∈ 𝓝 (chart_at H x x),
  { apply (e.subtype_restr U).symm.open_source.mem_nhds,
    show e x ∈ (e.subtype_restr U).symm.source,
    rw [local_homeomorph.subtype_restr_def, local_homeomorph.symm_source],
    have hxe : (x : M) ∈ e.source := mem_chart_source _ _,
    refine ⟨e.map_source hxe, _⟩,
    rw [U.local_homeomorph_subtype_coe_target, mem_preimage, e.left_inv_on hxe],
    exact x.prop },
  apply filter.eventually_eq_of_mem heUx_nhds,
  intros y hy,
  show (e.subtype_restr V).symm y = i ((e.subtype_restr U).symm y),
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

lemma foo (hG : local_invariant_prop G G' P) {U V : opens M} (hUV : U ≤ V) (f : V → M') (x : U) :
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

lemma bar' {Q : (H → H) → (set H) → H → Prop} (hG : local_invariant_prop G G Q)
  (hQ : ∀ y, Q id univ y) {U V : opens M} (h : U ≤ V) :
  lift_prop Q (set.inclusion h : U → V) :=
begin
  intro x,
  refine (foo hG h id x).mp _,
  apply hG.lift_prop_id hQ,
end

end structure_groupoid.local_invariant_prop
