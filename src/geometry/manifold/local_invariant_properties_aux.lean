/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.local_invariant_properties
import topology.category.Top.opens

/-! # Further facts about of `local_invariant_prop` -/

open_locale manifold topological_space
open set topological_space structure_groupoid structure_groupoid.local_invariant_prop opposite

variables {H : Type*} [topological_space H]
  {H' : Type*} [topological_space H']
  {G : structure_groupoid H} [closed_under_restriction G] {G' : structure_groupoid H'}
  (M : Type*) [topological_space M] [charted_space H M] [has_groupoid M G]
  (M' : Type*) [topological_space M'] [charted_space H' M'] [has_groupoid M' G']
  {P : (H → H') → (set H) → H → Prop}

instance Top.of.charted_space : charted_space H (Top.of M) := (infer_instance : charted_space H M)

instance Top.of.has_groupoid : has_groupoid (Top.of M) G := (infer_instance : has_groupoid M G)

namespace structure_groupoid.local_invariant_prop
variables {M M'}

-- lemma mdifferentiable_inclusion {U V : opens M} (h : U ≤ V) :
--   mdifferentiable I I (set.inclusion h : U → V) :=
-- lemma bar {Q : (H → H) → (set H) → H → Prop} (hG : local_invariant_prop G G Q)
--   {U V : opens (Top.of M)} (i : U ⟶ V) :
--   lift_prop Q i :=
-- begin
--   -- refine ⟨λ h, ⟨_, _⟩, λ h, ⟨_, _⟩⟩,
--   sorry,
-- end

-- lemma bar (hG : local_invariant_prop G G' P) {U : opens (Top.of M)} {f : M → M'} {x : U} :
--   lift_prop_at P (f ∘ (coe : U → Top.of M)) x ↔ lift_prop_at P f x.val :=


lemma foo₁ (hG : local_invariant_prop G G' P) {U V : opens (Top.of M)} {i : U ⟶ V} {f : V → M'}
  {x : U} :
  continuous_within_at f univ (i x) ↔ continuous_within_at (f ∘ i) univ x :=
begin
  simp only [continuous_within_at_univ],
  have hUV : U ≤ V := category_theory.le_of_hom i,
  split,
  { intro h,
    exact h.comp (continuous_inclusion hUV).continuous_at },
  { intro h,
    have hi : open_embedding i := topological_space.opens.open_embedding_of_le hUV,
    simpa [hi.continuous_at_iff] using h }
end

-- this should be a lot shorter!!! clean up with `mfld_set_tac` and/or better simp-lemmas
lemma foo₂ (hG : local_invariant_prop G G' P) {U V : opens (Top.of M)} {i : U ⟶ V} {f : V → M'}
  (e : M' →H') {x : U} :
  P (e ∘ f ∘ (chart_at H (i x)).symm) univ (chart_at H (i x) (i x))
  ↔ P (e ∘ (f ∘ i) ∘ ((chart_at H x).symm)) univ (chart_at H x x) :=
begin
  haveI : nonempty U := ⟨x⟩,
  haveI : nonempty V := ⟨i x⟩,
  set e' := chart_at H x.val,
  apply hG.congr_iff,
  apply filter.eventually_eq_of_mem,
  apply (e'.subtype_restr U).symm.open_source.mem_nhds,
  { show e' x ∈ (e'.subtype_restr U).symm.source,
    rw [local_homeomorph.subtype_restr_def, local_homeomorph.symm_source],
    dsimp,
    have hxe' : (x.1 :M) ∈ e'.source := mem_chart_source _ _,
    refine ⟨e'.map_source hxe', _⟩,
    rw [U.local_homeomorph_subtype_coe_target],
    convert x.prop,
    exact e'.left_inv_on hxe' },
  { show ∀ y ∈ (e'.subtype_restr U).symm.source,
      e (f ((e'.subtype_restr V).symm y)) = e (f (i ((e'.subtype_restr U).symm y))),
    intros y hy,
    have hy' : e'.symm y ∈ U,
    { rw [local_homeomorph.subtype_restr_def, local_homeomorph.symm_source] at hy,
      simp at hy,
      exact hy.2 },
    have he'y : e'.symm y ∈ V.local_homeomorph_subtype_coe.target,
    { rw V.local_homeomorph_subtype_coe_target,
      exact category_theory.le_of_hom i hy', },
    rw [local_homeomorph.subtype_restr_def],
    rw [local_homeomorph.subtype_restr_def],
    have ht : ∀ t, V.local_homeomorph_subtype_coe (i t) = U.local_homeomorph_subtype_coe t,
    { intro t,
      refl, },
    have hVU : V.local_homeomorph_subtype_coe ∘ i = U.local_homeomorph_subtype_coe := funext ht,
    congr' 2,
    dsimp,
    apply V.local_homeomorph_subtype_coe.inj_on,
    { rw ←local_homeomorph.symm_target,
      apply local_homeomorph.map_source,
      rw local_homeomorph.symm_source,
      exact he'y },
    { exact mem_univ _ },
    rw V.local_homeomorph_subtype_coe.right_inv,
    rw ht,
    rw U.local_homeomorph_subtype_coe.right_inv,
    { rw U.local_homeomorph_subtype_coe_target,
      exact hy' },
    { exact he'y } },
end

lemma foo (hG : local_invariant_prop G G' P) {U V : opens (Top.of M)} (i : U ⟶ V) (f : V → M')
  (x : U) :
  lift_prop_at P f (i x) ↔ lift_prop_at P (f ∘ i) x :=
⟨λh, ⟨(foo₁ hG).1 h.1, (foo₂ hG _).1 h.2⟩, λh, ⟨(foo₁ hG).2 h.1, (foo₂ hG _).2 h.2⟩⟩

lemma bar' {Q : (H → H) → (set H) → H → Prop} (hG : local_invariant_prop G G Q)
  (hQ : ∀ y, Q id univ y) {U V : opens M} (h : U ≤ V) :
  lift_prop Q (set.inclusion h : U → V) :=
begin
  intro x,
  refine (foo hG (category_theory.hom_of_le h) id x).mp _,
  apply hG.lift_prop_id hQ,
end

end structure_groupoid.local_invariant_prop
