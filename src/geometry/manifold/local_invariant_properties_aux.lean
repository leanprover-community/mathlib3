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
  {G : structure_groupoid H} [closed_under_restriction G] {G' : structure_groupoid H'}
  (M : Type*) [topological_space M] [charted_space H M] [has_groupoid M G]
  (M' : Type*) [topological_space M'] [charted_space H' M'] [has_groupoid M' G']
  {P : (H → H') → (set H) → H → Prop}

namespace structure_groupoid.local_invariant_prop
variables {M M'}

lemma foo₁ (hG : local_invariant_prop G G' P) {U V : opens M} {hUV : U ≤ V} {f : V → M'} {x : U} :
  continuous_within_at f univ (set.inclusion hUV x)
  ↔ continuous_within_at (f ∘ set.inclusion hUV) univ x :=
begin
  simp only [continuous_within_at_univ],
  split,
  { intro h,
    exact h.comp (continuous_inclusion hUV).continuous_at },
  { intro h,
    simpa [(topological_space.opens.open_embedding_of_le hUV).continuous_at_iff] using h }
end

-- this should be a lot shorter!!! clean up with `mfld_set_tac` and/or better simp-lemmas
lemma foo₂ (hG : local_invariant_prop G G' P) {U V : opens M} {hUV : U ≤ V} {f : V → M'}
  (e : M' → H') {x : U} :
  P (e ∘ f ∘ (chart_at H (set.inclusion hUV x : V)).symm) univ
    (chart_at H (set.inclusion hUV x : V) (set.inclusion hUV x))
  ↔ P (e ∘ (f ∘ set.inclusion hUV) ∘ ((chart_at H x).symm)) univ (chart_at H x x) :=
begin
  set i := set.inclusion hUV,
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
    have hxe'' : e'.symm (e' x) = _ := e'.left_inv_on hxe',
    rw [hxe''],
    exact x.prop },
  { show ∀ y ∈ (e'.subtype_restr U).symm.source,
      e (f ((e'.subtype_restr V).symm y)) = e (f (i ((e'.subtype_restr U).symm y))),
    intros y hy,
    have hy' : e'.symm y ∈ U,
    { rw [local_homeomorph.subtype_restr_def, local_homeomorph.symm_source] at hy,
      simp at hy,
      exact hy.2 },
    have he'y : e'.symm y ∈ V.local_homeomorph_subtype_coe.target,
    { rw V.local_homeomorph_subtype_coe_target,
      exact hUV hy', },
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

lemma foo (hG : local_invariant_prop G G' P) {U V : opens M} (hUV : U ≤ V) (f : V → M')
  (x : U) :
  lift_prop_at P f (set.inclusion hUV x) ↔ lift_prop_at P (f ∘ set.inclusion hUV : U → M') x :=
⟨λh, ⟨(foo₁ hG).1 h.1, (foo₂ hG _).1 h.2⟩, λh, ⟨(foo₁ hG).2 h.1, (foo₂ hG _).2 h.2⟩⟩

lemma bar' {Q : (H → H) → (set H) → H → Prop} (hG : local_invariant_prop G G Q)
  (hQ : ∀ y, Q id univ y) {U V : opens M} (h : U ≤ V) :
  lift_prop Q (set.inclusion h : U → V) :=
begin
  intro x,
  refine (foo hG h id x).mp _,
  apply hG.lift_prop_id hQ,
end

end structure_groupoid.local_invariant_prop
