/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import geometry.manifold.charted_space


noncomputable theory
open_locale classical manifold
universes u

variables {H : Type u} {M : Type*} [topological_space H] [topological_space M] [charted_space H M]

namespace structure_groupoid

variables (G : structure_groupoid H)

structure invariant_prop_set_pt (G : structure_groupoid H) (P : set H → H → Prop) : Prop :=
(is_local   : ∀ s x u, is_open u → x ∈ u → (P s x ↔ P (s ∩ u) x))
(invariance : ∀ s x (e : local_homeomorph H H), e ∈ G → P s x →
                P (e.target ∩ e.symm ⁻¹' (s ∩ e.source)) (e x))

structure invariant_prop_set (G : structure_groupoid H) (P : set H → Prop) : Prop :=
(is_local   : ∀ s, (∀ x ∈ s, ∃ u, is_open u ∧ x ∈ u ∧ P (s ∩ u)) → P s)
(mono       : ∀ s u, P s → is_open u → P (s ∩ u))
(invariance : ∀ s (e : local_homeomorph H H), e ∈ G → P s →
                P (e.target ∩ e.symm ⁻¹' (s ∩ e.source)))

lemma invariant_prop_set_pt.invariant_prop_set {P : set H → H → Prop}
  (h : G.invariant_prop_set_pt P) : G.invariant_prop_set (λ s, (∀ x ∈ s, P s x)) :=
begin
  split,
  { assume s hs x hx,
    rcases hs x hx with ⟨u, ⟨u_open, xu, hu⟩⟩,
    rw h.is_local s x u u_open xu,
    exact hu x ⟨hx, xu⟩ },
  { assume s u hs hu x hx,
    exact (h.is_local s x u hu hx.2).1 (hs x hx.1) },
  { assume s e eG hP x hx,
    set y := e.symm x with hy,
    have : P (e.target ∩ e.symm ⁻¹' (s ∩ e.source)) (e y) :=
      h.invariance s y e eG (hP y hx.2.1),
    rwa [hy, e.right_inv hx.1] at this }
end

end structure_groupoid


/-- If one can define a property of pointed sets in the model space, then one define a
corresponding property in the manifold, using the preferred chart at the point. -/
def charted_space.lift_prop_set_pt (P : set H → H → Prop) (s : set M) (x : M) : Prop :=
P ((chart_at H x).target ∩ (chart_at H x).symm ⁻¹' (s ∩ (chart_at H x).source)) (chart_at H x x)

/-- If one can define a property of sets in the model space, then one define a
corresponding property in the manifold, by requiring that it holds for all preferred charts. -/
def charted_space.lift_prop_set (P : set H → Prop) (s : set M) : Prop :=
∀ x, P ((chart_at H x).target ∩ (chart_at H x).symm ⁻¹' (s ∩ (chart_at H x).source))


section invariant_properties

variables {G : structure_groupoid H} [has_groupoid M G]

/- If a property of a pointed set is invariant under the structure groupoid, then expressing it in
the charted space does not depend on the element of the atlas one uses provided it contains the
point in its source. -/
lemma structure_groupoid.invariant_prop_set_pt.indep_chart
  {P : set H → H → Prop} (hG : G.invariant_prop_set_pt P) {e e' : local_homeomorph M H} (x : M)
  (he : e ∈ atlas H M) (xe : x ∈ e.source) (he' : e' ∈ atlas H M) (xe' : x ∈ e'.source)
  {s : set M} (h : P (e.target ∩ e.symm ⁻¹' (s ∩ e.source)) (e x)) :
  P (e'.target ∩ e'.symm ⁻¹' (s ∩ e'.source)) (e' x) :=
begin
  set c := e.symm ≫ₕ e' with hc,
  have cG : c ∈ G := has_groupoid.compatible G he he',
  suffices A : P ((e'.target ∩ e'.symm ⁻¹' (s ∩ e'.source)) ∩ c.target) (e' x),
  { apply (hG.is_local _ _ _ c.open_target _).2 A,
    simp [c, local_equiv.trans_target, xe, xe'] },
  set t := e.target ∩ e.symm ⁻¹' (s ∩ e.source) with ht,
  have B : (e'.target ∩ e'.symm ⁻¹' (s ∩ e'.source)) ∩ c.target =
           c.target ∩ c.symm ⁻¹' (t ∩ c.source),
  { ext y,
    simp [c, local_equiv.trans_source, local_equiv.trans_target],
    split,
    { assume hy,
      simp [hy] },
    { assume hy,
      simp [hy],
      simpa [hy] using hy } },
  have : P (c.target ∩ c.symm ⁻¹' (t ∩ c.source)) (c (e x)) :=
    hG.invariance _ _ _ cG h,
  convert this using 1,
  { exact B },
  { simp [c, xe, xe'] }
end

/- If a property of a pointed set is invariant under the structure groupoid, then it is equivalent
to express it in the charted space using the preferred chart at the point, or any atlas member
containing the point in its source. -/
lemma structure_groupoid.invariant_prop_set_pt.lift_prop_set_pt_iff
  {P : set H → H → Prop} (hG : G.invariant_prop_set_pt P) {e : local_homeomorph M H} (x : M)
  (he : e ∈ atlas H M) (xe : x ∈ e.source) (s : set M) :
  charted_space.lift_prop_set_pt P s x ↔ P (e.target ∩ e.symm ⁻¹' (s ∩ e.source)) (e x) :=
⟨hG.indep_chart x (chart_mem_atlas H x) (mem_chart_source H x) he xe,
hG.indep_chart x he xe (chart_mem_atlas H x) (mem_chart_source H x)⟩

end invariant_properties
