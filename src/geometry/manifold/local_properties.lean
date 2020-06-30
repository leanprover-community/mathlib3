/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import geometry.manifold.smooth_manifold_with_corners
import analysis.calculus.times_cont_diff


noncomputable theory
open_locale classical manifold topological_space
universes u

open set

variables {H : Type u} {M : Type*} [topological_space H] [topological_space M] [charted_space H M]
{H' : Type*} {M' : Type*} [topological_space H'] [topological_space M'] [charted_space H' M']

namespace structure_groupoid

variables (G : structure_groupoid H) (G' : structure_groupoid H')

structure invariant_prop_set_pt (P : set H → H → Prop) : Prop :=
(is_local   : ∀ {s x u}, is_open u → x ∈ u → (P s x ↔ P (s ∩ u) x))
(invariance : ∀ {s x} {e : local_homeomorph H H}, e ∈ G → x ∈ e.source → P s x →
                P (e.target ∩ e.symm ⁻¹' s) (e x))

structure invariant_prop_fun_set_pt (P : (H → H') → (set H) → H → Prop) : Prop :=
(is_local : ∀ {s x u} {f : H → H'}, is_open u → x ∈ u → (P f s x ↔ P f (s ∩ u) x))
(right_invariance : ∀ {s x f} {e : local_homeomorph H H}, e ∈ G → x ∈ e.source → P f s x →
                      P (f ∘ e.symm) (e.target ∩ e.symm ⁻¹' s) (e x))
(congr : ∀ {s x} {f g : H → H'}, (∀ y ∈ s, f y = g y) → (f x = g x) → P f s x → P g s x)
(left_invariance : ∀ {s x f} {e' : local_homeomorph H' H'}, e' ∈ G' → s ⊆ f ⁻¹' (e'.source) →
                     f x ∈ e'.source → P f s x → P (e' ∘ f) s x)

end structure_groupoid

/-- If one can define a property of pointed sets in the model space, then one define a
corresponding property in the manifold, using the preferred chart at the point. -/
def charted_space.lift_prop_set_pt (P : set H → H → Prop) (s : set M) (x : M) : Prop :=
P ((chart_at H x).target ∩ (chart_at H x).symm ⁻¹' s) (chart_at H x x)

/-- If one can define a property of germs of functions and sets in the model space, then one define
a corresponding property in the manifold, by requiring that it holds for all preferred charts. -/
def charted_space.lift_prop_fun_set_within_at (P : (H → H') → set H → H → Prop)
  (f : M → M') (s : set M) (x : M) : Prop :=
continuous_within_at f s x ∧
P ((chart_at H' (f x)) ∘ f ∘ (chart_at H x).symm)
  ((chart_at H x).target ∩ (chart_at H x).symm ⁻¹' (s ∩ f ⁻¹' (chart_at H' (f x)).source))
  (chart_at H x x)

def charted_space.lift_prop_fun_set_on (P : (H → H') → set H → H → Prop) (f : M → M') (s : set M) :=
∀ x ∈ s, charted_space.lift_prop_fun_set_within_at P f s x

def charted_space.lift_prop_fun_set_at (P : (H → H') → set H → H → Prop) (f : M → M') (x : M) :=
charted_space.lift_prop_fun_set_within_at P f univ x

def charted_space.lift_prop_fun_set (P : (H → H') → set H → H → Prop) (f : M → M') :=
∀ x, charted_space.lift_prop_fun_set_at P f x

open charted_space

namespace structure_groupoid

variables {G : structure_groupoid H} {G' : structure_groupoid H'}
{e e' : local_homeomorph M H} {f f' : local_homeomorph M' H'}

/-- If a property of a pointed set is invariant under the structure groupoid, then expressing it in
the charted space does not depend on the element of the maximal atlas one uses provided it
contains the point in its source. -/
lemma invariant_prop_set_pt.indep_chart {P : set H → H → Prop}
  (hG : G.invariant_prop_set_pt P) (x : M)
  (he : e ∈ G.maximal_atlas M) (xe : x ∈ e.source)
  (he' : e' ∈ G.maximal_atlas M) (xe' : x ∈ e'.source)
  {s : set M} (h : P (e.target ∩ e.symm ⁻¹' s) (e x)) :
  P (e'.target ∩ e'.symm ⁻¹' s) (e' x) :=
begin
  set c := e.symm ≫ₕ e' with hc,
  have cG : c ∈ G := compatible_of_mem_maximal_atlas he he',
  suffices A : P ((e'.target ∩ e'.symm ⁻¹' s) ∩ c.target) (e' x),
  { apply (hG.is_local c.open_target _).2 A,
    simp only [c, xe, xe'] with mfld_simps },
  set t := e.target ∩ e.symm ⁻¹' s with ht,
  have B : (e'.target ∩ e'.symm ⁻¹' s) ∩ c.target =
           c.target ∩ c.symm ⁻¹' t,
  { ext y,
    simp only with mfld_simps,
    split,
    { assume hy,
      simp only [hy] with mfld_simps },
    { assume hy,
      simp only [hy] with mfld_simps,
      simpa only [hy] with mfld_simps using hy } },
  have : P (c.target ∩ c.symm ⁻¹' t) (c (e x)) :=
    hG.invariance cG (by simp only [xe, xe'] with mfld_simps) h,
  convert this using 1,
  { exact B },
  { simp only [c, xe, xe'] with mfld_simps }
end

/-- If a property of a pointed set is invariant under the structure groupoid, then it is equivalent
to express it in the charted space using the preferred chart at the point, or any maximal atlas
member containing the point in its source. -/
lemma invariant_prop_set_pt.lift_prop_set_pt_iff [has_groupoid M G]
  {P : set H → H → Prop} (hG : G.invariant_prop_set_pt P) {e : local_homeomorph M H} (x : M)
  (he : e ∈ G.maximal_atlas M) (xe : x ∈ e.source) (s : set M) :
  charted_space.lift_prop_set_pt P s x ↔ P (e.target ∩ e.symm ⁻¹' s) (e x) :=
⟨hG.indep_chart x (G.chart_mem_maximal_atlas x) (mem_chart_source H x) he xe,
hG.indep_chart x he xe (G.chart_mem_maximal_atlas x) (mem_chart_source H x)⟩

namespace invariant_prop_fun_set_pt

variables {P : (H → H') → set H → H → Prop} (hG : G.invariant_prop_fun_set_pt G' P)
{g : M → M'} {s t : set M} {x : M}

include hG

/-- If a property of a germ of function `g` on a pointed set `(s, x)` is invariant under the
structure groupoid (by composition in the source space and in the target space), then
expressing it in charted spaces does not depend on the element of the maximal atlas one uses
both in the source and in the target manifolds, provided they are defined around `x` and `g x`
respectively, and provided `g` is continuous within `s` at `x` (otherwise, the local behavior
of `g` at `x` can not be captured with a chart in the target). -/
lemma lift_within_at_indep_chart_aux
  (he : e ∈ G.maximal_atlas M) (xe : x ∈ e.source)
  (he' : e' ∈ G.maximal_atlas M) (xe' : x ∈ e'.source)
  (hf : f ∈ G'.maximal_atlas M') (xf : g x ∈ f.source)
  (hf' : f' ∈ G'.maximal_atlas M') (xf' : g x ∈ f'.source)
  (hgs : continuous_within_at g s x)
  (h : P (f ∘ g ∘ e.symm) (e.target ∩ e.symm ⁻¹' (s ∩ g⁻¹' f.source)) (e x)) :
  P (f' ∘ g ∘ e'.symm) (e'.target ∩ e'.symm ⁻¹' (s ∩ g⁻¹' f'.source)) (e' x) :=
begin
  obtain ⟨o, o_open, xo, oe, oe', of, of'⟩ :
    ∃ (o : set M), is_open o ∧ x ∈ o ∧ o ⊆ e.source ∧ o ⊆ e'.source ∧
      o ∩ s ⊆ g ⁻¹' f.source ∧ o ∩ s ⊆  g⁻¹' f'.to_local_equiv.source,
  { have : f.source ∩ f'.source ∈ 𝓝 (g x) :=
      mem_nhds_sets (is_open_inter f.open_source f'.open_source) ⟨xf, xf'⟩,
    rcases mem_nhds_within.1 (hgs.preimage_mem_nhds_within this) with ⟨u, u_open, xu, hu⟩,
    refine ⟨u ∩ e.source ∩ e'.source, _, ⟨⟨xu, xe⟩, xe'⟩, _, _, _, _⟩,
    { exact is_open_inter (is_open_inter u_open e.open_source) e'.open_source },
    { assume x hx, exact hx.1.2 },
    { assume x hx, exact hx.2 },
    { assume x hx, exact (hu ⟨hx.1.1.1, hx.2⟩).1 },
    { assume x hx, exact (hu ⟨hx.1.1.1, hx.2⟩).2 } },
  have A : P (f ∘ g ∘ e.symm)
             (e.target ∩ e.symm ⁻¹' (s ∩ g⁻¹' f.source) ∩ (e.target ∩ e.symm ⁻¹' o)) (e x),
  { apply (hG.is_local _ _).1 h,
    { exact e.continuous_on_symm.preimage_open_of_open e.open_target o_open },
    { simp only [xe, xo] with mfld_simps} },
  have B : P ((f.symm ≫ₕ f') ∘ (f ∘ g ∘ e.symm))
             (e.target ∩ e.symm ⁻¹' (s ∩ g⁻¹' f.source) ∩ (e.target ∩ e.symm ⁻¹' o)) (e x),
  { refine hG.left_invariance (compatible_of_mem_maximal_atlas hf hf') (λ y hy, _)
      (by simp only [xe, xf, xf'] with mfld_simps) A,
    simp only with mfld_simps at hy,
    have : e.symm y ∈ o ∩ s, by simp only [hy] with mfld_simps,
    simpa only [hy] with mfld_simps using of' this },
  have C : P (f' ∘ g ∘ e.symm)
             (e.target ∩ e.symm ⁻¹' (s ∩ g⁻¹' f.source) ∩ (e.target ∩ e.symm ⁻¹' o)) (e x),
  { refine hG.congr (λ y hy, _) (by simp only [xe, xf] with mfld_simps) B,
    simp only [local_homeomorph.coe_trans, function.comp_app],
    rw f.left_inv,
    apply of,
    simp only with mfld_simps at hy,
    simp only [hy] with mfld_simps },
  let w := e.symm ≫ₕ e',
  let ow := w.target ∩ w.symm ⁻¹'
    (e.target ∩ e.symm ⁻¹' (s ∩ g⁻¹' f.source) ∩ (e.target ∩ e.symm ⁻¹' o)),
  have wG : w ∈ G := compatible_of_mem_maximal_atlas he he',
  have D : P ((f' ∘ g ∘ e.symm) ∘ w.symm) ow (w (e x)) :=
    hG.right_invariance wG (by simp only [w, xe, xe'] with mfld_simps) C,
  have E : P (f' ∘ g ∘ e'.symm) ow (w (e x)),
  { refine hG.congr _ (by simp only [xe, xe'] with mfld_simps) D,
    assume y hy,
    simp only with mfld_simps,
    rw e.left_inv,
    simp only with mfld_simps at hy,
    simp only [hy] with mfld_simps },
  have : w (e x) = e' x, by simp only [w, xe] with mfld_simps,
  rw this at E,
  have : ow = (e'.target ∩ e'.symm ⁻¹' (s ∩ g⁻¹' f'.source))
               ∩ (w.target ∩ (e'.target ∩ e'.symm ⁻¹' o)),
  { ext y,
    split,
    { assume hy,
      have : e.symm (e ((e'.symm) y)) = e'.symm y,
        by { simp only with mfld_simps at hy, simp only [hy] with mfld_simps },
      simp only [this] with mfld_simps at hy,
      have : g (e'.symm y) ∈ f'.source, by { apply of', simp only [hy] with mfld_simps },
      simp only [hy, this] with mfld_simps },
    { assume hy,
      simp only with mfld_simps at hy,
      have : g (e'.symm y) ∈ f.source, by { apply of, simp only [hy] with mfld_simps },
      simp only [this, hy] with mfld_simps } },
  rw this at E,
  apply (hG.is_local _ _).2 E,
  { exact is_open_inter w.open_target
      (e'.continuous_on_symm.preimage_open_of_open e'.open_target o_open) },
  { simp only [xe', xe, xo] with mfld_simps },
end

lemma lift_within_at_indep_chart [has_groupoid M G] [has_groupoid M' G']
  (he : e ∈ G.maximal_atlas M) (xe : x ∈ e.source)
  (hf : f ∈ G'.maximal_atlas M') (xf : g x ∈ f.source) :
  lift_prop_fun_set_within_at P g s x ↔
  continuous_within_at g s x ∧ P (f ∘ g ∘ e.symm) (e.target ∩ e.symm ⁻¹' (s ∩ g⁻¹' f.source)) (e x) :=
⟨λ H, ⟨H.1,
  hG.lift_within_at_indep_chart_aux (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) he xe
  (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) hf xf H.1 H.2⟩,
λ H, ⟨H.1,
  hG.lift_within_at_indep_chart_aux he xe (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) hf xf
  (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) H.1 H.2⟩⟩

lemma lift_within_at_inter' (ht : t ∈ nhds_within x s) :
  lift_prop_fun_set_within_at P g (s ∩ t) x ↔ lift_prop_fun_set_within_at P g s x :=
begin
  by_cases hcont : ¬ (continuous_within_at g s x),
  { have : ¬ (continuous_within_at g (s ∩ t) x), by rwa [continuous_within_at_inter' ht],
    simp [lift_prop_fun_set_within_at, hcont, this] },
  push_neg at hcont,
  have A : continuous_within_at g (s ∩ t) x, by rwa [continuous_within_at_inter' ht],
  obtain ⟨o, o_open, xo, oc, oc', ost⟩ :
    ∃ (o : set M), is_open o ∧ x ∈ o ∧ o ⊆ (chart_at H x).source ∧
      o ∩ s ⊆ g ⁻¹' (chart_at H' (g x)).source ∧ o ∩ s ⊆ t,
  { rcases mem_nhds_within.1 ht with ⟨u, u_open, xu, ust⟩,
    have : (chart_at H' (g x)).source ∈ 𝓝 (g x) :=
      mem_nhds_sets ((chart_at H' (g x))).open_source (mem_chart_source H' (g x)),
    rcases mem_nhds_within.1 (hcont.preimage_mem_nhds_within this) with ⟨v, v_open, xv, hv⟩,
    refine ⟨u ∩ v ∩ (chart_at H x).source, _, ⟨⟨xu, xv⟩, mem_chart_source _ _⟩, _, _, _⟩,
    { exact is_open_inter (is_open_inter u_open v_open) (chart_at H x).open_source },
    { assume y hy, exact hy.2 },
    { assume y hy, exact hv ⟨hy.1.1.2, hy.2⟩ },
    { assume y hy, exact ust ⟨hy.1.1.1, hy.2⟩ } },
  simp only [lift_prop_fun_set_within_at, A, hcont, true_and, preimage_inter],
  have : is_open ((chart_at H x).target ∩ (chart_at H x).symm⁻¹' o),
  { apply continuous_on.preimage_open_of_open,

  },
  have Z := hG.is_local,

end

#exit

lemma mdifferentiable_within_at_inter (ht : t ∈ 𝓝 x) :
  mdifferentiable_within_at I I' f (s ∩ t) x ↔ mdifferentiable_within_at I I' f s x :=
begin
  rw [mdifferentiable_within_at, mdifferentiable_within_at, ext_chart_preimage_inter_eq,
      differentiable_within_at_inter, continuous_within_at_inter ht],
  exact ext_chart_preimage_mem_nhds I x ht
end

lemma mdifferentiable_within_at_inter' (ht : t ∈ nhds_within x s) :
  mdifferentiable_within_at I I' f (s ∩ t) x ↔ mdifferentiable_within_at I I' f s x :=
begin
  rw [mdifferentiable_within_at, mdifferentiable_within_at, ext_chart_preimage_inter_eq,
      differentiable_within_at_inter', continuous_within_at_inter' ht],
  exact ext_chart_preimage_mem_nhds_within I x ht
end

lemma mdifferentiable_at.mdifferentiable_within_at
  (h : mdifferentiable_at I I' f x) : mdifferentiable_within_at I I' f s x :=
mdifferentiable_within_at.mono (subset_univ _) (mdifferentiable_within_at_univ.2 h)

lemma mdifferentiable_within_at.mdifferentiable_at
  (h : mdifferentiable_within_at I I' f s x) (hs : s ∈ 𝓝 x) : mdifferentiable_at I I' f x :=
begin
  have : s = univ ∩ s, by rw univ_inter,
  rwa [this, mdifferentiable_within_at_inter hs, mdifferentiable_within_at_univ] at h,
end

lemma mdifferentiable_on.mono
  (h : mdifferentiable_on I I' f t) (st : s ⊆ t) : mdifferentiable_on I I' f s :=
λx hx, (h x (st hx)).mono st

end structure_groupoid


#exit

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
{E' : Type*} [normed_group E'] [normed_space 𝕜 E'] (I' : model_with_corners 𝕜 E' H')

lemma differentiable_within_at_invariant :
  (times_cont_diff_groupoid ∞ I).invariant_prop_fun_set_pt (times_cont_diff_groupoid ∞ I')
  (λ f s x, differentiable_within_at 𝕜 (I' ∘ f ∘ I.symm) (range I ∩ I.symm ⁻¹' s) (I x)) :=
{ is_local :=
  begin
    assume s x u f u_open xu,
    have : range I ∩ I.symm ⁻¹' (s ∩ u) = (range I ∩ I.symm ⁻¹' s) ∩ I.symm ⁻¹' u,
      by simp [inter_assoc],
    rw this,
    symmetry,
    apply differentiable_within_at_inter,
    have : u ∈ 𝓝 (I.symm (I x)),
      by { rw [model_with_corners.left_inv], exact mem_nhds_sets u_open xu },
    apply continuous_at.preimage_mem_nhds I.continuous_symm.continuous_at this,
  end,
  right_invariance :=
  begin
    assume s x f e he hx h,
    have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)), by simp only [hx] with mfld_simps,
    rw this at h,
    have : I (e x) ∈ (I.symm) ⁻¹' e.target ∩ range ⇑I, by simp only [hx] with mfld_simps,
    have := ((mem_groupoid_of_pregroupoid.2 he).2.times_cont_diff_within_at this).differentiable_within_at le_top,
    convert h.comp' _ this using 1,
    { ext y, simp only with mfld_simps },
    { ext y, split; { assume hy, simp only with mfld_simps at hy, simp only [hy] with mfld_simps } },
  end,
  congr :=
  begin
    assume s x f g h hx hf,
    apply hf.congr_of_eventually_eq (filter.eventually_eq_of_mem self_mem_nhds_within _),
    { simp only [hx] with mfld_simps },
    { assume y hy,
      simp only [(∘)],
      rw h,
      exact hy.2 }
  end,
  left_invariance :=
  begin
    assume s x f e' he' hs hx h,
    have A : (I' ∘ f ∘ I.symm) (I x) ∈ (I'.symm ⁻¹' e'.source ∩ range I'),
      by simp only [hx] with mfld_simps,
    have := ((mem_groupoid_of_pregroupoid.2 he').1.times_cont_diff_within_at A).differentiable_within_at le_top,
    convert this.comp _ h _,
    { ext y, simp only with mfld_simps },
    { assume y hy, simp only with mfld_simps at hy, simpa only [hy] with mfld_simps using hs hy.2 }
  end }


lemma times_cont_diff_within_at_invariant (n : ℕ) :
  (times_cont_diff_groupoid ∞ I).invariant_prop_fun_set_pt (times_cont_diff_groupoid ∞ I')
  (λ f s x, times_cont_diff_within_at 𝕜 n (I' ∘ f ∘ I.symm) (range I ∩ I.symm ⁻¹' s) (I x)) :=
{ is_local :=
  begin
    assume s x u f u_open xu,
    have : range I ∩ I.symm ⁻¹' (s ∩ u) = (range I ∩ I.symm ⁻¹' s) ∩ I.symm ⁻¹' u,
      by simp [inter_assoc],
    rw this,
    symmetry,
    apply times_cont_diff_within_at_inter,
    have : u ∈ 𝓝 (I.symm (I x)),
      by { rw [model_with_corners.left_inv], exact mem_nhds_sets u_open xu },
    apply continuous_at.preimage_mem_nhds I.continuous_symm.continuous_at this,
  end,
  right_invariance :=
  begin
    assume s x f e he hx h,
    have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)), by simp only [hx] with mfld_simps,
    rw this at h,
    have : I (e x) ∈ (I.symm) ⁻¹' e.target ∩ range ⇑I, by simp only [hx] with mfld_simps,
    have := ((mem_groupoid_of_pregroupoid.2 he).2.times_cont_diff_within_at this).of_le le_top,
    convert h.comp' this using 1,
    { ext y, simp only with mfld_simps },
    { ext y, split; { assume hy, simp only with mfld_simps at hy, simp only [hy] with mfld_simps } }
  end,
  congr :=
  begin
    assume s x f g h hx hf,
    apply hf.congr_of_eventually_eq (filter.eventually_eq_of_mem self_mem_nhds_within _),
    { assume y hy,
      simp only [(∘)],
      rw h,
      exact hy.2 }
  end,
  left_invariance :=
  begin
    assume s x f e' he' hs hx h,
    have A : (I' ∘ f ∘ I.symm) (I x) ∈ (I'.symm ⁻¹' e'.source ∩ range I'),
      by simp only [hx] with mfld_simps,
    have := ((mem_groupoid_of_pregroupoid.2 he').1.times_cont_diff_within_at A).of_le le_top,
    convert this.comp h _,
    { ext y, simp only with mfld_simps },
    { assume y hy, simp only with mfld_simps at hy, simpa only [hy] with mfld_simps using hs hy.2 }
  end }
