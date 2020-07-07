/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import geometry.manifold.smooth_manifold_with_corners
import analysis.calculus.times_cont_diff
import tactic.basic

/-!
# Local properties invariant under a groupoid

We study properties of a triple `(g, s, x)` where `g` is a function between two spaces `H` and `H'`,
`s` is a subset of `H` and `x` is a point of `H`. Our goal is to register how such a property
should behave to make sense in charted spaces modelled on `H` and `H'`.

The main examples we have in mind are the properties "`g` is differentiable at `x` within `s`", or
"`g` is smooth at `x` within `s`". We want to develop general results that, when applied in these
specific situations, say that the notion of smooth function in a manifold behaves well under
restriction, intersection, is local, and so on.

## Main definitions

* `local_invariant_prop G G' P` says that a property `P` of a triple `(g, s, x)` is local, and
  invariant under composition by elements of the groupoids `G` and `G'` of `H` and `H'`
  respectively.
* `local_invariant_mono_prop G G' P` requires additionally that the property is invariant under
  arbitrary restriction, i.e., if it holds for `(g, s, x)`, then it holds for `(g, t, x)` when
  `t` is a subset of `s`.
* `charted_space.lift_prop_within_at` (resp. `lift_prop_at`, `lift_prop_on` and `lift_prop`):
  given a property `P` of `(g, s, x)` where `g : H → H'`, define the corresponding property
  for functions `M → M'` where `M` and `M'` are charted spaces modelled respectively on `H` and
  `H'`. We define these properties within a set at a point, or at a point, or on a set, or in the
  whole space. This lifting process (obtained by restricting to suitable chart domains) can always
  be done, but it only behaves well under locality and invariance assumptions.

Given `hG : local_invariant_prop G G' P`, we deduce many properties of the lifted property on the
charted spaces. For instance, `hG.lift_prop_within_at_inter` says that `P g s x` is equivalent to
`P g (s ∩ t) x` whenever `t` is a neighborhood of `x`.

## Implementation notes

We do not use dot notation for properties of the lifted property. For instance, we have
`hG.lift_prop_within_at_of_lift_prop_at` saying that if `lift_prop_at P g x` holds, then
`lift_prop_within_at P g s x` holds. We can't call it `lift_prop_at.lift_prop_within_at` as it is
in the namespace associated to `local_invariant_prop`, not in the one for `lift_prop_at`.
-/

noncomputable theory
open_locale classical manifold topological_space
universes u

open set

variables {H : Type u} {M : Type*} [topological_space H] [topological_space M] [charted_space H M]
{H' : Type*} {M' : Type*} [topological_space H'] [topological_space M'] [charted_space H' M']

namespace structure_groupoid

variables (G : structure_groupoid H) (G' : structure_groupoid H')

structure local_invariant_prop (P : (H → H') → (set H) → H → Prop) : Prop :=
(is_local : ∀ {s x u} {f : H → H'}, is_open u → x ∈ u → (P f s x ↔ P f (s ∩ u) x))
(right_invariance : ∀ {s x f} {e : local_homeomorph H H}, e ∈ G → x ∈ e.source → P f s x →
                      P (f ∘ e.symm) (e.target ∩ e.symm ⁻¹' s) (e x))
(congr : ∀ {s x} {f g : H → H'}, (∀ y ∈ s, f y = g y) → (f x = g x) → P f s x → P g s x)
(left_invariance : ∀ {s x f} {e' : local_homeomorph H' H'}, e' ∈ G' → s ⊆ f ⁻¹' (e'.source) →
                     f x ∈ e'.source → P f s x → P (e' ∘ f) s x)

structure local_invariant_mono_prop (P : (H → H') → (set H) → H → Prop)
  extends local_invariant_prop G G' P : Prop :=
(mono : ∀ {s x t} {f : H → H'}, t ⊆ s → P f s x → P f t x)

end structure_groupoid

/-- If one can define a property of germs of functions and sets in the model space, then one define
a corresponding property in the manifold, by requiring that it holds for all preferred charts. -/
def charted_space.lift_prop_within_at (P : (H → H') → set H → H → Prop)
  (f : M → M') (s : set M) (x : M) : Prop :=
continuous_within_at f s x ∧
P ((chart_at H' (f x)) ∘ f ∘ (chart_at H x).symm)
  ((chart_at H x).target ∩ (chart_at H x).symm ⁻¹' (s ∩ f ⁻¹' (chart_at H' (f x)).source))
  (chart_at H x x)

def charted_space.lift_prop_on (P : (H → H') → set H → H → Prop) (f : M → M') (s : set M) :=
∀ x ∈ s, charted_space.lift_prop_within_at P f s x

def charted_space.lift_prop_at (P : (H → H') → set H → H → Prop) (f : M → M') (x : M) :=
charted_space.lift_prop_within_at P f univ x

def charted_space.lift_prop (P : (H → H') → set H → H → Prop) (f : M → M') :=
∀ x, charted_space.lift_prop_at P f x

open charted_space

namespace structure_groupoid

variables {G : structure_groupoid H} {G' : structure_groupoid H'}
{e e' : local_homeomorph M H} {f f' : local_homeomorph M' H'}
{P : (H → H') → set H → H → Prop} {g g' : M → M'} {s t : set M} {x : M}
{Q : (H → H) → set H → H → Prop}

lemma lift_prop_within_at_univ :
  lift_prop_within_at P g univ x ↔ lift_prop_at P g x :=
iff.rfl

lemma lift_prop_on_univ :
  lift_prop_on P g univ ↔ lift_prop P g :=
by simp [lift_prop_on, lift_prop, lift_prop_at]

namespace local_invariant_prop

variable (hG : G.local_invariant_prop G' P)
include hG

/-- If a property of a germ of function `g` on a pointed set `(s, x)` is invariant under the
structure groupoid (by composition in the source space and in the target space), then
expressing it in charted spaces does not depend on the element of the maximal atlas one uses
both in the source and in the target manifolds, provided they are defined around `x` and `g x`
respectively, and provided `g` is continuous within `s` at `x` (otherwise, the local behavior
of `g` at `x` can not be captured with a chart in the target). -/
lemma lift_prop_within_at_indep_chart_aux
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

lemma lift_prop_within_at_indep_chart [has_groupoid M G] [has_groupoid M' G']
  (he : e ∈ G.maximal_atlas M) (xe : x ∈ e.source)
  (hf : f ∈ G'.maximal_atlas M') (xf : g x ∈ f.source) :
  lift_prop_within_at P g s x ↔
  continuous_within_at g s x ∧ P (f ∘ g ∘ e.symm) (e.target ∩ e.symm ⁻¹' (s ∩ g⁻¹' f.source)) (e x) :=
⟨λ H, ⟨H.1,
  hG.lift_prop_within_at_indep_chart_aux (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) he xe
  (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) hf xf H.1 H.2⟩,
λ H, ⟨H.1,
  hG.lift_prop_within_at_indep_chart_aux he xe (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) hf xf
  (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) H.1 H.2⟩⟩

lemma lift_prop_within_at_inter' (ht : t ∈ nhds_within x s) :
  lift_prop_within_at P g (s ∩ t) x ↔ lift_prop_within_at P g s x :=
begin
  by_cases hcont : ¬ (continuous_within_at g s x),
  { have : ¬ (continuous_within_at g (s ∩ t) x), by rwa [continuous_within_at_inter' ht],
    simp only [lift_prop_within_at, hcont, this, false_and] },
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
  simp only [lift_prop_within_at, A, hcont, true_and, preimage_inter],
  have B : is_open ((chart_at H x).target ∩ (chart_at H x).symm⁻¹' o) :=
    (chart_at H x).preimage_open_of_open_symm o_open,
  have C : (chart_at H x) x ∈ (chart_at H x).target ∩ (chart_at H x).symm⁻¹' o,
    by simp only [xo] with mfld_simps,
  conv_lhs { rw hG.is_local B C },
  conv_rhs { rw hG.is_local B C },
  congr' 2,
  ext y,
  split;
  { assume hy, simp only with mfld_simps at hy, simp only [hy, ost _] with mfld_simps }
end

lemma lift_prop_within_at_inter (ht : t ∈ 𝓝 x) :
  lift_prop_within_at P g (s ∩ t) x ↔ lift_prop_within_at P g s x :=
hG.lift_prop_within_at_inter' (mem_nhds_within_of_mem_nhds ht)

lemma lift_prop_within_at_to_lift_prop_at (h : lift_prop_within_at P g s x) (hs : s ∈ 𝓝 x) :
  lift_prop_at P g x :=
begin
  have : s = univ ∩ s, by rw univ_inter,
  rwa [this, hG.lift_prop_within_at_inter hs] at h,
end

lemma lift_prop_on_of_locally_lift_prop_on
  (h : ∀x∈s, ∃u, is_open u ∧ x ∈ u ∧ lift_prop_on P g (s ∩ u)) :
  lift_prop_on P g s :=
begin
  assume x hx,
  rcases h x hx with ⟨u, u_open, xu, hu⟩,
  have := hu x ⟨hx, xu⟩,
  rwa hG.lift_prop_within_at_inter at this,
  exact mem_nhds_sets u_open xu,
end

lemma lift_prop_within_at_congr
  (h : lift_prop_within_at P g s x) (h₁ : ∀ y ∈ s, g' y = g y) (hx : g' x = g x) :
  lift_prop_within_at P g' s x :=
begin
  refine ⟨h.1.congr h₁ hx, _⟩,
  have A : s ∩ g' ⁻¹' (chart_at H' (g' x)).source = s ∩ g ⁻¹' (chart_at H' (g' x)).source,
  { ext y,
    split,
    { assume hy,
      simp only with mfld_simps at hy,
      simp only [hy, ← h₁ _ hy.1] with mfld_simps },
    { assume hy,
      simp only with mfld_simps at hy,
      simp only [hy, h₁ _ hy.1] with mfld_simps } },
  have := h.2,
  rw [← hx, ← A] at this,
  convert hG.congr _ _ this using 2,
  { assume y hy,
    simp only with mfld_simps at hy,
    have : (chart_at H x).symm y ∈ s, by simp only [hy],
    simp only [hy, h₁ _ this] with mfld_simps },
  { simp only [hx] with mfld_simps }
end

lemma lift_prop_within_at_congr_of_eventually_eq
  (h : lift_prop_within_at P g s x) (h₁ : g' =ᶠ[nhds_within x s] g) (hx : g' x = g x) :
  lift_prop_within_at P g' s x :=
begin
  rcases h₁.exists_mem with ⟨t, t_nhd, ht⟩,
  rw ← hG.lift_prop_within_at_inter' t_nhd at h ⊢,
  exact hG.lift_prop_within_at_congr h (λ y hy, ht _ hy.2) hx
end

omit hG

lemma lift_prop_at_chart [has_groupoid M G]
  (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y)
  (he : e ∈ maximal_atlas M G) (hx : x ∈ e.source) :
  lift_prop_at Q e x :=
begin
  suffices h : Q (e ∘ e.symm) e.target (e x),
  { rw [lift_prop_at, hG.lift_prop_within_at_indep_chart he hx G.id_mem_maximal_atlas (mem_univ _)],
    refine ⟨(e.continuous_at hx).continuous_within_at, _⟩,
    simpa only with mfld_simps },
  have A : Q id e.target (e x),
  { have Z := hQ (e x),
    have : e x ∈ e.target, by simp only [hx] with mfld_simps,
    have T := hG.is_local e.open_target this,
  },
end


end local_invariant_prop

namespace local_invariant_mono_prop

variable (hG : G.local_invariant_mono_prop G' P)
include hG

lemma lift_prop_within_at_mono (h : lift_prop_within_at P g t x) (hst : s ⊆ t) :
  lift_prop_within_at P g s x :=
begin
  refine ⟨h.1.mono hst, _⟩,
  apply hG.mono (λ y hy, _) h.2,
  simp only with mfld_simps at hy,
  simp only [hy, hst _] with mfld_simps,
end

lemma lift_prop_within_at_of_lift_prop_at (h : lift_prop_at P g x) : lift_prop_within_at P g s x :=
begin
  rw ← lift_prop_within_at_univ at h,
  exact hG.lift_prop_within_at_mono h (subset_univ _),
end

lemma lift_prop_on_mono (h : lift_prop_on P g t) (hst : s ⊆ t) :
  lift_prop_on P g s :=
λ x hx, hG.lift_prop_within_at_mono (h x (hst hx)) hst

lemma lift_prop_on_of_lift_prop (h : lift_prop P g) : lift_prop_on P g s :=
begin
  rw ← lift_prop_on_univ at h,
  exact hG.lift_prop_on_mono h (subset_univ _)
end

end local_invariant_mono_prop

end structure_groupoid

#exit





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
