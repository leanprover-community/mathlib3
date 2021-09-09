/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import geometry.manifold.smooth_manifold_with_corners

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
`hG.lift_prop_within_at_congr` saying that if `lift_prop_within_at P g s x` holds, and `g` and `g'`
coincide on `s`, then `lift_prop_within_at P g' s x` holds. We can't call it
`lift_prop_within_at.congr` as it is in the namespace associated to `local_invariant_prop`, not
in the one for `lift_prop_within_at`.
-/

noncomputable theory
open_locale classical manifold topological_space

open set

variables {H : Type*} {M : Type*} [topological_space H] [topological_space M] [charted_space H M]
{H' : Type*} {M' : Type*} [topological_space H'] [topological_space M'] [charted_space H' M']

namespace structure_groupoid

variables (G : structure_groupoid H) (G' : structure_groupoid H')

/-- Structure recording good behavior of a property of a triple `(f, s, x)` where `f` is a function,
`s` a set and `x` a point. Good behavior here means locality and invariance under given groupoids
(both in the source and in the target). Given such a good behavior, the lift of this property
to charted spaces admitting these groupoids will inherit the good behavior. -/
structure local_invariant_prop (P : (H → H') → (set H) → H → Prop) : Prop :=
(is_local : ∀ {s x u} {f : H → H'}, is_open u → x ∈ u → (P f s x ↔ P f (s ∩ u) x))
(right_invariance : ∀ {s x f} {e : local_homeomorph H H}, e ∈ G → x ∈ e.source → P f s x →
                      P (f ∘ e.symm) (e.target ∩ e.symm ⁻¹' s) (e x))
(congr : ∀ {s x} {f g : H → H'}, (∀ y ∈ s, f y = g y) → (f x = g x) → P f s x → P g s x)
(left_invariance : ∀ {s x f} {e' : local_homeomorph H' H'}, e' ∈ G' → s ⊆ f ⁻¹' (e'.source) →
                     f x ∈ e'.source → P f s x → P (e' ∘ f) s x)

end structure_groupoid

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property in a charted space, by requiring that it holds at the preferred chart at
this point. (When the property is local and invariant, it will in fact hold using any chart, see
`lift_prop_within_at_indep_chart`). We require continuity in the lifted property, as otherwise one
single chart might fail to capture the behavior of the function.
-/
def charted_space.lift_prop_within_at (P : (H → H') → set H → H → Prop)
  (f : M → M') (s : set M) (x : M) : Prop :=
continuous_within_at f s x ∧
P ((chart_at H' (f x)) ∘ f ∘ (chart_at H x).symm)
  ((chart_at H x).target ∩ (chart_at H x).symm ⁻¹' (s ∩ f ⁻¹' (chart_at H' (f x)).source))
  (chart_at H x x)

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of functions on sets in a charted space, by requiring that it holds
around each point of the set, in the preferred charts. -/
def charted_space.lift_prop_on (P : (H → H') → set H → H → Prop) (f : M → M') (s : set M) :=
∀ x ∈ s, charted_space.lift_prop_within_at P f s x

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function at a point in a charted space, by requiring that it holds
in the preferred chart. -/
def charted_space.lift_prop_at (P : (H → H') → set H → H → Prop) (f : M → M') (x : M) :=
charted_space.lift_prop_within_at P f univ x

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function in a charted space, by requiring that it holds
in the preferred chart around every point. -/
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
      is_open.mem_nhds (is_open.inter f.open_source f'.open_source) ⟨xf, xf'⟩,
    rcases mem_nhds_within.1 (hgs.preimage_mem_nhds_within this) with ⟨u, u_open, xu, hu⟩,
    refine ⟨u ∩ e.source ∩ e'.source, _, ⟨⟨xu, xe⟩, xe'⟩, _, _, _, _⟩,
    { exact is_open.inter (is_open.inter u_open e.open_source) e'.open_source },
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
  { exact is_open.inter w.open_target
      (e'.continuous_on_symm.preimage_open_of_open e'.open_target o_open) },
  { simp only [xe', xe, xo] with mfld_simps },
end

lemma lift_prop_within_at_indep_chart [has_groupoid M G] [has_groupoid M' G']
  (he : e ∈ G.maximal_atlas M) (xe : x ∈ e.source)
  (hf : f ∈ G'.maximal_atlas M') (xf : g x ∈ f.source) :
  lift_prop_within_at P g s x ↔
    continuous_within_at g s x ∧ P (f ∘ g ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' (s ∩ g⁻¹' f.source)) (e x) :=
⟨λ H, ⟨H.1,
  hG.lift_prop_within_at_indep_chart_aux (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) he xe
  (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) hf xf H.1 H.2⟩,
λ H, ⟨H.1,
  hG.lift_prop_within_at_indep_chart_aux he xe (chart_mem_maximal_atlas _ _) (mem_chart_source _ _)
    hf xf (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) H.1 H.2⟩⟩

lemma lift_prop_on_indep_chart [has_groupoid M G] [has_groupoid M' G']
  (he : e ∈ G.maximal_atlas M) (hf : f ∈ G'.maximal_atlas M') (h : lift_prop_on P g s) :
  ∀ y ∈ e.target ∩ e.symm ⁻¹' (s ∩ g ⁻¹' f.source),
  P (f ∘ g ∘ e.symm) (e.target ∩ e.symm ⁻¹' (s ∩ g ⁻¹' f.source)) y :=
begin
  assume y hy,
  simp only with mfld_simps at hy,
  have : e.symm y ∈ s, by simp only [hy] with mfld_simps,
  convert ((hG.lift_prop_within_at_indep_chart he _ hf _).1 (h _ this)).2,
  repeat { simp only [hy] with mfld_simps },
end

lemma lift_prop_within_at_inter' (ht : t ∈ 𝓝[s] x) :
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
      is_open.mem_nhds ((chart_at H' (g x))).open_source (mem_chart_source H' (g x)),
    rcases mem_nhds_within.1 (hcont.preimage_mem_nhds_within this) with ⟨v, v_open, xv, hv⟩,
    refine ⟨u ∩ v ∩ (chart_at H x).source, _, ⟨⟨xu, xv⟩, mem_chart_source _ _⟩, _, _, _⟩,
    { exact is_open.inter (is_open.inter u_open v_open) (chart_at H x).open_source },
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
  have : ∀ y, y ∈ o ∩ s → y ∈ t := ost,
  mfld_set_tac
end

lemma lift_prop_within_at_inter (ht : t ∈ 𝓝 x) :
  lift_prop_within_at P g (s ∩ t) x ↔ lift_prop_within_at P g s x :=
hG.lift_prop_within_at_inter' (mem_nhds_within_of_mem_nhds ht)

lemma lift_prop_at_of_lift_prop_within_at (h : lift_prop_within_at P g s x) (hs : s ∈ 𝓝 x) :
  lift_prop_at P g x :=
begin
  have : s = univ ∩ s, by rw univ_inter,
  rwa [this, hG.lift_prop_within_at_inter hs] at h,
end

lemma lift_prop_within_at_of_lift_prop_at_of_mem_nhds (h : lift_prop_at P g x) (hs : s ∈ 𝓝 x) :
  lift_prop_within_at P g s x :=
begin
  have : s = univ ∩ s, by rw univ_inter,
  rwa [this, hG.lift_prop_within_at_inter hs],
end

lemma lift_prop_on_of_locally_lift_prop_on
  (h : ∀x∈s, ∃u, is_open u ∧ x ∈ u ∧ lift_prop_on P g (s ∩ u)) :
  lift_prop_on P g s :=
begin
  assume x hx,
  rcases h x hx with ⟨u, u_open, xu, hu⟩,
  have := hu x ⟨hx, xu⟩,
  rwa hG.lift_prop_within_at_inter at this,
  exact is_open.mem_nhds u_open xu,
end

lemma lift_prop_of_locally_lift_prop_on
  (h : ∀x, ∃u, is_open u ∧ x ∈ u ∧ lift_prop_on P g u) :
  lift_prop P g :=
begin
  rw ← lift_prop_on_univ,
  apply hG.lift_prop_on_of_locally_lift_prop_on (λ x hx, _),
  simp [h x],
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

lemma lift_prop_within_at_congr_iff (h₁ : ∀ y ∈ s, g' y = g y) (hx : g' x = g x) :
  lift_prop_within_at P g' s x ↔ lift_prop_within_at P g s x :=
⟨λ h, hG.lift_prop_within_at_congr h (λ y hy, (h₁ y hy).symm) hx.symm,
 λ h, hG.lift_prop_within_at_congr h h₁ hx⟩

lemma lift_prop_within_at_congr_of_eventually_eq
  (h : lift_prop_within_at P g s x) (h₁ : g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x) :
  lift_prop_within_at P g' s x :=
begin
  rcases h₁.exists_mem with ⟨t, t_nhd, ht⟩,
  rw ← hG.lift_prop_within_at_inter' t_nhd at h ⊢,
  exact hG.lift_prop_within_at_congr h (λ y hy, ht hy.2) hx
end

lemma lift_prop_within_at_congr_iff_of_eventually_eq
  (h₁ : g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x) :
  lift_prop_within_at P g' s x ↔ lift_prop_within_at P g s x :=
⟨λ h, hG.lift_prop_within_at_congr_of_eventually_eq h h₁.symm hx.symm,
 λ h, hG.lift_prop_within_at_congr_of_eventually_eq h h₁ hx⟩

lemma lift_prop_at_congr_of_eventually_eq (h : lift_prop_at P g x) (h₁ : g' =ᶠ[𝓝 x] g) :
  lift_prop_at P g' x :=
begin
  apply hG.lift_prop_within_at_congr_of_eventually_eq h _ h₁.eq_of_nhds,
  convert h₁,
  rw nhds_within_univ
end

lemma lift_prop_at_congr_iff_of_eventually_eq
  (h₁ : g' =ᶠ[𝓝 x] g) : lift_prop_at P g' x ↔ lift_prop_at P g x :=
⟨λ h, hG.lift_prop_at_congr_of_eventually_eq h h₁.symm,
 λ h, hG.lift_prop_at_congr_of_eventually_eq h h₁⟩

lemma lift_prop_on_congr (h : lift_prop_on P g s) (h₁ : ∀ y ∈ s, g' y = g y) :
  lift_prop_on P g' s :=
λ x hx, hG.lift_prop_within_at_congr (h x hx) h₁ (h₁ x hx)

lemma lift_prop_on_congr_iff (h₁ : ∀ y ∈ s, g' y = g y) :
  lift_prop_on P g' s ↔ lift_prop_on P g s :=
⟨λ h, hG.lift_prop_on_congr h (λ y hy, (h₁ y hy).symm), λ h, hG.lift_prop_on_congr h h₁⟩

omit hG

lemma lift_prop_within_at_mono
  (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
  (h : lift_prop_within_at P g t x) (hst : s ⊆ t) :
  lift_prop_within_at P g s x :=
begin
  refine ⟨h.1.mono hst, _⟩,
  apply mono (λ y hy, _) h.2,
  simp only with mfld_simps at hy,
  simp only [hy, hst _] with mfld_simps,
end

lemma lift_prop_within_at_of_lift_prop_at
  (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x) (h : lift_prop_at P g x) :
  lift_prop_within_at P g s x :=
begin
  rw ← lift_prop_within_at_univ at h,
  exact lift_prop_within_at_mono mono h (subset_univ _),
end

lemma lift_prop_on_mono (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
  (h : lift_prop_on P g t) (hst : s ⊆ t) :
  lift_prop_on P g s :=
λ x hx, lift_prop_within_at_mono mono (h x (hst hx)) hst

lemma lift_prop_on_of_lift_prop
  (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x) (h : lift_prop P g) :
  lift_prop_on P g s :=
begin
  rw ← lift_prop_on_univ at h,
  exact lift_prop_on_mono mono h (subset_univ _)
end

lemma lift_prop_at_of_mem_maximal_atlas [has_groupoid M G]
  (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y)
  (he : e ∈ maximal_atlas M G) (hx : x ∈ e.source) : lift_prop_at Q e x :=
begin
  suffices h : Q (e ∘ e.symm) e.target (e x),
  { rw [lift_prop_at, hG.lift_prop_within_at_indep_chart he hx G.id_mem_maximal_atlas (mem_univ _)],
    refine ⟨(e.continuous_at hx).continuous_within_at, _⟩,
    simpa only with mfld_simps },
  have A : Q id e.target (e x),
  { have : e x ∈ e.target, by simp only [hx] with mfld_simps,
    simpa only with mfld_simps using (hG.is_local e.open_target this).1 (hQ (e x)) },
  apply hG.congr _ _ A;
  simp only [hx] with mfld_simps {contextual := tt}
end

lemma lift_prop_on_of_mem_maximal_atlas [has_groupoid M G]
  (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) (he : e ∈ maximal_atlas M G) :
  lift_prop_on Q e e.source :=
begin
  assume x hx,
  apply hG.lift_prop_within_at_of_lift_prop_at_of_mem_nhds
    (hG.lift_prop_at_of_mem_maximal_atlas hQ he hx),
  apply is_open.mem_nhds e.open_source hx,
end

lemma lift_prop_at_symm_of_mem_maximal_atlas [has_groupoid M G] {x : H}
  (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y)
  (he : e ∈ maximal_atlas M G) (hx : x ∈ e.target) : lift_prop_at Q e.symm x :=
begin
  suffices h : Q (e ∘ e.symm) e.target x,
  { have A : e.symm ⁻¹' e.source ∩ e.target = e.target,
      by mfld_set_tac,
    have : e.symm x ∈ e.source, by simp only [hx] with mfld_simps,
    rw [lift_prop_at,
      hG.lift_prop_within_at_indep_chart G.id_mem_maximal_atlas (mem_univ _) he this],
    refine ⟨(e.symm.continuous_at hx).continuous_within_at, _⟩,
    simp only with mfld_simps,
    rwa [hG.is_local e.open_target hx, A] },
  have A : Q id e.target x,
    by simpa only with mfld_simps using (hG.is_local e.open_target hx).1 (hQ x),
  apply hG.congr _ _ A;
  simp only [hx] with mfld_simps {contextual := tt}
end

lemma lift_prop_on_symm_of_mem_maximal_atlas [has_groupoid M G]
  (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) (he : e ∈ maximal_atlas M G) :
  lift_prop_on Q e.symm e.target :=
begin
  assume x hx,
  apply hG.lift_prop_within_at_of_lift_prop_at_of_mem_nhds
    (hG.lift_prop_at_symm_of_mem_maximal_atlas hQ he hx),
  apply is_open.mem_nhds e.open_target hx,
end

lemma lift_prop_at_chart [has_groupoid M G]
  (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) : lift_prop_at Q (chart_at H x) x :=
hG.lift_prop_at_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x) (mem_chart_source H x)

lemma lift_prop_on_chart [has_groupoid M G]
  (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) :
  lift_prop_on Q (chart_at H x) (chart_at H x).source :=
hG.lift_prop_on_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x)

lemma lift_prop_at_chart_symm [has_groupoid M G]
  (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) :
  lift_prop_at Q (chart_at H x).symm ((chart_at H x) x) :=
hG.lift_prop_at_symm_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x) (by simp)

lemma lift_prop_on_chart_symm [has_groupoid M G]
  (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) :
  lift_prop_on Q (chart_at H x).symm (chart_at H x).target :=
hG.lift_prop_on_symm_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x)

lemma lift_prop_id (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) :
  lift_prop Q (id : M → M) :=
begin
  assume x,
  dsimp [lift_prop_at, lift_prop_within_at],
  refine ⟨continuous_within_at_id, _⟩,
  let t := ((chart_at H x).target ∩ (chart_at H x).symm ⁻¹' (chart_at H x).source),
  suffices H : Q id t ((chart_at H x) x),
  { simp only with mfld_simps,
    refine hG.congr (λ y hy, _) (by simp) H,
    simp only with mfld_simps at hy,
    simp only [hy] with mfld_simps },
  have : t = univ ∩ (chart_at H x).target, by mfld_set_tac,
  rw this,
  exact (hG.is_local (chart_at H x).open_target (by simp)).1 (hQ _)
end

end local_invariant_prop

section local_structomorph

variables (G)
open local_homeomorph

/-- A function from a model space `H` to itself is a local structomorphism, with respect to a
structure groupoid `G` for `H`, relative to a set `s` in `H`, if for all points `x` in the set, the
function agrees with a `G`-structomorphism on `s` in a neighbourhood of `x`. -/
def is_local_structomorph_within_at (f : H → H) (s : set H) (x : H) : Prop :=
(x ∈ s) → ∃ (e : local_homeomorph H H), e ∈ G ∧ eq_on f e.to_fun (s ∩ e.source) ∧ x ∈ e.source

/-- For a groupoid `G` which is `closed_under_restriction`, being a local structomorphism is a local
invariant property. -/
lemma is_local_structomorph_within_at_local_invariant_prop [closed_under_restriction G] :
  local_invariant_prop G G (is_local_structomorph_within_at G) :=
{ is_local := begin
    intros s x u f hu hux,
    split,
    { rintros h hx,
      rcases h hx.1 with ⟨e, heG, hef, hex⟩,
      have : s ∩ u ∩ e.source ⊆ s ∩ e.source := by mfld_set_tac,
      exact ⟨e, heG, hef.mono this, hex⟩ },
    { rintros h hx,
      rcases h ⟨hx, hux⟩ with ⟨e, heG, hef, hex⟩,
      refine ⟨e.restr (interior u), _, _, _⟩,
      { exact closed_under_restriction' heG (is_open_interior) },
      { have : s ∩ u ∩ e.source = s ∩ (e.source ∩ u) := by mfld_set_tac,
        simpa only [this, interior_interior, hu.interior_eq] with mfld_simps using hef },
      { simp only [*, interior_interior, hu.interior_eq] with mfld_simps } }
  end,
  right_invariance := begin
    intros s x f e' he'G he'x h hx,
    have hxs : x ∈ s := by simpa only [e'.left_inv he'x] with mfld_simps using hx.2,
    rcases h hxs with ⟨e, heG, hef, hex⟩,
    refine ⟨e'.symm.trans e, G.trans (G.symm he'G) heG, _, _⟩,
    { intros y hy,
      simp only with mfld_simps at hy,
      simp only [hef ⟨hy.1.2, hy.2.2⟩] with mfld_simps },
    { simp only [hex, he'x] with mfld_simps }
  end,
  congr := begin
    intros s x f g hfgs hfg' h hx,
    rcases h hx with ⟨e, heG, hef, hex⟩,
    refine ⟨e, heG, _, hex⟩,
    intros y hy,
    rw [← hef hy, hfgs y hy.1]
  end,
  left_invariance := begin
    intros s x f e' he'G he' hfx h hx,
    rcases h hx with ⟨e, heG, hef, hex⟩,
    refine ⟨e.trans e', G.trans heG he'G, _, _⟩,
    { intros y hy,
      simp only with mfld_simps at hy,
      simp only [hef ⟨hy.1, hy.2.1⟩] with mfld_simps },
    { simpa only [hex, hef ⟨hx, hex⟩] with mfld_simps using hfx }
  end }

end local_structomorph

end structure_groupoid
