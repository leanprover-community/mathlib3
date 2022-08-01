/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import geometry.manifold.charted_space

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

open set filter

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
                      P (f ∘ e.symm) (e.symm ⁻¹' s) (e x))
(congr_of_forall : ∀ {s x} {f g : H → H'}, (∀ y ∈ s, f y = g y) → f x = g x → P f s x → P g s x)
(left_invariance' : ∀ {s x f} {e' : local_homeomorph H' H'}, e' ∈ G' → s ⊆ f ⁻¹' e'.source →
                     f x ∈ e'.source → P f s x → P (e' ∘ f) s x)

variables {G G'} {P : (H → H') → (set H) → H → Prop} {s t u : set H} {x : H}

variable (hG : G.local_invariant_prop G' P)
include hG

namespace local_invariant_prop

lemma congr_set {s t : set H} {x : H} {f : H → H'} (hu : s =ᶠ[𝓝 x] t) :
  P f s x ↔ P f t x :=
begin
  obtain ⟨o, host, ho, hxo⟩ := mem_nhds_iff.mp hu.mem_iff,
  simp_rw [subset_def, mem_set_of, ← and.congr_left_iff, ← mem_inter_iff, ← set.ext_iff] at host,
  rw [hG.is_local ho hxo, host, ← hG.is_local ho hxo]
end

lemma is_local_nhds {s u : set H} {x : H} {f : H → H'} (hu : u ∈ 𝓝[s] x) :
  P f s x ↔ P f (s ∩ u) x :=
hG.congr_set $ mem_nhds_within_iff_eventually_eq.mp hu

lemma left_invariance {s : set H} {x : H} {f : H → H'} {e' : local_homeomorph H' H'}
  (he' : e' ∈ G') (hfs : continuous_within_at f s x) (hxe' : f x ∈ e'.source) (hP : P f s x) :
  P (e' ∘ f) s x :=
begin
  rw [hG.is_local_nhds (hfs.preimage_mem_nhds_within $ e'.open_source.mem_nhds hxe')] at hP ⊢,
  exact hG.left_invariance' he' (inter_subset_right _ _) hxe' hP
end

lemma congr_iff_nhds_within {s : set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g)
  (h2 : f x = g x) : P f s x ↔ P g s x :=
by { simp_rw [hG.is_local_nhds h1],
  exact ⟨hG.congr_of_forall (λ y hy, hy.2) h2, hG.congr_of_forall (λ y hy, hy.2.symm) h2.symm⟩ }

lemma congr_nhds_within {s : set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
  (hP : P f s x) : P g s x :=
(hG.congr_iff_nhds_within h1 h2).mp hP

lemma congr_nhds_within' {s : set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
  (hP : P g s x) : P f s x :=
(hG.congr_iff_nhds_within h1 h2).mpr hP

lemma congr_iff {s : set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) : P f s x ↔ P g s x :=
hG.congr_iff_nhds_within (mem_nhds_within_of_mem_nhds h) (mem_of_mem_nhds h : _)

lemma congr {s : set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) (hP : P f s x) : P g s x :=
(hG.congr_iff h).mp hP

lemma congr' {s : set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) (hP : P g s x) : P f s x :=
hG.congr h.symm hP

end local_invariant_prop
end structure_groupoid

namespace charted_space

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property in a charted space, by requiring that it holds at the preferred chart at
this point. (When the property is local and invariant, it will in fact hold using any chart, see
`lift_prop_within_at_indep_chart`). We require continuity in the lifted property, as otherwise one
single chart might fail to capture the behavior of the function.
-/
def lift_prop_within_at (P : (H → H') → set H → H → Prop)
  (f : M → M') (s : set M) (x : M) : Prop :=
continuous_within_at f s x ∧
P (chart_at H' (f x) ∘ f ∘ (chart_at H x).symm) ((chart_at H x).symm ⁻¹' s) (chart_at H x x)

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of functions on sets in a charted space, by requiring that it holds
around each point of the set, in the preferred charts. -/
def lift_prop_on (P : (H → H') → set H → H → Prop) (f : M → M') (s : set M) :=
∀ x ∈ s, lift_prop_within_at P f s x

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function at a point in a charted space, by requiring that it holds
in the preferred chart. -/
def lift_prop_at (P : (H → H') → set H → H → Prop) (f : M → M') (x : M) :=
lift_prop_within_at P f univ x

lemma lift_prop_at_iff {P : (H → H') → set H → H → Prop} {f : M → M'} {x : M} :
  lift_prop_at P f x ↔ continuous_at f x ∧
  P (chart_at H' (f x) ∘ f ∘ (chart_at H x).symm) univ (chart_at H x x) :=
by rw [lift_prop_at, lift_prop_within_at, continuous_within_at_univ, preimage_univ]

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function in a charted space, by requiring that it holds
in the preferred chart around every point. -/
def lift_prop (P : (H → H') → set H → H → Prop) (f : M → M') :=
∀ x, lift_prop_at P f x

lemma lift_prop_iff {P : (H → H') → set H → H → Prop} {f : M → M'} :
  lift_prop P f ↔ continuous f ∧
  ∀ x, P (chart_at H' (f x) ∘ f ∘ (chart_at H x).symm) univ (chart_at H x x) :=
by simp_rw [lift_prop, lift_prop_at_iff, forall_and_distrib, continuous_iff_continuous_at]

end charted_space
open charted_space

namespace structure_groupoid

variables {G : structure_groupoid H} {G' : structure_groupoid H'}
{e e' : local_homeomorph M H} {f f' : local_homeomorph M' H'}
{P : (H → H') → set H → H → Prop} {g g' : M → M'} {s t : set M} {x : M}
{Q : (H → H) → set H → H → Prop}

lemma lift_prop_within_at_univ : lift_prop_within_at P g univ x ↔ lift_prop_at P g x :=
iff.rfl

lemma lift_prop_on_univ : lift_prop_on P g univ ↔ lift_prop P g :=
by simv [lift_prop_on, lift_prop, lift_prop_at]

namespace local_invariant_prop

variable (hG : G.local_invariant_prop G' P)
include hG

/-- `lift_prop_within_at P f s x` is equivalent to a definition where we restrict the set we are
  considering to the domain of the charts at `x` and `f x`. -/
lemma lift_prop_within_at_iff {f : M → M'} (hf : continuous_within_at f s x) :
  lift_prop_within_at P f s x ↔
  P ((chart_at H' (f x)) ∘ f ∘ (chart_at H x).symm)
  ((chart_at H x).target ∩ (chart_at H x).symm ⁻¹' (s ∩ f ⁻¹' (chart_at H' (f x)).source))
  (chart_at H x x) :=
begin
  rw [lift_prop_within_at, iff_true_intro hf, true_and, hG.congr_set],
  exact local_homeomorph.preimage_eventually_eq_target_inter_preimage_inter hf
    (mem_chart_source H x) (chart_source_mem_nhds H' (f x))
end

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
  (h : P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x)) :
  P (f' ∘ g ∘ e'.symm) (e'.symm ⁻¹' s) (e' x) :=
begin
  have hcont : continuous_within_at (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x),
  { rw [← e.left_inv xe] at hgs xf,
    refine (f.continuous_at $ by exact xf).comp_continuous_within_at _,
    exact hgs.comp (e.symm.continuous_at $ e.maps_to xe).continuous_within_at subset.rfl },
  have A : P ((f.symm ≫ₕ f') ∘ (f ∘ g ∘ e.symm)) (e.symm ⁻¹' s) (e x),
  { refine hG.left_invariance (compatible_of_mem_maximal_atlas hf hf') hcont
      (by simv only [xe, xf, xf'] with mfld_simps) h },
  have B : P (f' ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x),
  { refine hG.congr_nhds_within _ (by simv only [xe, xf] with mfld_simps) A,
    simp_rw [local_homeomorph.coe_trans, eventually_eq],
    have := (e.eventually_nhds_within' _ xe).mpr (hgs.eventually $ f.eventually_left_inverse xf),
    exact this.mono (λ y, congr_arg f') },
  let w := e.symm ≫ₕ e',
  let ow := w.symm ⁻¹' (e.symm ⁻¹' s),
  have wG : w ∈ G := compatible_of_mem_maximal_atlas he he',
  have C : P ((f' ∘ g ∘ e.symm) ∘ w.symm) ow (w (e x)) :=
    hG.right_invariance wG (by simv only [w, xe, xe'] with mfld_simps) B,
  have : ∀ y ∈ e.source, w (e y) = e' y := λ y hy, by simv only [w, hy] with mfld_simps,
  rw [this x xe] at C,
  have D : P (f' ∘ g ∘ e'.symm) ow (e' x),
  { refine hG.congr _ C,
    refine ((e'.eventually_nhds' _ xe').mpr $ e.eventually_left_inverse xe).mono (λ y hy, _),
    simv only [w] with mfld_simps,
    rw [hy] },
  refine (hG.congr_set _).2 D,
  refine (eventually_of_mem _ $ λ y (hy : y ∈ e'.symm ⁻¹' e.source), _).set_eq,
  { refine (e'.symm.continuous_at $ e'.maps_to xe').preimage_mem_nhds (e.open_source.mem_nhds _),
    simp_rw [e'.left_inv xe', xe] },
  simp_rw [ow, mem_preimage, w, local_homeomorph.coe_trans_symm, local_homeomorph.symm_symm,
    function.comp_apply, e.left_inv hy]
end

lemma lift_prop_within_at_indep_chart [has_groupoid M G] [has_groupoid M' G']
  (he : e ∈ G.maximal_atlas M) (xe : x ∈ e.source)
  (hf : f ∈ G'.maximal_atlas M') (xf : g x ∈ f.source) :
  lift_prop_within_at P g s x ↔
    continuous_within_at g s x ∧ P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) :=
⟨λ H, ⟨H.1,
  hG.lift_prop_within_at_indep_chart_aux (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) he xe
  (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) hf xf H.1 H.2⟩,
λ H, ⟨H.1,
  hG.lift_prop_within_at_indep_chart_aux he xe (chart_mem_maximal_atlas _ _) (mem_chart_source _ _)
    hf xf (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) H.1 H.2⟩⟩

lemma lift_prop_on_indep_chart [has_groupoid M G] [has_groupoid M' G']
  (he : e ∈ G.maximal_atlas M) (hf : f ∈ G'.maximal_atlas M') (h : lift_prop_on P g s)
  {y : H} (hy : y ∈ e.target ∩ e.symm ⁻¹'  (s ∩ g ⁻¹' f.source)) :
  P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) y :=
begin
  convert ((hG.lift_prop_within_at_indep_chart he (e.symm_maps_to hy.1) hf hy.2.2).1
    (h _ hy.2.1)).2,
  rw [e.right_inv hy.1],
end

lemma lift_prop_within_at_inter' (ht : t ∈ 𝓝[s] x) :
  lift_prop_within_at P g (s ∩ t) x ↔ lift_prop_within_at P g s x :=
begin
  rw [lift_prop_within_at, lift_prop_within_at, continuous_within_at_inter' ht, hG.congr_set],
  simp_rw [eventually_eq_set, mem_preimage,
    (chart_at H x).eventually_nhds' (λ x, x ∈ s ∩ t ↔ x ∈ s) (mem_chart_source H x)],
  exact (mem_nhds_within_iff_eventually_eq.mp ht).symm.mem_iff
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
  (h : ∀ x ∈ s, ∃ u, is_open u ∧ x ∈ u ∧ lift_prop_on P g (s ∩ u)) :
  lift_prop_on P g s :=
begin
  assume x hx,
  rcases h x hx with ⟨u, u_open, xu, hu⟩,
  have := hu x ⟨hx, xu⟩,
  rwa hG.lift_prop_within_at_inter at this,
  exact is_open.mem_nhds u_open xu,
end

lemma lift_prop_of_locally_lift_prop_on (h : ∀ x, ∃ u, is_open u ∧ x ∈ u ∧ lift_prop_on P g u) :
  lift_prop P g :=
begin
  rw ← lift_prop_on_univ,
  apply hG.lift_prop_on_of_locally_lift_prop_on (λ x hx, _),
  simv [h x],
end

lemma lift_prop_within_at_congr_of_eventually_eq
  (h : lift_prop_within_at P g s x) (h₁ : g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x) :
  lift_prop_within_at P g' s x :=
begin
  refine ⟨h.1.congr_of_eventually_eq h₁ hx, _⟩,
  refine hG.congr_nhds_within' _ (by simp_rw [function.comp_apply,
    (chart_at H x).left_inv (mem_chart_source H x), hx]) h.2,
  simp_rw [eventually_eq, function.comp_app, (chart_at H x).eventually_nhds_within'
    (λ y, chart_at H' (g' x) (g' y) = chart_at H' (g x) (g y))
    (mem_chart_source H x)],
  exact h₁.mono (λ y hy, by rw [hx, hy])
end

lemma lift_prop_within_at_congr_iff_of_eventually_eq (h₁ :  g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x) :
  lift_prop_within_at P g' s x ↔ lift_prop_within_at P g s x :=
⟨λ h, hG.lift_prop_within_at_congr_of_eventually_eq h h₁.symm hx.symm,
 λ h, hG.lift_prop_within_at_congr_of_eventually_eq h h₁ hx⟩

lemma lift_prop_within_at_congr_iff
  (h₁ : ∀ y ∈ s, g' y = g y) (hx : g' x = g x) :
  lift_prop_within_at P g' s x ↔ lift_prop_within_at P g s x :=
hG.lift_prop_within_at_congr_iff_of_eventually_eq (eventually_nhds_within_of_forall h₁) hx

lemma lift_prop_within_at_congr
  (h : lift_prop_within_at P g s x) (h₁ : ∀ y ∈ s, g' y = g y) (hx : g' x = g x) :
  lift_prop_within_at P g' s x :=
(hG.lift_prop_within_at_congr_iff h₁ hx).mpr h

lemma lift_prop_at_congr_iff_of_eventually_eq
  (h₁ : g' =ᶠ[𝓝 x] g) : lift_prop_at P g' x ↔ lift_prop_at P g x :=
hG.lift_prop_within_at_congr_iff_of_eventually_eq (by simp_rw [nhds_within_univ, h₁]) h₁.eq_of_nhds

lemma lift_prop_at_congr_of_eventually_eq (h : lift_prop_at P g x) (h₁ : g' =ᶠ[𝓝 x] g) :
  lift_prop_at P g' x :=
(hG.lift_prop_at_congr_iff_of_eventually_eq h₁).mpr h

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
  simv only with mfld_simps at hy,
  simv only [hy, hst _] with mfld_simps,
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
  simp_rw [lift_prop_at,
    hG.lift_prop_within_at_indep_chart he hx G.id_mem_maximal_atlas (mem_univ _),
    (e.continuous_at hx).continuous_within_at, true_and],
  exact hG.congr' (e.eventually_right_inverse' hx) (hQ _)
end

lemma lift_prop_on_of_mem_maximal_atlas [has_groupoid M G]
  (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) (he : e ∈ maximal_atlas M G) :
  lift_prop_on Q e e.source :=
begin
  assume x hx,
  apply hG.lift_prop_within_at_of_lift_prop_at_of_mem_nhds
    (hG.lift_prop_at_of_mem_maximal_atlas hQ he hx),
  exact is_open.mem_nhds e.open_source hx,
end

lemma lift_prop_at_symm_of_mem_maximal_atlas [has_groupoid M G] {x : H}
  (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y)
  (he : e ∈ maximal_atlas M G) (hx : x ∈ e.target) : lift_prop_at Q e.symm x :=
begin
  suffices h : Q (e ∘ e.symm) univ x,
  { have A : e.symm ⁻¹' e.source ∩ e.target = e.target,
      by mfld_set_tac,
    have : e.symm x ∈ e.source, by simv only [hx] with mfld_simps,
    rw [lift_prop_at,
      hG.lift_prop_within_at_indep_chart G.id_mem_maximal_atlas (mem_univ _) he this],
    refine ⟨(e.symm.continuous_at hx).continuous_within_at, _⟩,
    simv only [h] with mfld_simps },
  exact hG.congr' (e.eventually_right_inverse hx) (hQ x)
end

lemma lift_prop_on_symm_of_mem_maximal_atlas [has_groupoid M G]
  (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) (he : e ∈ maximal_atlas M G) :
  lift_prop_on Q e.symm e.target :=
begin
  assume x hx,
  apply hG.lift_prop_within_at_of_lift_prop_at_of_mem_nhds
    (hG.lift_prop_at_symm_of_mem_maximal_atlas hQ he hx),
  exact is_open.mem_nhds e.open_target hx,
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
hG.lift_prop_at_symm_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x) (by simv)

lemma lift_prop_on_chart_symm [has_groupoid M G]
  (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) :
  lift_prop_on Q (chart_at H x).symm (chart_at H x).target :=
hG.lift_prop_on_symm_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x)

lemma lift_prop_id (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) :
  lift_prop Q (id : M → M) :=
begin
  simp_rw [lift_prop_iff, continuous_id, true_and],
  exact λ x, hG.congr' ((chart_at H x).eventually_right_inverse $ mem_chart_target H x) (hQ _)
end

end local_invariant_prop

section local_structomorph

variables (G)
open local_homeomorph

/-- A function from a model space `H` to itself is a local structomorphism, with respect to a
structure groupoid `G` for `H`, relative to a set `s` in `H`, if for all points `x` in the set, the
function agrees with a `G`-structomorphism on `s` in a neighbourhood of `x`. -/
def is_local_structomorph_within_at (f : H → H) (s : set H) (x : H) : Prop :=
x ∈ s → ∃ (e : local_homeomorph H H), e ∈ G ∧ eq_on f e.to_fun (s ∩ e.source) ∧ x ∈ e.source

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
      { simv only [*, interior_interior, hu.interior_eq] with mfld_simps } }
  end,
  right_invariance := begin
    intros s x f e' he'G he'x h hx,
    have hxs : x ∈ s := by simpa only [e'.left_inv he'x] with mfld_simps using hx,
    rcases h hxs with ⟨e, heG, hef, hex⟩,
    refine ⟨e'.symm.trans e, G.trans (G.symm he'G) heG, _, _⟩,
    { intros y hy,
      simv only with mfld_simps at hy,
      simv only [hef ⟨hy.1, hy.2.2⟩] with mfld_simps },
    { simv only [hex, he'x] with mfld_simps }
  end,
  congr_of_forall := begin
    intros s x f g hfgs hfg' h hx,
    rcases h hx with ⟨e, heG, hef, hex⟩,
    refine ⟨e, heG, _, hex⟩,
    intros y hy,
    rw [← hef hy, hfgs y hy.1]
  end,
  left_invariance' := begin
    intros s x f e' he'G he' hfx h hx,
    rcases h hx with ⟨e, heG, hef, hex⟩,
    refine ⟨e.trans e', G.trans heG he'G, _, _⟩,
    { intros y hy,
      simv only with mfld_simps at hy,
      simv only [hef ⟨hy.1, hy.2.1⟩] with mfld_simps },
    { simpa only [hex, hef ⟨hx, hex⟩] with mfld_simps using hfx }
  end }

end local_structomorph

end structure_groupoid
