/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import geometry.manifold.charted_space

/-!
# Local properties invariant under a groupoid

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
open_locale classical manifold topology

open set filter topological_space

variables {H M H' M' X : Type*}
variables [topological_space H] [topological_space M] [charted_space H M]
variables [topological_space H'] [topological_space M'] [charted_space H' M']
variables [topological_space X]

namespace structure_groupoid

variables (G : structure_groupoid H) (G' : structure_groupoid H')

/-- Structure recording good behavior of a property of a triple `(f, s, x)` where `f` is a function,
`s` a set and `x` a point. Good behavior here means locality and invariance under given groupoids
(both in the source and in the target). Given such a good behavior, the lift of this property
to charted spaces admitting these groupoids will inherit the good behavior. -/
structure local_invariant_prop (P : (H → H') → (set H) → H → Prop) : Prop :=
(is_local : ∀ {s x u} {f : H → H'}, is_open u → x ∈ u → (P f s x ↔ P f (s ∩ u) x))
(right_invariance' : ∀ {s x f} {e : local_homeomorph H H}, e ∈ G → x ∈ e.source → P f s x →
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

lemma left_invariance {s : set H} {x : H} {f : H → H'} {e' : local_homeomorph H' H'}
  (he' : e' ∈ G') (hfs : continuous_within_at f s x) (hxe' : f x ∈ e'.source) :
  P (e' ∘ f) s x ↔ P f s x :=
begin
  have h2f := hfs.preimage_mem_nhds_within (e'.open_source.mem_nhds hxe'),
  have h3f := (((e'.continuous_at hxe').comp_continuous_within_at hfs).preimage_mem_nhds_within $
    e'.symm.open_source.mem_nhds $ e'.maps_to hxe'),
  split,
  { intro h,
    rw [hG.is_local_nhds h3f] at h,
    have h2 := hG.left_invariance' (G'.symm he') (inter_subset_right _ _)
      (by exact e'.maps_to hxe') h,
    rw [← hG.is_local_nhds h3f] at h2,
    refine hG.congr_nhds_within _ (e'.left_inv hxe') h2,
    exact eventually_of_mem h2f (λ x', e'.left_inv) },
  { simp_rw [hG.is_local_nhds h2f],
    exact hG.left_invariance' he' (inter_subset_right _ _) hxe' }
end

lemma right_invariance {s : set H} {x : H} {f : H → H'} {e : local_homeomorph H H}
  (he : e ∈ G) (hxe : x ∈ e.source) : P (f ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P f s x :=
begin
  refine ⟨λ h, _, hG.right_invariance' he hxe⟩,
  have := hG.right_invariance' (G.symm he) (e.maps_to hxe) h,
  rw [e.symm_symm, e.left_inv hxe] at this,
  refine hG.congr _ ((hG.congr_set _).mp this),
  { refine eventually_of_mem (e.open_source.mem_nhds hxe) (λ x' hx', _),
    simp_rw [function.comp_apply, e.left_inv hx'] },
  { rw [eventually_eq_set],
    refine eventually_of_mem (e.open_source.mem_nhds hxe) (λ x' hx', _),
    simp_rw [mem_preimage, e.left_inv hx'] },
end

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
by simp [lift_prop_on, lift_prop, lift_prop_at]

lemma lift_prop_within_at_self {f : H → H'} {s : set H} {x : H} :
  lift_prop_within_at P f s x ↔ continuous_within_at f s x ∧ P f s x :=
iff.rfl

lemma lift_prop_within_at_self_source {f : H → M'} {s : set H} {x : H} :
  lift_prop_within_at P f s x ↔ continuous_within_at f s x ∧ P (chart_at H' (f x) ∘ f) s x :=
iff.rfl

lemma lift_prop_within_at_self_target {f : M → H'} :
  lift_prop_within_at P f s x ↔
    continuous_within_at f s x ∧
    P (f ∘ (chart_at H x).symm) ((chart_at H x).symm ⁻¹' s) (chart_at H x x) :=
iff.rfl

namespace local_invariant_prop

variable (hG : G.local_invariant_prop G' P)
include hG

/-- `lift_prop_within_at P f s x` is equivalent to a definition where we restrict the set we are
  considering to the domain of the charts at `x` and `f x`. -/
lemma lift_prop_within_at_iff {f : M → M'} :
  lift_prop_within_at P f s x ↔
  continuous_within_at f s x ∧ P ((chart_at H' (f x)) ∘ f ∘ (chart_at H x).symm)
  ((chart_at H x).target ∩ (chart_at H x).symm ⁻¹' (s ∩ f ⁻¹' (chart_at H' (f x)).source))
  (chart_at H x x) :=
begin
  refine and_congr_right (λ hf, hG.congr_set _),
  exact local_homeomorph.preimage_eventually_eq_target_inter_preimage_inter hf
    (mem_chart_source H x) (chart_source_mem_nhds H' (f x))
end

lemma lift_prop_within_at_indep_chart_source_aux (g : M → H')
  (he : e ∈ G.maximal_atlas M) (xe : x ∈ e.source)
  (he' : e' ∈ G.maximal_atlas M) (xe' : x ∈ e'.source) :
  P (g ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P (g ∘ e'.symm) (e'.symm ⁻¹' s) (e' x) :=
begin
  rw [← hG.right_invariance (compatible_of_mem_maximal_atlas he he')],
  swap, { simp only [xe, xe'] with mfld_simps },
  simp_rw [local_homeomorph.trans_apply, e.left_inv xe],
  rw [hG.congr_iff],
  { refine hG.congr_set _,
    refine (eventually_of_mem _ $ λ y (hy : y ∈ e'.symm ⁻¹' e.source), _).set_eq,
    { refine (e'.symm.continuous_at $ e'.maps_to xe').preimage_mem_nhds (e.open_source.mem_nhds _),
      simp_rw [e'.left_inv xe', xe] },
    simp_rw [mem_preimage, local_homeomorph.coe_trans_symm, local_homeomorph.symm_symm,
      function.comp_apply, e.left_inv hy] },
  { refine ((e'.eventually_nhds' _ xe').mpr $ e.eventually_left_inverse xe).mono (λ y hy, _),
    simp only with mfld_simps,
    rw [hy] },
end

lemma lift_prop_within_at_indep_chart_target_aux2 (g : H → M') {x : H} {s : set H}
  (hf : f ∈ G'.maximal_atlas M') (xf : g x ∈ f.source)
  (hf' : f' ∈ G'.maximal_atlas M') (xf' : g x ∈ f'.source)
  (hgs : continuous_within_at g s x) :
  P (f ∘ g) s x ↔ P (f' ∘ g) s x :=
begin
  have hcont : continuous_within_at (f ∘ g) s x :=
    (f.continuous_at xf).comp_continuous_within_at hgs,
  rw [← hG.left_invariance (compatible_of_mem_maximal_atlas hf hf') hcont
      (by simp only [xf, xf'] with mfld_simps)],
  refine hG.congr_iff_nhds_within _ (by simp only [xf] with mfld_simps),
  exact (hgs.eventually $ f.eventually_left_inverse xf).mono (λ y, congr_arg f')
end

lemma lift_prop_within_at_indep_chart_target_aux {g : X → M'} {e : local_homeomorph X H} {x : X}
  {s : set X} (xe : x ∈ e.source)
  (hf : f ∈ G'.maximal_atlas M') (xf : g x ∈ f.source)
  (hf' : f' ∈ G'.maximal_atlas M') (xf' : g x ∈ f'.source)
  (hgs : continuous_within_at g s x) :
  P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P (f' ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) :=
begin
  rw [← e.left_inv xe] at xf xf' hgs,
  refine hG.lift_prop_within_at_indep_chart_target_aux2 (g ∘ e.symm) hf xf hf' xf' _,
  exact hgs.comp (e.symm.continuous_at $ e.maps_to xe).continuous_within_at subset.rfl
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
  (hgs : continuous_within_at g s x) :
  P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P (f' ∘ g ∘ e'.symm) (e'.symm ⁻¹' s) (e' x) :=
by rw [hG.lift_prop_within_at_indep_chart_source_aux (f ∘ g) he xe he' xe',
    hG.lift_prop_within_at_indep_chart_target_aux xe' hf xf hf' xf' hgs]

lemma lift_prop_within_at_indep_chart [has_groupoid M G] [has_groupoid M' G']
  (he : e ∈ G.maximal_atlas M) (xe : x ∈ e.source)
  (hf : f ∈ G'.maximal_atlas M') (xf : g x ∈ f.source) :
  lift_prop_within_at P g s x ↔
    continuous_within_at g s x ∧ P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) :=
and_congr_right $ hG.lift_prop_within_at_indep_chart_aux (chart_mem_maximal_atlas _ _)
  (mem_chart_source _ _) he xe (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) hf xf

/-- A version of `lift_prop_within_at_indep_chart`, only for the source. -/
lemma lift_prop_within_at_indep_chart_source [has_groupoid M G]
  (he : e ∈ G.maximal_atlas M) (xe : x ∈ e.source) :
  lift_prop_within_at P g s x ↔ lift_prop_within_at P (g ∘ e.symm) (e.symm ⁻¹' s) (e x) :=
begin
  have := e.symm.continuous_within_at_iff_continuous_within_at_comp_right xe,
  rw [e.symm_symm] at this,
  rw [lift_prop_within_at_self_source, lift_prop_within_at, ← this],
  simp_rw [function.comp_app, e.left_inv xe],
  refine and_congr iff.rfl _,
  rw hG.lift_prop_within_at_indep_chart_source_aux (chart_at H' (g x) ∘ g)
    (chart_mem_maximal_atlas G x) (mem_chart_source H x) he xe,
end

/-- A version of `lift_prop_within_at_indep_chart`, only for the target. -/
lemma lift_prop_within_at_indep_chart_target [has_groupoid M' G']
  (hf : f ∈ G'.maximal_atlas M') (xf : g x ∈ f.source) :
  lift_prop_within_at P g s x ↔ continuous_within_at g s x ∧ lift_prop_within_at P (f ∘ g) s x :=
begin
  rw [lift_prop_within_at_self_target, lift_prop_within_at, and.congr_right_iff],
  intro hg,
  simp_rw [(f.continuous_at xf).comp_continuous_within_at hg, true_and],
  exact hG.lift_prop_within_at_indep_chart_target_aux (mem_chart_source _ _)
    (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) hf xf hg
end

/-- A version of `lift_prop_within_at_indep_chart`, that uses `lift_prop_within_at` on both sides.
-/
lemma lift_prop_within_at_indep_chart' [has_groupoid M G] [has_groupoid M' G']
  (he : e ∈ G.maximal_atlas M) (xe : x ∈ e.source)
  (hf : f ∈ G'.maximal_atlas M') (xf : g x ∈ f.source) :
  lift_prop_within_at P g s x ↔
    continuous_within_at g s x ∧ lift_prop_within_at P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) :=
begin
  rw [hG.lift_prop_within_at_indep_chart he xe hf xf, lift_prop_within_at_self, and.left_comm,
    iff.comm, and_iff_right_iff_imp],
  intro h,
  have h1 := (e.symm.continuous_within_at_iff_continuous_within_at_comp_right xe).mp h.1,
  have : continuous_at f ((g ∘ e.symm) (e x)),
  { simp_rw [function.comp, e.left_inv xe, f.continuous_at xf] },
  exact this.comp_continuous_within_at h1,
end

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
by rwa [← univ_inter s, hG.lift_prop_within_at_inter hs] at h

lemma lift_prop_within_at_of_lift_prop_at_of_mem_nhds (h : lift_prop_at P g x) (hs : s ∈ 𝓝 x) :
  lift_prop_within_at P g s x :=
by rwa [← univ_inter s, hG.lift_prop_within_at_inter hs]

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
  simp [h x],
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

lemma lift_prop_within_at_mono_of_mem
  (mono_of_mem : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, s ∈ 𝓝[t] x → P f s x → P f t x)
  (h : lift_prop_within_at P g s x) (hst : s ∈ 𝓝[t] x) :
  lift_prop_within_at P g t x :=
begin
  refine ⟨h.1.mono_of_mem hst, mono_of_mem _ h.2⟩,
  simp_rw [← mem_map, (chart_at H x).symm.map_nhds_within_preimage_eq (mem_chart_target H x),
    (chart_at H x).left_inv (mem_chart_source H x), hst]
end

lemma lift_prop_within_at_mono
  (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
  (h : lift_prop_within_at P g s x) (hts : t ⊆ s) :
  lift_prop_within_at P g t x :=
begin
  refine ⟨h.1.mono hts, _⟩,
  apply mono (λ y hy, _) h.2,
  simp only with mfld_simps at hy,
  simp only [hy, hts _] with mfld_simps,
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
    have : e.symm x ∈ e.source, by simp only [hx] with mfld_simps,
    rw [lift_prop_at,
      hG.lift_prop_within_at_indep_chart G.id_mem_maximal_atlas (mem_univ _) he this],
    refine ⟨(e.symm.continuous_at hx).continuous_within_at, _⟩,
    simp only [h] with mfld_simps },
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
hG.lift_prop_at_symm_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x) (by simp)

lemma lift_prop_on_chart_symm [has_groupoid M G]
  (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) :
  lift_prop_on Q (chart_at H x).symm (chart_at H x).target :=
hG.lift_prop_on_symm_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x)

lemma lift_prop_at_of_mem_groupoid (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y)
  {f : local_homeomorph H H} (hf : f ∈ G) {x : H} (hx : x ∈ f.source) :
  lift_prop_at Q f x :=
lift_prop_at_of_mem_maximal_atlas hG hQ (G.mem_maximal_atlas_of_mem_groupoid hf) hx

lemma lift_prop_on_of_mem_groupoid (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y)
  {f : local_homeomorph H H} (hf : f ∈ G) :
  lift_prop_on Q f f.source :=
lift_prop_on_of_mem_maximal_atlas hG hQ (G.mem_maximal_atlas_of_mem_groupoid hf)

lemma lift_prop_id (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) :
  lift_prop Q (id : M → M) :=
begin
  simp_rw [lift_prop_iff, continuous_id, true_and],
  exact λ x, hG.congr' ((chart_at H x).eventually_right_inverse $ mem_chart_target H x) (hQ _)
end

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
      { simp only [*, interior_interior, hu.interior_eq] with mfld_simps } }
  end,
  right_invariance' := begin
    intros s x f e' he'G he'x h hx,
    have hxs : x ∈ s := by simpa only [e'.left_inv he'x] with mfld_simps using hx,
    rcases h hxs with ⟨e, heG, hef, hex⟩,
    refine ⟨e'.symm.trans e, G.trans (G.symm he'G) heG, _, _⟩,
    { intros y hy,
      simp only with mfld_simps at hy,
      simp only [hef ⟨hy.1, hy.2.2⟩] with mfld_simps },
    { simp only [hex, he'x] with mfld_simps }
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
      simp only with mfld_simps at hy,
      simp only [hef ⟨hy.1, hy.2.1⟩] with mfld_simps },
    { simpa only [hex, hef ⟨hx, hex⟩] with mfld_simps using hfx }
  end }

/-- A slight reformulation of `is_local_structomorph_within_at` when `f` is a local homeomorph.
  This gives us an `e` that is defined on a subset of `f.source`. -/
lemma _root_.local_homeomorph.is_local_structomorph_within_at_iff {G : structure_groupoid H}
  [closed_under_restriction G]
  (f : local_homeomorph H H) {s : set H} {x : H} (hx : x ∈ f.source ∪ sᶜ) :
  G.is_local_structomorph_within_at ⇑f s x ↔
  x ∈ s → ∃ (e : local_homeomorph H H), e ∈ G ∧ e.source ⊆ f.source ∧
  eq_on f ⇑e (s ∩ e.source) ∧ x ∈ e.source :=
begin
  split,
  { intros hf h2x,
    obtain ⟨e, he, hfe, hxe⟩ := hf h2x,
    refine ⟨e.restr f.source, closed_under_restriction' he f.open_source, _, _, hxe, _⟩,
    { simp_rw [local_homeomorph.restr_source],
      refine (inter_subset_right _ _).trans interior_subset },
    { intros x' hx', exact hfe ⟨hx'.1, hx'.2.1⟩ },
    { rw [f.open_source.interior_eq], exact or.resolve_right hx (not_not.mpr h2x) } },
  { intros hf hx, obtain ⟨e, he, h2e, hfe, hxe⟩ := hf hx, exact ⟨e, he, hfe, hxe⟩ }
end

/-- A slight reformulation of `is_local_structomorph_within_at` when `f` is a local homeomorph and
  the set we're considering is a superset of `f.source`. -/
lemma _root_.local_homeomorph.is_local_structomorph_within_at_iff' {G : structure_groupoid H}
  [closed_under_restriction G]
  (f : local_homeomorph H H) {s : set H} {x : H} (hs : f.source ⊆ s) (hx : x ∈ f.source ∪ sᶜ) :
  G.is_local_structomorph_within_at ⇑f s x ↔
  x ∈ s → ∃ (e : local_homeomorph H H), e ∈ G ∧ e.source ⊆ f.source ∧
  eq_on f ⇑e e.source ∧ x ∈ e.source :=
begin
  simp_rw [f.is_local_structomorph_within_at_iff hx],
  refine imp_congr_right (λ hx, exists_congr $ λ e, and_congr_right $ λ he, _),
  refine and_congr_right (λ h2e, _),
  rw [inter_eq_right_iff_subset.mpr (h2e.trans hs)],
end

/-- A slight reformulation of `is_local_structomorph_within_at` when `f` is a local homeomorph and
  the set we're considering is `f.source`. -/
lemma _root_.local_homeomorph.is_local_structomorph_within_at_source_iff {G : structure_groupoid H}
  [closed_under_restriction G]
  (f : local_homeomorph H H) {x : H} :
  G.is_local_structomorph_within_at ⇑f f.source x ↔
  x ∈ f.source → ∃ (e : local_homeomorph H H), e ∈ G ∧ e.source ⊆ f.source ∧
  eq_on f ⇑e e.source ∧ x ∈ e.source :=
begin
  have : x ∈ f.source ∪ f.sourceᶜ, { simp_rw [union_compl_self] },
  exact f.is_local_structomorph_within_at_iff' subset.rfl this,
end

variables {H₁ : Type*} [topological_space H₁] {H₂ : Type*} [topological_space H₂]
   {H₃ : Type*} [topological_space H₃] [charted_space H₁ H₂] [charted_space H₂ H₃]
   {G₁ : structure_groupoid H₁} [has_groupoid H₂ G₁] [closed_under_restriction G₁]
   (G₂ : structure_groupoid H₂) [has_groupoid H₃ G₂]

variables (G₂)
lemma has_groupoid.comp
  (H : ∀ e ∈ G₂, lift_prop_on (is_local_structomorph_within_at G₁) (e : H₂ → H₂) e.source) :
  @has_groupoid H₁ _ H₃ _ (charted_space.comp H₁ H₂ H₃) G₁ :=
{ compatible := begin
    rintros _ _ ⟨e, f, he, hf, rfl⟩ ⟨e', f', he', hf', rfl⟩,
    apply G₁.locality,
    intros x hx,
    simp only with mfld_simps at hx,
    have hxs : x ∈ f.symm ⁻¹' (e.symm ≫ₕ e').source,
    { simp only [hx] with mfld_simps },
    have hxs' : x ∈ f.target ∩ (f.symm) ⁻¹' ((e.symm ≫ₕ e').source ∩ (e.symm ≫ₕ e') ⁻¹' f'.source),
    { simp only [hx] with mfld_simps },
    obtain ⟨φ, hφG₁, hφ, hφ_dom⟩ := local_invariant_prop.lift_prop_on_indep_chart
      (is_local_structomorph_within_at_local_invariant_prop G₁) (G₁.subset_maximal_atlas hf)
      (G₁.subset_maximal_atlas hf') (H _ (G₂.compatible he he')) hxs' hxs,
    simp_rw [← local_homeomorph.coe_trans, local_homeomorph.trans_assoc] at hφ,
    simp_rw [local_homeomorph.trans_symm_eq_symm_trans_symm, local_homeomorph.trans_assoc],
    have hs : is_open (f.symm ≫ₕ e.symm ≫ₕ e' ≫ₕ f').source :=
      (f.symm ≫ₕ e.symm ≫ₕ e' ≫ₕ f').open_source,
    refine ⟨_, hs.inter φ.open_source, _, _⟩,
    { simp only [hx, hφ_dom] with mfld_simps, },
    { refine G₁.eq_on_source (closed_under_restriction' hφG₁ hs) _,
      rw local_homeomorph.restr_source_inter,
      refine (hφ.mono _).restr_eq_on_source,
      mfld_set_tac },
  end }

end local_structomorph

end structure_groupoid
