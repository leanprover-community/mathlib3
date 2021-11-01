/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.measure.measure_space

/-!
# Vitali families

On a metric space with a measure `μ`, consider for each `x` a family of measurable sets with
nonempty interiors, called `sets_at x`. This family is a Vitali family if it satisfies the following
property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `sets_at x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.

This file gives the basic definition of Vitali families. More interesting developments of this
notion are deferred to other files:
* constructions of specific Vitali families are provided by the Besicovitch covering theorem, in
`besicovitch.vitali_family`, and by the Vitali covering theorem, in `vitali.vitali_family`.
* The main theorem on differentiation of measures along a Vitali family is proved in
`vitali_family.ae_tendsto_rn_deriv`.

## Main definitions

* `vitali_family μ` is a structure made, for each `x : X`, of a family of sets around `x`, such that
one can extract an almost everywhere disjoint covering from any subfamily containing sets of
arbitrarily small diameters.

Let `v` be such a Vitali family.
* `v.fine_subfamily_on` describes the subfamilies of `v` from which one can extract almost
everywhere disjoint coverings. This property, called
`v.fine_subfamily_on.exists_disjoint_covering_ae`, is essentially a restatement of the definition
of a Vitali family. We also provide an API to use efficiently such a disjoint covering.
* `v.filter_at x` is a filter on sets of `X`, such that convergence with respect to this filter
means convergence when sets in the Vitali family shrink towards `x`.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.8][Federer1996] (Vitali families are called
Vitali relations there)
-/

open measure_theory metric set filter topological_space measure_theory.measure
open_locale filter measure_theory topological_space

variables {α : Type*} [metric_space α]

/-- On a metric space with a measure `μ`, consider for each `x` a family of measurable sets with
nonempty interiors, called `sets_at x`. This family is a Vitali family if it satisfies the following
property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `sets_at x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.
-/
@[nolint has_inhabited_instance]
structure vitali_family {m : measurable_space α} (μ : measure α) :=
(sets_at : Π (x : α), set (set α))
(measurable_set' : ∀ (x : α), ∀ (a : set α), a ∈ sets_at x → measurable_set a)
(nonempty_interior : ∀ (x : α), ∀ (y : set α), y ∈ sets_at x → (interior y).nonempty)
(nontrivial : ∀ (x : α) (ε > (0 : ℝ)), ∃ y ∈ sets_at x, y ⊆ closed_ball x ε)
(covering : ∀ (s : set α) (f : Π (x : α), set (set α)), (∀ x ∈ s, f x ⊆ sets_at x) →
  (∀ (x ∈ s) (ε > (0 : ℝ)), ∃ a ∈ f x, a ⊆ closed_ball x ε) →
  ∃ (t : set α) (u : α → set α), t ⊆ s ∧ t.pairwise (disjoint on u) ∧ (∀ x ∈ t, u x ∈ f x)
  ∧ μ (s \ ⋃ x ∈ t, u x) = 0)

namespace vitali_family

variables {m0 : measurable_space α} {μ : measure α}
include μ

/-- A Vitali family for a measure `μ` is also a Vitali family for any measure absolutely continuous
with respect to `μ`. -/
def mono (v : vitali_family μ) (ν : measure α) (hν : ν ≪ μ) :
  vitali_family ν :=
{ sets_at := v.sets_at,
  measurable_set' := v.measurable_set',
  nonempty_interior := v.nonempty_interior,
  nontrivial := v.nontrivial,
  covering := λ s f h h', begin
    rcases v.covering s f h h' with ⟨t, u, ts, u_disj, uf, μu⟩,
    exact ⟨t, u, ts, u_disj, uf, hν μu⟩
  end }

/-- Given a Vitali family `v` for a measure `μ`, a family `f` is a fine subfamily on a set `s` if
every point `x` in `s` belongs to arbitrarily small sets in `v.sets_at x ∩ f x`. This is precisely
the subfamilies for which the Vitali family definition ensures that one can extract a disjoint
covering of almost all `s`. -/
def fine_subfamily_on (v : vitali_family μ) (f : α → set (set α)) (s : set α) : Prop :=
∀ x ∈ s, ∀ (ε > 0), ∃ a ∈ v.sets_at x ∩ f x, a ⊆ closed_ball x ε

namespace fine_subfamily_on

variables {v : vitali_family μ} {f : α → set (set α)} {s : set α} (h : v.fine_subfamily_on f s)
include h

theorem exists_disjoint_covering_ae :
  ∃ (t : set α) (u : α → set α), t ⊆ s ∧ t.pairwise (disjoint on u) ∧
    (∀ x ∈ t, u x ∈ v.sets_at x ∩ f x) ∧ μ (s \ ⋃ x ∈ t, u x) = 0 :=
v.covering s (λ x, v.sets_at x ∩ f x) (λ x hx, inter_subset_left _ _) h

/-- Given `h : v.fine_subfamily_on f s`, then `h.t` is a subset of `s` parametrizing a disjoint
covering of almost every `s`. -/
protected def t : set α :=
h.exists_disjoint_covering_ae.some

/-- Given `h : v.fine_subfamily_on f s`, then `h.u x` is a set in the family, for `x ∈ h.t`, such
that these sets form a disjoint covering of almost every `s`. -/
protected def u : α → set α :=
h.exists_disjoint_covering_ae.some_spec.some

lemma t_subset_s : h.t ⊆ s :=
h.exists_disjoint_covering_ae.some_spec.some_spec.1

lemma u_disjoint : h.t.pairwise (disjoint on h.u) :=
h.exists_disjoint_covering_ae.some_spec.some_spec.2.1

lemma u_disjoint_subtype : pairwise (disjoint on (λ x : h.t, h.u x)) :=
(pairwise_subtype_iff_pairwise_set _ _).2 h.u_disjoint

lemma u_mem_f {x : α} (hx : x ∈ h.t) : h.u x ∈ f x :=
(h.exists_disjoint_covering_ae.some_spec.some_spec.2.2.1 x hx).2

lemma u_mem_v {x : α} (hx : x ∈ h.t) : h.u x ∈ v.sets_at x :=
(h.exists_disjoint_covering_ae.some_spec.some_spec.2.2.1 x hx).1

lemma measure_diff_bUnion : μ (s \ ⋃ x ∈ h.t, h.u x) = 0 :=
h.exists_disjoint_covering_ae.some_spec.some_spec.2.2.2

lemma t_countable [second_countable_topology α] : countable h.t :=
countable_of_nonempty_interior_of_disjoint h.u (λ x hx, v.nonempty_interior _ _ (h.u_mem_v hx))
  h.u_disjoint

protected lemma measurable_set_u {x : α} (hx : x ∈ h.t) : _root_.measurable_set (h.u x) :=
v.measurable_set' x _ (h.u_mem_v hx)

lemma measure_le_tsum_of_absolutely_continuous [second_countable_topology α]
  {ρ : measure α} (hρ : ρ ≪ μ) :
  ρ s ≤ ∑' (x : h.t), ρ (h.u x) :=
calc ρ s ≤ ρ ((s \ ⋃ (x ∈ h.t), h.u x) ∪ (⋃ (x ∈ h.t), h.u x)) :
    measure_mono (by simp only [subset_union_left, diff_union_self])
  ... ≤ ρ (s \ ⋃ (x ∈ h.t), h.u x) + ρ (⋃ (x ∈ h.t), h.u x) : measure_union_le _ _
  ... = ∑' (x : h.t), ρ (h.u x) : by rw [hρ h.measure_diff_bUnion,
    measure_bUnion h.t_countable h.u_disjoint (λ x hx, h.measurable_set_u hx), zero_add]

lemma measure_le_tsum [second_countable_topology α] :
  μ s ≤ ∑' (x : h.t), μ (h.u x) :=
h.measure_le_tsum_of_absolutely_continuous measure.absolutely_continuous.rfl

end fine_subfamily_on

variable (v : vitali_family μ)
include v

/-- Given a vitali family `v`, then `v.filter_at x` is the filter on `set α` made of those families
that contain all sets of `v.sets_at x` of a sufficiently small diameter. This filter makes it
possible to express limiting behavior when sets in `v.sets_at x` shrink to `x`. -/
def filter_at (x : α) : filter (set α) :=
⨅ (ε ∈ Ioi (0 : ℝ)), 𝓟 {a ∈ v.sets_at x | a ⊆ closed_ball x ε}

lemma mem_filter_at_iff {x : α} {s : set (set α)} :
  (s ∈ v.filter_at x) ↔ ∃ (ε > (0 : ℝ)), ∀ a ∈ v.sets_at x, a ⊆ closed_ball x ε → a ∈ s :=
begin
  simp only [filter_at, exists_prop, gt_iff_lt],
  rw mem_binfi_of_directed,
  { simp only [subset_def, and_imp, exists_prop, mem_sep_eq, mem_Ioi, mem_principal] },
  { simp only [directed_on, exists_prop, ge_iff_le, le_principal_iff, mem_Ioi, order.preimage,
      mem_principal],
    assume x hx y hy,
    refine ⟨min x y, lt_min hx hy,
      λ a ha, ⟨ha.1, ha.2.trans (closed_ball_subset_closed_ball (min_le_left _ _))⟩,
      λ a ha, ⟨ha.1, ha.2.trans (closed_ball_subset_closed_ball (min_le_right _ _))⟩⟩ },
  { exact ⟨(1 : ℝ), mem_Ioi.2 zero_lt_one⟩ }
end

instance filter_at_ne_bot (x : α) : (v.filter_at x).ne_bot :=
begin
  simp only [ne_bot_iff, ←empty_mem_iff_bot, mem_filter_at_iff, not_exists, exists_prop,
    mem_empty_eq, and_true, gt_iff_lt, not_and, ne.def, not_false_iff, not_forall],
  assume ε εpos,
  obtain ⟨w, w_sets, hw⟩ : ∃ (w ∈ v.sets_at x), w ⊆ closed_ball x ε := v.nontrivial x ε εpos,
  exact ⟨w, w_sets, hw⟩
end

lemma eventually_filter_at_iff {x : α} {P : set α → Prop} :
  (∀ᶠ a in v.filter_at x, P a) ↔ ∃ (ε > (0 : ℝ)), ∀ a ∈ v.sets_at x, a ⊆ closed_ball x ε → P a :=
v.mem_filter_at_iff

lemma eventually_filter_at_mem_sets (x : α) :
  ∀ᶠ a in v.filter_at x, a ∈ v.sets_at x :=
begin
  simp only [eventually_filter_at_iff, exists_prop, and_true, gt_iff_lt,
             implies_true_iff] {contextual := tt},
  exact ⟨1, zero_lt_one⟩
end

lemma frequently_filter_at_iff {x : α} {P : set α → Prop} :
  (∃ᶠ a in v.filter_at x, P a) ↔ ∀ (ε > (0 : ℝ)), ∃ a ∈ v.sets_at x, a ⊆ closed_ball x ε ∧ P a :=
by simp only [filter.frequently, eventually_filter_at_iff, not_exists, exists_prop, not_and,
  not_not, not_forall]

lemma eventually_filter_at_subset_of_nhds {x : α} {o : set α} (hx : o ∈ 𝓝 x) :
  ∀ᶠ a in v.filter_at x, a ⊆ o :=
begin
  rw eventually_filter_at_iff,
  rcases metric.mem_nhds_iff.1 hx with ⟨ε, εpos, hε⟩,
  exact ⟨ε/2, half_pos εpos,
    λ a av ha, ha.trans ((closed_ball_subset_ball (half_lt_self εpos)).trans hε)⟩
end

lemma fine_subfamily_on_of_frequently (v : vitali_family μ) (f : α → set (set α)) (s : set α)
  (h : ∀ x ∈ s, ∃ᶠ a in v.filter_at x, a ∈ f x) :
  v.fine_subfamily_on f s :=
begin
  assume x hx ε εpos,
  obtain ⟨a, av, ha, af⟩ : ∃ (a : set α) (H : a ∈ v.sets_at x), a ⊆ closed_ball x ε ∧ a ∈ f x :=
    v.frequently_filter_at_iff.1 (h x hx) ε εpos,
  exact ⟨a, ⟨av, af⟩, ha⟩,
end

end vitali_family
