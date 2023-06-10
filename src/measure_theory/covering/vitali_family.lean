/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.measure.measure_space

/-!
# Vitali families

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

On a metric space `X` with a measure `μ`, consider for each `x : X` a family of measurable sets with
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
open_locale filter measure_theory topology

variables {α : Type*} [metric_space α]

/-- On a metric space `X` with a measure `μ`, consider for each `x : X` a family of measurable sets
with nonempty interiors, called `sets_at x`. This family is a Vitali family if it satisfies the
following property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `sets_at x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.
-/
@[nolint has_nonempty_instance]
structure vitali_family {m : measurable_space α} (μ : measure α) :=
(sets_at : Π (x : α), set (set α))
(measurable_set' : ∀ (x : α), ∀ (a : set α), a ∈ sets_at x → measurable_set a)
(nonempty_interior : ∀ (x : α), ∀ (y : set α), y ∈ sets_at x → (interior y).nonempty)
(nontrivial : ∀ (x : α) (ε > (0 : ℝ)), ∃ y ∈ sets_at x, y ⊆ closed_ball x ε)
(covering : ∀ (s : set α) (f : Π (x : α), set (set α)), (∀ x ∈ s, f x ⊆ sets_at x) →
  (∀ (x ∈ s) (ε > (0 : ℝ)), ∃ a ∈ f x, a ⊆ closed_ball x ε) → ∃ (t : set (α × set α)),
    (∀ (p : α × set α), p ∈ t → p.1 ∈ s) ∧ t.pairwise_disjoint (λ p, p.2) ∧
    (∀ (p : α × set α), p ∈ t → p.2 ∈ f p.1) ∧ μ (s \ ⋃ (p : α × set α) (hp : p ∈ t), p.2) = 0)

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
    rcases v.covering s f h h' with ⟨t, ts, disj, mem_f, hμ⟩,
    exact ⟨t, ts, disj, mem_f, hν hμ⟩
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
  ∃ (t : set (α × set α)), (∀ (p : α × set α), p ∈ t → p.1 ∈ s) ∧
  t.pairwise_disjoint (λ p, p.2) ∧
  (∀ (p : α × set α), p ∈ t → p.2 ∈ v.sets_at p.1 ∩ f p.1)
  ∧ μ (s \ ⋃ (p : α × set α) (hp : p ∈ t), p.2) = 0 :=
v.covering s (λ x, v.sets_at x ∩ f x) (λ x hx, inter_subset_left _ _) h

/-- Given `h : v.fine_subfamily_on f s`, then `h.index` is a set parametrizing a disjoint
covering of almost every `s`. -/
protected def index : set (α × set α) :=
h.exists_disjoint_covering_ae.some

/-- Given `h : v.fine_subfamily_on f s`, then `h.covering p` is a set in the family,
for `p ∈ h.index`, such that these sets form a disjoint covering of almost every `s`. -/
@[nolint unused_arguments] protected def covering : α × set α → set α :=
λ p, p.2

lemma index_subset : ∀ (p : α × set α), p ∈ h.index → p.1 ∈ s :=
h.exists_disjoint_covering_ae.some_spec.1

lemma covering_disjoint : h.index.pairwise_disjoint h.covering :=
h.exists_disjoint_covering_ae.some_spec.2.1

lemma covering_disjoint_subtype : pairwise (disjoint on (λ x : h.index, h.covering x)) :=
(pairwise_subtype_iff_pairwise_set _ _).2 h.covering_disjoint

lemma covering_mem {p : α × set α} (hp : p ∈ h.index) : h.covering p ∈ f p.1 :=
(h.exists_disjoint_covering_ae.some_spec.2.2.1 p hp).2

lemma covering_mem_family {p : α × set α} (hp : p ∈ h.index) : h.covering p ∈ v.sets_at p.1 :=
(h.exists_disjoint_covering_ae.some_spec.2.2.1 p hp).1

lemma measure_diff_bUnion : μ (s \ ⋃ p ∈ h.index, h.covering p) = 0 :=
h.exists_disjoint_covering_ae.some_spec.2.2.2

lemma index_countable [second_countable_topology α] : h.index.countable :=
h.covering_disjoint.countable_of_nonempty_interior
  (λ x hx, v.nonempty_interior _ _ (h.covering_mem_family hx))

protected lemma measurable_set_u {p : α × set α} (hp : p ∈ h.index) :
  measurable_set (h.covering p) :=
v.measurable_set' p.1 _ (h.covering_mem_family hp)

lemma measure_le_tsum_of_absolutely_continuous [second_countable_topology α]
  {ρ : measure α} (hρ : ρ ≪ μ) :
  ρ s ≤ ∑' (p : h.index), ρ (h.covering p) :=
calc ρ s ≤ ρ ((s \ ⋃ (p ∈ h.index), h.covering p) ∪ (⋃ (p ∈ h.index), h.covering p)) :
    measure_mono (by simp only [subset_union_left, diff_union_self])
  ... ≤ ρ (s \ ⋃ (p ∈ h.index), h.covering p) + ρ (⋃ (p ∈ h.index), h.covering p) :
    measure_union_le _ _
  ... = ∑' (p : h.index), ρ (h.covering p) : by rw [hρ h.measure_diff_bUnion,
    measure_bUnion h.index_countable h.covering_disjoint (λ x hx, h.measurable_set_u hx),
    zero_add]

lemma measure_le_tsum [second_countable_topology α] :
  μ s ≤ ∑' (x : h.index), μ (h.covering x) :=
h.measure_le_tsum_of_absolutely_continuous measure.absolutely_continuous.rfl

end fine_subfamily_on

/-- One can enlarge a Vitali family by adding to the sets `f x` at `x` all sets which are not
contained in a `δ`-neighborhood on `x`. This does not change the local filter at a point, but it
can be convenient to get a nicer global behavior. -/
def enlarge (v : vitali_family μ) (δ : ℝ) (δpos : 0 < δ) : vitali_family μ :=
{ sets_at := λ x, v.sets_at x ∪
                {a | measurable_set a ∧ (interior a).nonempty ∧ ¬(a ⊆ closed_ball x δ)},
  measurable_set' := λ x a ha, by { cases ha, exacts [v.measurable_set' _ _ ha, ha.1] },
  nonempty_interior := λ x a ha, by { cases ha, exacts [v.nonempty_interior _ _ ha, ha.2.1] },
  nontrivial := begin
    assume x ε εpos,
    rcases v.nontrivial x ε εpos with ⟨a, ha, h'a⟩,
    exact ⟨a, mem_union_left _ ha, h'a⟩,
  end,
  covering := begin
    assume s f fset ffine,
    let g : α → set (set α) := λ x, f x ∩ v.sets_at x,
    have : ∀ x ∈ s, ∀ (ε : ℝ), ε > 0 → (∃ (a : set α) (H : a ∈ g x), a ⊆ closed_ball x ε),
    { assume x hx ε εpos,
      obtain ⟨a, af, ha⟩ : ∃ a ∈ f x, a ⊆ closed_ball x (min ε δ),
        from ffine x hx (min ε δ) (lt_min εpos δpos),
      rcases fset x hx af with h'a|h'a,
      { exact ⟨a, ⟨af, h'a⟩, ha.trans (closed_ball_subset_closed_ball (min_le_left _ _))⟩ },
      { refine false.elim (h'a.2.2 _),
        exact ha.trans (closed_ball_subset_closed_ball (min_le_right _ _)) } },
    rcases v.covering s g (λ x hx, inter_subset_right _ _) this with ⟨t, ts, tdisj, tg, μt⟩,
    exact ⟨t, ts, tdisj, λ p hp, (tg p hp).1, μt⟩,
  end }

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
  { simp only [subset_def, and_imp, exists_prop, mem_sep_iff, mem_Ioi, mem_principal] },
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
    mem_empty_iff_false, and_true, gt_iff_lt, not_and, ne.def, not_false_iff, not_forall],
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

lemma eventually_filter_at_subset_closed_ball (x : α) {ε : ℝ} (hε : 0 < ε) :
  ∀ᶠ (a : set α) in v.filter_at x, a ⊆ closed_ball x ε :=
begin
  simp only [v.eventually_filter_at_iff],
  exact ⟨ε, hε, λ a ha ha', ha'⟩,
end

lemma tendsto_filter_at_iff {ι : Type*} {l : filter ι} {f : ι → set α} {x : α} :
  tendsto f l (v.filter_at x) ↔
  (∀ᶠ i in l, f i ∈ v.sets_at x) ∧ (∀ (ε > (0 : ℝ)), ∀ᶠ i in l, f i ⊆ closed_ball x ε) :=
begin
  refine ⟨λ H,
    ⟨H.eventually $ v.eventually_filter_at_mem_sets x,
     λ ε hε, H.eventually $ v.eventually_filter_at_subset_closed_ball x hε⟩,
    λ H s hs, (_ : ∀ᶠ i in l, f i ∈ s)⟩,
  obtain ⟨ε, εpos, hε⟩ := v.mem_filter_at_iff.mp hs,
  filter_upwards [H.1, H.2 ε εpos] with i hi hiε using hε _ hi hiε,
end

lemma eventually_filter_at_measurable_set (x : α) :
  ∀ᶠ a in v.filter_at x, measurable_set a :=
by { filter_upwards [v.eventually_filter_at_mem_sets x] with _ ha using v.measurable_set' _ _ ha }

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
