/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import measure_theory.outer_measure
import order.filter.countable_Inter
import data.set.accumulate
import measure_theory.measurable_space_0

/-!
# Measure spaces

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the measure of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, a measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

Measures on `α` form a complete lattice, and are closed under scalar multiplication with `ℝ≥0∞`.

We introduce the following typeclasses for measures:

* `probability_measure μ`: `μ univ = 1`;
* `finite_measure μ`: `μ univ < ∞`;
* `sigma_finite μ`: there exists a countable collection of measurable sets that cover `univ`
  where `μ` is finite;
* `locally_finite_measure μ` : `∀ x, ∃ s ∈ 𝓝 x, μ s < ∞`;
* `has_no_atoms μ` : `∀ x, μ {x} = 0`; possibly should be redefined as
  `∀ s, 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s`.

Given a measure, the null sets are the sets where `μ s = 0`, where `μ` denotes the corresponding
outer measure (so `s` might not be measurable). We can then define the completion of `μ` as the
measure on the least `σ`-algebra that also contains all null sets, by defining the measure to be `0`
on the null sets.

## Main statements

* `completion` is the completion of a measure to all null measurable sets.
* `measure.of_measurable` and `outer_measure.to_measure` are two important ways to define a measure.

## Implementation notes

Given `μ : measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

You often don't want to define a measure via its constructor.
Two ways that are sometimes more convenient:
* `measure.of_measurable` is a way to define a measure by only giving its value on measurable sets
  and proving the properties (1) and (2) mentioned above.
* `outer_measure.to_measure` is a way of obtaining a measure from an outer measure by showing that
  all measurable sets in the measurable space are Carathéodory measurable.

To prove that two measures are equal, there are multiple options:
* `ext`: two measures are equal if they are equal on all measurable sets.
* `ext_of_generate_from_of_Union`: two measures are equal if they are equal on a π-system generating
  the measurable sets, if the π-system contains a spanning increasing sequence of sets where the
  measures take finite value (in particular the measures are σ-finite). This is a special case of
  the more general `ext_of_generate_from_of_cover`
* `ext_of_generate_finite`: two finite measures are equal if they are equal on a π-system
  generating the measurable sets. This is a special case of `ext_of_generate_from_of_Union` using
  `C ∪ {univ}`, but is easier to work with.

A `measure_space` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Complete_measure>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space, completion, null set, null measurable set
-/

noncomputable theory

open classical set filter (hiding map) function measurable_space
open_locale classical topological_space big_operators filter ennreal nnreal

variables {α β γ δ ι : Type*}

namespace measure_theory

/-- A measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure. -/
structure measure (α : Type*) [measurable_space α] extends outer_measure α :=
(m_Union ⦃f : ℕ → set α⦄ :
  (∀ i, measurable_set (f i)) → pairwise (disjoint on f) →
  measure_of (⋃ i, f i) = ∑' i, measure_of (f i))
(trimmed : to_outer_measure.trim = to_outer_measure)

/-- Measure projections for a measure space.

For measurable sets this returns the measure assigned by the `measure_of` field in `measure`.
But we can extend this to _all_ sets, but using the outer measure. This gives us monotonicity and
subadditivity for all sets.
-/
instance measure.has_coe_to_fun [measurable_space α] : has_coe_to_fun (measure α) :=
⟨λ _, set α → ℝ≥0∞, λ m, m.to_outer_measure⟩

section

variables [measurable_space α] {μ μ₁ μ₂ : measure α} {s s₁ s₂ t : set α}

namespace measure

/-! ### General facts about measures -/

/-- Obtain a measure by giving a countably additive function that sends `∅` to `0`. -/
def of_measurable (m : Π (s : set α), measurable_set s → ℝ≥0∞)
  (m0 : m ∅ measurable_set.empty = 0)
  (mU : ∀ {{f : ℕ → set α}} (h : ∀ i, measurable_set (f i)), pairwise (disjoint on f) →
    m (⋃ i, f i) (measurable_set.Union h) = ∑' i, m (f i) (h i)) : measure α :=
{ m_Union := λ f hf hd,
  show induced_outer_measure m _ m0 (Union f) =
      ∑' i, induced_outer_measure m _ m0 (f i), begin
    rw [induced_outer_measure_eq m0 mU, mU hf hd],
    congr, funext n, rw induced_outer_measure_eq m0 mU
  end,
  trimmed :=
  show (induced_outer_measure m _ m0).trim = induced_outer_measure m _ m0, begin
    unfold outer_measure.trim,
    congr, funext s hs,
    exact induced_outer_measure_eq m0 mU hs
  end,
  ..induced_outer_measure m _ m0 }

lemma of_measurable_apply {m : Π (s : set α), measurable_set s → ℝ≥0∞}
  {m0 : m ∅ measurable_set.empty = 0}
  {mU : ∀ {{f : ℕ → set α}} (h : ∀ i, measurable_set (f i)), pairwise (disjoint on f) →
    m (⋃ i, f i) (measurable_set.Union h) = ∑' i, m (f i) (h i)}
  (s : set α) (hs : measurable_set s) : of_measurable m m0 mU s = m s hs :=
induced_outer_measure_eq m0 mU hs

lemma to_outer_measure_injective : injective (to_outer_measure : measure α → outer_measure α) :=
λ ⟨m₁, u₁, h₁⟩ ⟨m₂, u₂, h₂⟩ h, by { congr, exact h }

@[ext] lemma ext (h : ∀ s, measurable_set s → μ₁ s = μ₂ s) : μ₁ = μ₂ :=
to_outer_measure_injective $ by rw [← trimmed, outer_measure.trim_congr h, trimmed]

lemma ext_iff : μ₁ = μ₂ ↔ ∀ s, measurable_set s → μ₁ s = μ₂ s :=
⟨by { rintro rfl s hs, refl }, measure.ext⟩

end measure

@[simp] lemma coe_to_outer_measure : ⇑μ.to_outer_measure = μ := rfl

lemma to_outer_measure_apply (s : set α) : μ.to_outer_measure s = μ s := rfl

lemma measure_eq_trim (s : set α) : μ s = μ.to_outer_measure.trim s :=
by rw μ.trimmed; refl

lemma measure_eq_infi (s : set α) : μ s = ⨅ t (st : s ⊆ t) (ht : measurable_set t), μ t :=
by rw [measure_eq_trim, outer_measure.trim_eq_infi]; refl

/-- A variant of `measure_eq_infi` which has a single `infi`. This is useful when applying a
  lemma next that only works for non-empty infima, in which case you can use
  `nonempty_measurable_superset`. -/
lemma measure_eq_infi' (μ : measure α) (s : set α) :
  μ s = ⨅ t : { t // s ⊆ t ∧ measurable_set t}, μ t :=
by simp_rw [infi_subtype, infi_and, subtype.coe_mk, ← measure_eq_infi]

lemma measure_eq_induced_outer_measure :
  μ s = induced_outer_measure (λ s _, μ s) measurable_set.empty μ.empty s :=
measure_eq_trim _

lemma to_outer_measure_eq_induced_outer_measure :
  μ.to_outer_measure = induced_outer_measure (λ s _, μ s) measurable_set.empty μ.empty :=
μ.trimmed.symm

lemma measure_eq_extend (hs : measurable_set s) :
  μ s = extend (λ t (ht : measurable_set t), μ t) s :=
by { rw [measure_eq_induced_outer_measure, induced_outer_measure_eq_extend _ _ hs],
  exact μ.m_Union }

@[simp] lemma measure_empty : μ ∅ = 0 := μ.empty

lemma nonempty_of_measure_ne_zero (h : μ s ≠ 0) : s.nonempty :=
ne_empty_iff_nonempty.1 $ λ h', h $ h'.symm ▸ measure_empty

lemma measure_mono (h : s₁ ⊆ s₂) : μ s₁ ≤ μ s₂ := μ.mono h

lemma measure_mono_null (h : s₁ ⊆ s₂) (h₂ : μ s₂ = 0) : μ s₁ = 0 :=
nonpos_iff_eq_zero.1 $ h₂ ▸ measure_mono h

lemma measure_mono_top (h : s₁ ⊆ s₂) (h₁ : μ s₁ = ∞) : μ s₂ = ∞ :=
top_unique $ h₁ ▸ measure_mono h

/-- For every set there exists a measurable superset of the same measure. -/
lemma exists_measurable_superset (μ : measure α) (s : set α) :
  ∃ t, s ⊆ t ∧ measurable_set t ∧ μ t = μ s :=
by simpa only [← measure_eq_trim] using μ.to_outer_measure.exists_measurable_superset_eq_trim s

/-- For every set `s` and a countable collection of measures `μ i` there exists a measurable
superset `t ⊇ s` such that each measure `μ i` takes the same value on `s` and `t`. -/
lemma exists_measurable_superset_forall_eq {ι} [encodable ι] (μ : ι → measure α) (s : set α) :
  ∃ t, s ⊆ t ∧ measurable_set t ∧ ∀ i, μ i t = μ i s :=
by simpa only [← measure_eq_trim]
  using outer_measure.exists_measurable_superset_forall_eq_trim (λ i, (μ i).to_outer_measure) s

/-- A measurable set `t ⊇ s` such that `μ t = μ s`. -/
def to_measurable (μ : measure α) (s : set α) : set α :=
classical.some (exists_measurable_superset μ s)

lemma subset_to_measurable (μ : measure α) (s : set α) : s ⊆ to_measurable μ s :=
(classical.some_spec (exists_measurable_superset μ s)).1

@[simp] lemma measurable_set_to_measurable (μ : measure α) (s : set α) :
  measurable_set (to_measurable μ s) :=
(classical.some_spec (exists_measurable_superset μ s)).2.1

@[simp] lemma measure_to_measurable (s : set α) : μ (to_measurable μ s) = μ s :=
(classical.some_spec (exists_measurable_superset μ s)).2.2

lemma exists_measurable_superset_of_null (h : μ s = 0) :
  ∃ t, s ⊆ t ∧ measurable_set t ∧ μ t = 0 :=
outer_measure.exists_measurable_superset_of_trim_eq_zero (by rw [← measure_eq_trim, h])

lemma exists_measurable_superset_iff_measure_eq_zero :
  (∃ t, s ⊆ t ∧ measurable_set t ∧ μ t = 0) ↔ μ s = 0 :=
⟨λ ⟨t, hst, _, ht⟩, measure_mono_null hst ht, exists_measurable_superset_of_null⟩

theorem measure_Union_le [encodable β] (s : β → set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
μ.to_outer_measure.Union _

lemma measure_bUnion_le {s : set β} (hs : countable s) (f : β → set α) :
  μ (⋃ b ∈ s, f b) ≤ ∑' p : s, μ (f p) :=
begin
  haveI := hs.to_encodable,
  rw [bUnion_eq_Union],
  apply measure_Union_le
end

lemma measure_bUnion_finset_le (s : finset β) (f : β → set α) :
  μ (⋃ b ∈ s, f b) ≤ ∑ p in s, μ (f p) :=
begin
  rw [← finset.sum_attach, finset.attach_eq_univ, ← tsum_fintype],
  exact measure_bUnion_le s.countable_to_set f
end

lemma measure_bUnion_lt_top {s : set β} {f : β → set α} (hs : finite s)
  (hfin : ∀ i ∈ s, μ (f i) < ∞) : μ (⋃ i ∈ s, f i) < ∞ :=
begin
  convert (measure_bUnion_finset_le hs.to_finset f).trans_lt _,
  { ext, rw [finite.mem_to_finset] },
  apply ennreal.sum_lt_top, simpa only [finite.mem_to_finset]
end

lemma measure_Union_null [encodable β] {s : β → set α} :
  (∀ i, μ (s i) = 0) → μ (⋃ i, s i) = 0 :=
μ.to_outer_measure.Union_null

lemma measure_Union_null_iff [encodable ι] {s : ι → set α} :
  μ (⋃ i, s i) = 0 ↔ ∀ i, μ (s i) = 0 :=
⟨λ h i, measure_mono_null (subset_Union _ _) h, measure_Union_null⟩

lemma measure_bUnion_null_iff {s : set ι} (hs : countable s) {t : ι → set α} :
  μ (⋃ i ∈ s, t i) = 0 ↔ ∀ i ∈ s, μ (t i) = 0 :=
by { haveI := hs.to_encodable, rw [← Union_subtype, measure_Union_null_iff, set_coe.forall], refl }

theorem measure_union_le (s₁ s₂ : set α) : μ (s₁ ∪ s₂) ≤ μ s₁ + μ s₂ :=
μ.to_outer_measure.union _ _

lemma measure_union_null : μ s₁ = 0 → μ s₂ = 0 → μ (s₁ ∪ s₂) = 0 :=
μ.to_outer_measure.union_null

lemma measure_union_null_iff : μ (s₁ ∪ s₂) = 0 ↔ μ s₁ = 0 ∧ μ s₂ = 0:=
⟨λ h, ⟨measure_mono_null (subset_union_left _ _) h, measure_mono_null (subset_union_right _ _) h⟩,
  λ h, measure_union_null h.1 h.2⟩

/-! ### The almost everywhere filter -/

/-- The “almost everywhere” filter of co-null sets. -/
def measure.ae (μ : measure α) : filter α :=
{ sets := {s | μ sᶜ = 0},
  univ_sets := by simp,
  inter_sets := λ s t hs ht, by simp only [compl_inter, mem_set_of_eq];
    exact measure_union_null hs ht,
  sets_of_superset := λ s t hs hst, measure_mono_null (set.compl_subset_compl.2 hst) hs }

notation `∀ᵐ` binders ` ∂` μ `, ` r:(scoped P, filter.eventually P (measure.ae μ)) := r
notation `∃ᵐ` binders ` ∂` μ `, ` r:(scoped P, filter.frequently P (measure.ae μ)) := r
notation f ` =ᵐ[`:50 μ:50 `] `:0 g:50 := f =ᶠ[measure.ae μ] g
notation f ` ≤ᵐ[`:50 μ:50 `] `:0 g:50 := f ≤ᶠ[measure.ae μ] g

lemma mem_ae_iff {s : set α} : s ∈ μ.ae ↔ μ sᶜ = 0 := iff.rfl

lemma ae_iff {p : α → Prop} : (∀ᵐ a ∂ μ, p a) ↔ μ { a | ¬ p a } = 0 := iff.rfl

lemma compl_mem_ae_iff {s : set α} : sᶜ ∈ μ.ae ↔ μ s = 0 := by simp only [mem_ae_iff, compl_compl]

lemma frequently_ae_iff {p : α → Prop} : (∃ᵐ a ∂μ, p a) ↔ μ {a | p a} ≠ 0 :=
not_congr compl_mem_ae_iff

lemma frequently_ae_mem_iff {s : set α} : (∃ᵐ a ∂μ, a ∈ s) ↔ μ s ≠ 0 :=
not_congr compl_mem_ae_iff

lemma measure_zero_iff_ae_nmem {s : set α} : μ s = 0 ↔ ∀ᵐ a ∂ μ, a ∉ s :=
compl_mem_ae_iff.symm

lemma ae_of_all {p : α → Prop} (μ : measure α) : (∀ a, p a) → ∀ᵐ a ∂ μ, p a :=
eventually_of_forall

--instance ae_is_measurably_generated : is_measurably_generated μ.ae :=
--⟨λ s hs, let ⟨t, hst, htm, htμ⟩ := exists_measurable_superset_of_null hs in
--  ⟨tᶜ, compl_mem_ae_iff.2 htμ, htm.compl, compl_subset_comm.1 hst⟩⟩

instance : countable_Inter_filter μ.ae :=
⟨begin
  intros S hSc hS,
  simp only [mem_ae_iff, compl_sInter, sUnion_image, bUnion_eq_Union] at hS ⊢,
  haveI := hSc.to_encodable,
  exact measure_Union_null (subtype.forall.2 hS)
end⟩

lemma ae_imp_iff {p : α → Prop} {q : Prop} : (∀ᵐ x ∂μ, q → p x) ↔ (q → ∀ᵐ x ∂μ, p x) :=
filter.eventually_imp_distrib_left

lemma ae_all_iff [encodable ι] {p : α → ι → Prop} :
  (∀ᵐ a ∂ μ, ∀ i, p a i) ↔ (∀ i, ∀ᵐ a ∂ μ, p a i) :=
eventually_countable_forall

lemma ae_ball_iff {S : set ι} (hS : countable S) {p : Π (x : α) (i ∈ S), Prop} :
  (∀ᵐ x ∂ μ, ∀ i ∈ S, p x i ‹_›) ↔ ∀ i ∈ S, ∀ᵐ x ∂ μ, p x i ‹_› :=
eventually_countable_ball hS

lemma ae_eq_refl (f : α → δ) : f =ᵐ[μ] f := eventually_eq.rfl

lemma ae_eq_symm {f g : α → δ} (h : f =ᵐ[μ] g) : g =ᵐ[μ] f :=
h.symm

lemma ae_eq_trans {f g h: α → δ} (h₁ : f =ᵐ[μ] g) (h₂ : g =ᵐ[μ] h) :
  f =ᵐ[μ] h :=
h₁.trans h₂

@[simp] lemma ae_eq_empty : s =ᵐ[μ] (∅ : set α) ↔ μ s = 0 :=
eventually_eq_empty.trans $ by simp [ae_iff]

lemma ae_le_set : s ≤ᵐ[μ] t ↔ μ (s \ t) = 0 :=
calc s ≤ᵐ[μ] t ↔ ∀ᵐ x ∂μ, x ∈ s → x ∈ t : iff.rfl
           ... ↔ μ (s \ t) = 0          : by simp [ae_iff]; refl

@[simp] lemma union_ae_eq_right : (s ∪ t : set α) =ᵐ[μ] t ↔ μ (s \ t) = 0 :=
by simp [eventually_le_antisymm_iff, ae_le_set, union_diff_right,
  diff_eq_empty.2 (set.subset_union_right _ _)]

lemma diff_ae_eq_self : (s \ t : set α) =ᵐ[μ] s ↔ μ (s ∩ t) = 0 :=
by simp [eventually_le_antisymm_iff, ae_le_set, diff_diff_right,
  diff_diff, diff_eq_empty.2 (set.subset_union_right _ _)]

lemma ae_eq_set {s t : set α} :
  s =ᵐ[μ] t ↔ μ (s \ t) = 0 ∧ μ (t \ s) = 0 :=
by simp [eventually_le_antisymm_iff, ae_le_set]

/-- If `s ⊆ t` modulo a set of measure `0`, then `μ s ≤ μ t`. -/
@[mono] lemma measure_mono_ae (H : s ≤ᵐ[μ] t) : μ s ≤ μ t :=
calc μ s ≤ μ (s ∪ t)       : measure_mono $ subset_union_left s t
     ... = μ (t ∪ s \ t)   : by rw [union_diff_self, set.union_comm]
     ... ≤ μ t + μ (s \ t) : measure_union_le _ _
     ... = μ t             : by rw [ae_le_set.1 H, add_zero]

alias measure_mono_ae ← filter.eventually_le.measure_le

/-- If two sets are equal modulo a set of measure zero, then `μ s = μ t`. -/
lemma measure_congr (H : s =ᵐ[μ] t) : μ s = μ t :=
le_antisymm H.le.measure_le H.symm.le.measure_le

/-- A measure space is a measurable space equipped with a
  measure, referred to as `volume`. -/
class measure_space (α : Type*) extends measurable_space α :=
(volume : measure α)

export measure_space (volume)

/-- `volume` is the canonical  measure on `α`. -/
add_decl_doc volume

section measure_space

notation `∀ᵐ` binders `, ` r:(scoped P, filter.eventually P
  (measure_theory.measure.ae measure_theory.measure_space.volume)) := r

notation `∃ᵐ` binders `, ` r:(scoped P, filter.frequently P
  (measure_theory.measure.ae measure_theory.measure_space.volume)) := r

/-- The tactic `exact volume`, to be used in optional (`auto_param`) arguments. -/
meta def volume_tac : tactic unit := `[exact measure_theory.measure_space.volume]

end measure_space

end

end measure_theory


section
open measure_theory

/-!
# Almost everywhere measurable functions

A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. We define this property, called `ae_measurable f μ`. It's properties are discussed in
`measure_theory.measure_space`.
-/

variables [measurable_space α] [measurable_space β]
  {f g : α → β} {μ ν : measure α}

/-- A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. -/
def ae_measurable (f : α → β) (μ : measure α . measure_theory.volume_tac) : Prop :=
∃ g : α → β, measurable g ∧ f =ᵐ[μ] g

lemma measurable.ae_measurable (h : measurable f) : ae_measurable f μ :=
⟨f, h, ae_eq_refl f⟩


namespace ae_measurable

/-- Given an almost everywhere measurable function `f`, associate to it a measurable function
that coincides with it almost everywhere. `f` is explicit in the definition to make sure that
it shows in pretty-printing. -/
def mk (f : α → β) (h : ae_measurable f μ) : α → β := classical.some h

lemma measurable_mk (h : ae_measurable f μ) : measurable (h.mk f) :=
(classical.some_spec h).1

lemma ae_eq_mk (h : ae_measurable f μ) : f =ᵐ[μ] (h.mk f) :=
(classical.some_spec h).2

lemma congr (hf : ae_measurable f μ) (h : f =ᵐ[μ] g) : ae_measurable g μ :=
⟨hf.mk f, hf.measurable_mk, h.symm.trans hf.ae_eq_mk⟩

end ae_measurable

lemma ae_measurable_congr (h : f =ᵐ[μ] g) :
  ae_measurable f μ ↔ ae_measurable g μ :=
⟨λ hf, ae_measurable.congr hf h, λ hg, ae_measurable.congr hg h.symm⟩

@[simp] lemma ae_measurable_const {b : β} : ae_measurable (λ a : α, b) μ :=
measurable_const.ae_measurable

lemma measurable.comp_ae_measurable [measurable_space δ] {f : α → δ} {g : δ → β}
  (hg : measurable g) (hf : ae_measurable f μ) : ae_measurable (g ∘ f) μ :=
⟨g ∘ hf.mk f, hg.comp hf.measurable_mk, eventually_eq.fun_comp hf.ae_eq_mk _⟩


end
