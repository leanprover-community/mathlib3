/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import measure_theory.outer_measure
import order.filter.countable_Inter

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

In the first part of the file we define operations on arbitrary functions defined on measurable
sets.

Measures on `α` form a complete lattice.

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

open classical set filter finset function
open_locale classical topological_space big_operators

universes u v w x

namespace measure_theory

/- We first consider operations on arbitrary functions defined on measurable sets. -/
section of_measurable
parameters {α : Type*} [measurable_space α]
parameters (m : Π (s : set α), is_measurable s → ennreal)
parameters (m0 : m ∅ is_measurable.empty = 0)
include m0

/-- We can trivially extend a function defined on measurable sets to all sets by defining it to be
 `∞` on the non-measurable sets.

`measure'` is mainly used to derive the outer measure, for the main `measure` projection. -/
def measure' (s : set α) : ennreal := ⨅ h : is_measurable s, m s h

lemma measure'_eq {s} (h : is_measurable s) : measure' s = m s h :=
by simp [measure', h]

lemma measure'_empty : measure' ∅ = 0 :=
(measure'_eq is_measurable.empty).trans m0

lemma measure'_Union_nat
  {f : ℕ → set α}
  (hm : ∀i, is_measurable (f i))
  (mU : m (⋃i, f i) (is_measurable.Union hm) = (∑'i, m (f i) (hm i))) :
  measure' (⋃i, f i) = (∑'i, measure' (f i)) :=
(measure'_eq _).trans $ mU.trans $
by congr; funext i; rw measure'_eq

/-- Given an arbitrary function on measurable sets, we can define the outer measure corresponding to
  it (this is the unique maximal outer measure that is at most `m` on measurable sets). -/
def outer_measure' : outer_measure α :=
outer_measure.of_function measure' measure'_empty

lemma measure'_Union_le_tsum_nat'
  (mU : ∀ {f : ℕ → set α} (hm : ∀i, is_measurable (f i)),
    m (⋃i, f i) (is_measurable.Union hm) ≤ (∑'i, m (f i) (hm i)))
  (s : ℕ → set α) :
  measure' (⋃i, s i) ≤ (∑'i, measure' (s i)) :=
begin
  by_cases h : ∀i, is_measurable (s i),
  { rw [measure'_eq _ _ (is_measurable.Union h),
        congr_arg tsum _], {apply mU h},
    funext i, apply measure'_eq _ _ (h i) },
  { cases not_forall.1 h with i hi,
    exact le_trans (le_infi $ λ h, hi.elim h) (ennreal.le_tsum i) }
end

parameter (mU : ∀ {f : ℕ → set α} (hm : ∀i, is_measurable (f i)),
  pairwise (disjoint on f) →
  m (⋃i, f i) (is_measurable.Union hm) = (∑'i, m (f i) (hm i)))
include mU

lemma measure'_Union
  {β} [encodable β] {f : β → set α}
  (hd : pairwise (disjoint on f)) (hm : ∀i, is_measurable (f i)) :
  measure' (⋃i, f i) = (∑'i, measure' (f i)) :=
begin
  rw [encodable.Union_decode2, outer_measure.Union_aux],
  { exact measure'_Union_nat _ _
      (λ n, encodable.Union_decode2_cases is_measurable.empty hm)
      (mU _ (measurable_space.Union_decode2_disjoint_on hd)) },
  { apply measure'_empty },
end

lemma measure'_union {s₁ s₂ : set α}
  (hd : disjoint s₁ s₂) (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) :
  measure' (s₁ ∪ s₂) = measure' s₁ + measure' s₂ :=
begin
  rw [union_eq_Union, measure'_Union _ _ @mU
      (pairwise_disjoint_on_bool.2 hd) (bool.forall_bool.2 ⟨h₂, h₁⟩),
    tsum_fintype],
  change _+_ = _, simp
end

lemma measure'_mono {s₁ s₂ : set α} (h₁ : is_measurable s₁) (hs : s₁ ⊆ s₂) :
  measure' s₁ ≤ measure' s₂ :=
le_infi $ λ h₂, begin
  have := measure'_union _ _ @mU disjoint_diff h₁ (h₂.diff h₁),
  rw union_diff_cancel hs at this,
  rw ← measure'_eq m m0 _,
  exact le_iff_exists_add.2 ⟨_, this⟩
end

lemma measure'_Union_le_tsum_nat : ∀ (s : ℕ → set α),
  measure' (⋃i, s i) ≤ (∑'i, measure' (s i)) :=
measure'_Union_le_tsum_nat' $ λ f h, begin
  simp [Union_disjointed.symm] {single_pass := tt},
  rw [mU (is_measurable.disjointed h) disjoint_disjointed],
  refine ennreal.tsum_le_tsum (λ i, _),
  rw [← measure'_eq m m0, ← measure'_eq m m0],
  exact measure'_mono _ _ @mU (is_measurable.disjointed h _) (inter_subset_left _ _)
end

lemma outer_measure'_eq {s : set α} (hs : is_measurable s) :
  outer_measure' s = m s hs :=
by rw ← measure'_eq m m0 hs; exact
(le_antisymm (outer_measure.of_function_le _ _ _) $
  le_infi $ λ f, le_infi $ λ hf,
  le_trans (measure'_mono _ _ @mU hs hf) $
  measure'_Union_le_tsum_nat _ _ @mU _)

lemma outer_measure'_eq_measure' {s : set α} (hs : is_measurable s) :
  outer_measure' s = measure' s :=
by rw [measure'_eq m m0 hs, outer_measure'_eq m m0 @mU hs]

end of_measurable

namespace outer_measure
variables {α : Type*} [measurable_space α] (m : outer_measure α)

/-- Given an outer measure `m` we can forget its value on non-measurable sets, and then consider
  `m.trim`, the unique maximal outer measure less than that function. -/
def trim : outer_measure α :=
outer_measure' (λ s _, m s) m.empty

theorem trim_ge : m ≤ m.trim :=
λ s, le_infi $ λ f, le_infi $ λ hs,
le_trans (m.mono hs) $ le_trans (m.Union_nat f) $
ennreal.tsum_le_tsum $ λ i, le_infi $ λ hf, le_refl _

theorem trim_eq {s : set α} (hs : is_measurable s) : m.trim s = m s :=
le_antisymm (le_trans (of_function_le _ _ _) (infi_le _ hs)) (trim_ge _ _)

theorem trim_congr {m₁ m₂ : outer_measure α}
  (H : ∀ {s : set α}, is_measurable s → m₁ s = m₂ s) :
  m₁.trim = m₂.trim :=
by unfold trim; congr; funext s hs; exact H hs

theorem trim_le_trim {m₁ m₂ : outer_measure α} (H : m₁ ≤ m₂) : m₁.trim ≤ m₂.trim :=
λ s, infi_le_infi $ λ f, infi_le_infi $ λ hs,
ennreal.tsum_le_tsum $ λ b, infi_le_infi $ λ hf, H _

theorem le_trim_iff {m₁ m₂ : outer_measure α} : m₁ ≤ m₂.trim ↔
  ∀ s, is_measurable s → m₁ s ≤ m₂ s :=
le_of_function.trans $ forall_congr $ λ s, le_infi_iff

theorem trim_eq_infi (s : set α) : m.trim s = ⨅ t (st : s ⊆ t) (ht : is_measurable t), m t :=
begin
  refine le_antisymm
    (le_infi $ λ t, le_infi $ λ st, le_infi $ λ ht, _)
    (le_infi $ λ f, le_infi $ λ hf, _),
  { rw ← trim_eq m ht, exact (trim m).mono st },
  { by_cases h : ∀i, is_measurable (f i),
    { refine infi_le_of_le _ (infi_le_of_le hf $
        infi_le_of_le (is_measurable.Union h) _),
      rw congr_arg tsum _, {exact m.Union_nat _},
      funext i, exact measure'_eq _ _ (h i) },
    { cases not_forall.1 h with i hi,
      exact le_trans (le_infi $ λ h, hi.elim h) (ennreal.le_tsum i) } }
end

theorem trim_eq_infi' (s : set α) : m.trim s = ⨅ t : {t // s ⊆ t ∧ is_measurable t}, m t.1 :=
by simp [infi_subtype, infi_and, trim_eq_infi]

theorem trim_trim (m : outer_measure α) : m.trim.trim = m.trim :=
le_antisymm (le_trim_iff.2 $ λ s hs, by simp [trim_eq _ hs, le_refl]) (trim_ge _)

theorem trim_zero : (0 : outer_measure α).trim = 0 :=
ext $ λ s, le_antisymm
  (le_trans ((trim 0).mono (subset_univ s)) $
    le_of_eq $ trim_eq _ is_measurable.univ)
  (zero_le _)

theorem trim_add (m₁ m₂ : outer_measure α) : (m₁ + m₂).trim = m₁.trim + m₂.trim :=
ext $ λ s, begin
  simp [trim_eq_infi'],
  rw ennreal.infi_add_infi,
  rintro ⟨t₁, st₁, ht₁⟩ ⟨t₂, st₂, ht₂⟩,
  exact ⟨⟨_, subset_inter_iff.2 ⟨st₁, st₂⟩, ht₁.inter ht₂⟩,
    add_le_add
      (m₁.mono' (inter_subset_left _ _))
      (m₂.mono' (inter_subset_right _ _))⟩,
end

theorem trim_sum_ge {ι} (m : ι → outer_measure α) : sum (λ i, (m i).trim) ≤ (sum m).trim :=
λ s, by simp [trim_eq_infi]; exact
λ t st ht, ennreal.tsum_le_tsum (λ i,
  infi_le_of_le t $ infi_le_of_le st $ infi_le _ ht)

end outer_measure

/-- A measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure. -/
structure measure (α : Type*) [measurable_space α] extends outer_measure α :=
(m_Union {f : ℕ → set α} :
  (∀i, is_measurable (f i)) → pairwise (disjoint on f) →
  measure_of (⋃i, f i) = (∑'i, measure_of (f i)))
(trimmed : to_outer_measure.trim = to_outer_measure)

/-- Measure projections for a measure space.

For measurable sets this returns the measure assigned by the `measure_of` field in `measure`.
But we can extend this to _all_ sets, but using the outer measure. This gives us monotonicity and
subadditivity for all sets.
-/
instance measure.has_coe_to_fun {α} [measurable_space α] : has_coe_to_fun (measure α) :=
⟨λ _, set α → ennreal, λ m, m.to_outer_measure⟩

namespace measure

/-- Obtain a measure by giving a countably additive function that sends `∅` to `0`. -/
def of_measurable {α} [measurable_space α]
  (m : Π (s : set α), is_measurable s → ennreal)
  (m0 : m ∅ is_measurable.empty = 0)
  (mU : ∀ {f : ℕ → set α} (h : ∀i, is_measurable (f i)),
    pairwise (disjoint on f) →
    m (⋃i, f i) (is_measurable.Union h) = (∑'i, m (f i) (h i))) :
  measure α :=
{ m_Union := λ f hf hd,
  show outer_measure' m m0 (Union f) =
      ∑' i, outer_measure' m m0 (f i), begin
    rw [outer_measure'_eq m m0 @mU, mU hf hd],
    congr, funext n, rw outer_measure'_eq m m0 @mU
  end,
  trimmed :=
  show (outer_measure' m m0).trim = outer_measure' m m0, begin
    unfold outer_measure.trim,
    congr, funext s hs,
    exact outer_measure'_eq m m0 @mU hs
  end,
  ..outer_measure' m m0 }

lemma of_measurable_apply {α} [measurable_space α]
  {m : Π (s : set α), is_measurable s → ennreal}
  {m0 : m ∅ is_measurable.empty = 0}
  {mU : ∀ {f : ℕ → set α} (h : ∀i, is_measurable (f i)),
    pairwise (disjoint on f) →
    m (⋃i, f i) (is_measurable.Union h) = (∑'i, m (f i) (h i))}
  (s : set α) (hs : is_measurable s) :
  of_measurable m m0 @mU s = m s hs :=
outer_measure'_eq m m0 @mU hs

@[ext] lemma ext {α} [measurable_space α] :
  ∀ {μ₁ μ₂ : measure α}, (∀s, is_measurable s → μ₁ s = μ₂ s) → μ₁ = μ₂
| ⟨m₁, u₁, h₁⟩ ⟨m₂, u₂, h₂⟩ h := by congr; rw [← h₁, ← h₂];
  exact outer_measure.trim_congr h

end measure

section
variables {α : Type*} {β : Type*} {ι : Type*} [measurable_space α] {μ μ₁ μ₂ : measure α}
  {s s₁ s₂ : set α}

@[simp] lemma to_outer_measure_apply (s) : μ.to_outer_measure s = μ s := rfl

lemma measure_eq_trim (s) : μ s = μ.to_outer_measure.trim s :=
by rw μ.trimmed; refl

lemma measure_eq_infi (s) : μ s = ⨅ t (st : s ⊆ t) (ht : is_measurable t), μ t :=
by rw [measure_eq_trim, outer_measure.trim_eq_infi]; refl

lemma measure_eq_outer_measure' :
  μ s = outer_measure' (λ s _, μ s) μ.empty s :=
measure_eq_trim _

lemma to_outer_measure_eq_outer_measure' :
  μ.to_outer_measure = outer_measure' (λ s _, μ s) μ.empty :=
μ.trimmed.symm

lemma measure_eq_measure' (hs : is_measurable s) :
  μ s = measure' (λ s _, μ s) μ.empty s :=
by rw [measure_eq_outer_measure',
  outer_measure'_eq_measure' (λ s _, μ s) _ μ.m_Union hs]

@[simp] lemma measure_empty : μ ∅ = 0 := μ.empty

lemma measure_mono (h : s₁ ⊆ s₂) : μ s₁ ≤ μ s₂ := μ.mono h

lemma measure_mono_null (h : s₁ ⊆ s₂) (h₂ : μ s₂ = 0) : μ s₁ = 0 :=
by rw [← le_zero_iff_eq, ← h₂]; exact measure_mono h

lemma exists_is_measurable_superset_of_measure_eq_zero {s : set α} (h : μ s = 0) :
  ∃t, s ⊆ t ∧ is_measurable t ∧ μ t = 0 :=
begin
  rw [measure_eq_infi] at h,
  have h := (infi_eq_bot _).1 h,
  choose t ht using show ∀n:ℕ, ∃t, s ⊆ t ∧ is_measurable t ∧ μ t < n⁻¹,
  { assume n,
    have : (0 : ennreal) < n⁻¹ :=
      (zero_lt_iff_ne_zero.2 $ ennreal.inv_ne_zero.2 $ ennreal.nat_ne_top _),
    rcases h _ this with ⟨t, ht⟩,
    use [t],
    simpa [(>), infi_lt_iff, -add_comm] using ht },
  refine ⟨⋂n, t n, subset_Inter (λn, (ht n).1), is_measurable.Inter (λn, (ht n).2.1), _⟩,
  refine eq_of_le_of_forall_le_of_dense bot_le (assume r hr, _),
  rcases ennreal.exists_inv_nat_lt (ne_of_gt hr) with ⟨n, hn⟩,
  calc μ (⋂n, t n) ≤ μ (t n) : measure_mono (Inter_subset _ _)
    ... ≤ n⁻¹ : le_of_lt (ht n).2.2
    ... ≤ r : le_of_lt hn
end

theorem measure_Union_le {β} [encodable β] (s : β → set α) : μ (⋃i, s i) ≤ (∑'i, μ (s i)) :=
μ.to_outer_measure.Union _

lemma measure_Union_null {β} [encodable β] {s : β → set α} :
  (∀ i, μ (s i) = 0) → μ (⋃i, s i) = 0 :=
μ.to_outer_measure.Union_null

theorem measure_union_le (s₁ s₂ : set α) : μ (s₁ ∪ s₂) ≤ μ s₁ + μ s₂ :=
μ.to_outer_measure.union _ _

lemma measure_union_null {s₁ s₂ : set α} : μ s₁ = 0 → μ s₂ = 0 → μ (s₁ ∪ s₂) = 0 :=
μ.to_outer_measure.union_null

lemma measure_Union {β} [encodable β] {f : β → set α}
  (hn : pairwise (disjoint on f)) (h : ∀i, is_measurable (f i)) :
  μ (⋃i, f i) = (∑'i, μ (f i)) :=
by rw [measure_eq_measure' (is_measurable.Union h),
     measure'_Union (λ s _, μ s) _ μ.m_Union hn h];
   simp [measure_eq_measure', h]

lemma measure_union (hd : disjoint s₁ s₂) (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) :
  μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
by rw [measure_eq_measure' (h₁.union h₂),
     measure'_union (λ s _, μ s) _ μ.m_Union hd h₁ h₂];
   simp [measure_eq_measure', h₁, h₂]

lemma measure_bUnion {s : set β} {f : β → set α} (hs : countable s)
  (hd : pairwise_on s (disjoint on f)) (h : ∀b∈s, is_measurable (f b)) :
  μ (⋃b∈s, f b) = ∑'p:s, μ (f p) :=
begin
  haveI := hs.to_encodable,
  rw [← measure_Union, bUnion_eq_Union],
  { rintro ⟨i, hi⟩ ⟨j, hj⟩ ij x ⟨h₁, h₂⟩,
    exact hd i hi j hj (mt subtype.ext_val ij:_) ⟨h₁, h₂⟩ },
  { simpa }
end

lemma measure_sUnion {S : set (set α)} (hs : countable S)
  (hd : pairwise_on S disjoint) (h : ∀s∈S, is_measurable s) :
  μ (⋃₀ S) = ∑' s:S, μ s :=
by rw [sUnion_eq_bUnion, measure_bUnion hs hd h]

lemma measure_bUnion_finset {s : finset ι} {f : ι → set α} (hd : pairwise_on ↑s (disjoint on f))
  (hm : ∀b∈s, is_measurable (f b)) :
  μ (⋃b∈s, f b) = ∑ p in s, μ (f p) :=
begin
  rw [← finset.sum_attach, finset.attach_eq_univ, ← tsum_fintype],
  exact measure_bUnion s.countable_to_set hd hm
end

lemma measure_diff {s₁ s₂ : set α} (h : s₂ ⊆ s₁)
  (h₁ : is_measurable s₁) (h₂ : is_measurable s₂)
  (h_fin : μ s₂ < ⊤) : μ (s₁ \ s₂) = μ s₁ - μ s₂ :=
begin
  refine (ennreal.add_sub_self' h_fin).symm.trans _,
  rw [← measure_union disjoint_diff h₂ (h₁.diff h₂), union_diff_cancel h]
end

lemma sum_measure_le_measure_univ {s : finset ι} {t : ι → set α} (h : ∀ i ∈ s, is_measurable (t i))
  (H : pairwise_on ↑s (disjoint on t)) :
  ∑ i in s, μ (t i) ≤ μ (univ : set α) :=
by { rw ← measure_bUnion_finset H h, exact measure_mono (subset_univ _) }

lemma tsum_measure_le_measure_univ {s : ι → set α} (hs : ∀ i, is_measurable (s i))
  (H : pairwise (disjoint on s)) :
  (∑' i, μ (s i)) ≤ μ (univ : set α) :=
begin
  rw [ennreal.tsum_eq_supr_sum],
  exact supr_le (λ s, sum_measure_le_measure_univ (λ i hi, hs i) (λ i hi j hj hij, H i j hij))
end

/-- Pigeonhole principle for measure spaces: if `∑' i, μ (s i) > μ univ`, then
one of the intersections `s i ∩ s j` is not empty. -/
lemma exists_nonempty_inter_of_measure_univ_lt_tsum_measure (μ : measure α) {s : ι → set α}
  (hs : ∀ i, is_measurable (s i)) (H : μ (univ : set α) < ∑' i, μ (s i)) :
  ∃ i j (h : i ≠ j), (s i ∩ s j).nonempty :=
begin
  contrapose! H,
  apply tsum_measure_le_measure_univ hs,
  exact λ i j hij x hx, H i j hij ⟨x, hx⟩
end

/-- Pigeonhole principle for measure spaces: if `s` is a `finset` and
`∑ i in s, μ (t i) > μ univ`, then one of the intersections `t i ∩ t j` is not empty. -/
lemma exists_nonempty_inter_of_measure_univ_lt_sum_measure (μ : measure α) {s : finset ι}
  {t : ι → set α} (h : ∀ i ∈ s, is_measurable (t i)) (H : μ (univ : set α) < ∑ i in s, μ (t i)) :
  ∃ (i ∈ s) (j ∈ s) (h : i ≠ j), (t i ∩ t j).nonempty :=
begin
  contrapose! H,
  apply sum_measure_le_measure_univ h,
  exact λ i hi j hj hij x hx, H i hi j hj hij ⟨x, hx⟩
end

lemma measure_Union_eq_supr_nat {s : ℕ → set α} (h : ∀i, is_measurable (s i)) (hs : monotone s) :
  μ (⋃i, s i) = (⨆i, μ (s i)) :=
begin
  have : ∀ t : finset ℕ, ∃ n, t ⊆ finset.range (n + 1),
    from λ t, (finset.exists_nat_subset_range t).imp (λ n hn, finset.subset.trans hn $
      finset.range_mono $ (le_add_iff_nonneg_right _).2 (zero_le 1)),
  rw [← Union_disjointed, measure_Union disjoint_disjointed (is_measurable.disjointed h),
    ennreal.tsum_eq_supr_sum' _ this],
  congr' 1, ext1 n,
  rw [← measure_bUnion_finset (disjoint_disjointed.pairwise_on _)
    (λ n _, is_measurable.disjointed h n)],
  convert congr_arg μ (Union_disjointed_of_mono hs n),
  ext, simp
end

lemma measure_Inter_eq_infi_nat {s : ℕ → set α}
  (h : ∀i, is_measurable (s i)) (hs : ∀i j, i ≤ j → s j ⊆ s i)
  (hfin : ∃i, μ (s i) < ⊤) :
  μ (⋂i, s i) = (⨅i, μ (s i)) :=
begin
  rcases hfin with ⟨k, hk⟩,
  rw [← ennreal.sub_sub_cancel (by exact hk) (infi_le _ k),
    ennreal.sub_infi,
    ← ennreal.sub_sub_cancel (by exact hk) (measure_mono (Inter_subset _ k)),
    ← measure_diff (Inter_subset _ k) (h k) (is_measurable.Inter h)
      (lt_of_le_of_lt (measure_mono (Inter_subset _ k)) hk),
    diff_Inter, measure_Union_eq_supr_nat],
  { congr, funext i,
    cases le_total k i with ik ik,
    { exact measure_diff (hs _ _ ik) (h k) (h i)
        (lt_of_le_of_lt (measure_mono (hs _ _ ik)) hk) },
    { rw [diff_eq_empty.2 (hs _ _ ik), measure_empty,
      ennreal.sub_eq_zero_of_le (measure_mono (hs _ _ ik))] } },
  { exact λ i, (h k).diff (h i) },
  { exact λ i j ij, diff_subset_diff_right (hs _ _ ij) }
end

lemma measure_eq_inter_diff {μ : measure α} {s t : set α}
  (hs : is_measurable s) (ht : is_measurable t) :
  μ s = μ (s ∩ t) + μ (s \ t) :=
have hd : disjoint (s ∩ t) (s \ t) := assume a ⟨⟨_, hs⟩, _, hns⟩, hns hs ,
by rw [← measure_union hd (hs.inter ht) (hs.diff ht), inter_union_diff s t]

lemma tendsto_measure_Union {μ : measure α} {s : ℕ → set α}
  (hs : ∀n, is_measurable (s n)) (hm : monotone s) :
  tendsto (μ ∘ s) at_top (𝓝 (μ (⋃n, s n))) :=
begin
  rw measure_Union_eq_supr_nat hs hm,
  exact tendsto_at_top_supr_nat (μ ∘ s) (assume n m hnm, measure_mono $ hm $ hnm)
end

lemma tendsto_measure_Inter {μ : measure α} {s : ℕ → set α}
  (hs : ∀n, is_measurable (s n)) (hm : ∀n m, n ≤ m → s m ⊆ s n) (hf : ∃i, μ (s i) < ⊤) :
  tendsto (μ ∘ s) at_top (𝓝 (μ (⋂n, s n))) :=
begin
  rw measure_Inter_eq_infi_nat hs hm hf,
  exact tendsto_at_top_infi_nat (μ ∘ s) (assume n m hnm, measure_mono $ hm _ _ $ hnm),
end

end
/-- Obtain a measure by giving an outer measure where all sets in the σ-algebra are
  Carathéodory measurable. -/
def outer_measure.to_measure {α} (m : outer_measure α)
  [ms : measurable_space α] (h : ms ≤ m.caratheodory) :
  measure α :=
measure.of_measurable (λ s _, m s) m.empty
  (λ f hf hd, m.Union_eq_of_caratheodory (λ i, h _ (hf i)) hd)

lemma le_to_outer_measure_caratheodory {α} [ms : measurable_space α]
  (μ : measure α) : ms ≤ μ.to_outer_measure.caratheodory :=
begin
  assume s hs,
  rw to_outer_measure_eq_outer_measure',
  refine outer_measure.caratheodory_is_measurable (λ t, le_infi $ λ ht, _),
  rw [← measure_eq_measure' (ht.inter hs),
    ← measure_eq_measure' (ht.diff hs),
    ← measure_union _ (ht.inter hs) (ht.diff hs),
    inter_union_diff],
  exact le_refl _,
  exact λ x ⟨⟨_, h₁⟩, _, h₂⟩, h₂ h₁
end

lemma to_measure_to_outer_measure {α} (m : outer_measure α)
  [ms : measurable_space α] (h : ms ≤ m.caratheodory) :
  (m.to_measure h).to_outer_measure = m.trim := rfl

@[simp] lemma to_measure_apply {α} (m : outer_measure α)
  [ms : measurable_space α] (h : ms ≤ m.caratheodory)
  {s : set α} (hs : is_measurable s) :
  m.to_measure h s = m s := m.trim_eq hs

lemma to_outer_measure_to_measure {α : Type*} [ms : measurable_space α] {μ : measure α} :
  μ.to_outer_measure.to_measure (le_to_outer_measure_caratheodory _) = μ :=
measure.ext $ λ s, μ.to_outer_measure.trim_eq

namespace measure
variables {α : Type*} {β : Type*} {γ : Type*}
  [measurable_space α] [measurable_space β] [measurable_space γ]

instance : has_zero (measure α) :=
⟨{ to_outer_measure := 0,
   m_Union := λ f hf hd, tsum_zero.symm,
   trimmed := outer_measure.trim_zero }⟩

@[simp] theorem zero_to_outer_measure :
  (0 : measure α).to_outer_measure = 0 := rfl

@[simp] theorem zero_apply (s : set α) : (0 : measure α) s = 0 := rfl

instance : inhabited (measure α) := ⟨0⟩

instance : has_add (measure α) :=
⟨λμ₁ μ₂, {
  to_outer_measure := μ₁.to_outer_measure + μ₂.to_outer_measure,
  m_Union := λs hs hd,
    show μ₁ (⋃ i, s i) + μ₂ (⋃ i, s i) = ∑' i, μ₁ (s i) + μ₂ (s i),
    by rw [ennreal.tsum_add, measure_Union hd hs, measure_Union hd hs],
  trimmed := by rw [outer_measure.trim_add, μ₁.trimmed, μ₂.trimmed] }⟩

@[simp] theorem add_to_outer_measure (μ₁ μ₂ : measure α) :
  (μ₁ + μ₂).to_outer_measure = μ₁.to_outer_measure + μ₂.to_outer_measure := rfl

@[simp] theorem add_apply (μ₁ μ₂ : measure α) (s : set α) :
  (μ₁ + μ₂) s = μ₁ s + μ₂ s := rfl

instance add_comm_monoid : add_comm_monoid (measure α) :=
{ zero      := 0,
  add       := (+),
  add_assoc := assume a b c, ext $ assume s hs, add_assoc _ _ _,
  add_comm  := assume a b, ext $ assume s hs, add_comm _ _,
  zero_add  := assume a, ext $ by simp,
  add_zero  := assume a, ext $ assume s hs, add_zero _ }

instance : partial_order (measure α) :=
{ le          := λm₁ m₂, ∀ s, is_measurable s → m₁ s ≤ m₂ s,
  le_refl     := assume m s hs, le_refl _,
  le_trans    := assume m₁ m₂ m₃ h₁ h₂ s hs, le_trans (h₁ s hs) (h₂ s hs),
  le_antisymm := assume m₁ m₂ h₁ h₂, ext $
    assume s hs, le_antisymm (h₁ s hs) (h₂ s hs) }

theorem le_iff {μ₁ μ₂ : measure α} :
  μ₁ ≤ μ₂ ↔ ∀ s, is_measurable s → μ₁ s ≤ μ₂ s := iff.rfl

theorem to_outer_measure_le {μ₁ μ₂ : measure α} :
  μ₁.to_outer_measure ≤ μ₂.to_outer_measure ↔ μ₁ ≤ μ₂ :=
by rw [← μ₂.trimmed, outer_measure.le_trim_iff]; refl

theorem le_iff' {μ₁ μ₂ : measure α} :
  μ₁ ≤ μ₂ ↔ ∀ s, μ₁ s ≤ μ₂ s :=
to_outer_measure_le.symm

section
variables {m : set (measure α)} {μ : measure α}

lemma Inf_caratheodory (s : set α) (hs : is_measurable s) :
  (Inf (measure.to_outer_measure '' m)).caratheodory.is_measurable s :=
begin
  rw [outer_measure.Inf_eq_of_function_Inf_gen],
  refine outer_measure.caratheodory_is_measurable (assume t, _),
  cases t.eq_empty_or_nonempty with ht ht, by simp [ht],
  simp only [outer_measure.Inf_gen_nonempty1 _ _ ht, le_infi_iff, ball_image_iff,
    to_outer_measure_apply, measure_eq_infi t],
  assume μ hμ u htu hu,
  have hm : ∀{s t}, s ⊆ t → outer_measure.Inf_gen (to_outer_measure '' m) s ≤ μ t,
  { assume s t hst,
    rw [outer_measure.Inf_gen_nonempty2 _ _ (mem_image_of_mem _ hμ)],
    refine infi_le_of_le (μ.to_outer_measure) (infi_le_of_le (mem_image_of_mem _ hμ) _),
    rw [to_outer_measure_apply],
    refine measure_mono hst },
  rw [measure_eq_inter_diff hu hs],
  refine add_le_add (hm $ inter_subset_inter_left _ htu) (hm $ diff_subset_diff_left htu)
end

instance : has_Inf (measure α) :=
⟨λm, (Inf (to_outer_measure '' m)).to_measure $ Inf_caratheodory⟩

lemma Inf_apply {m : set (measure α)} {s : set α} (hs : is_measurable s) :
  Inf m s = Inf (to_outer_measure '' m) s :=
to_measure_apply _ _ hs

private lemma Inf_le (h : μ ∈ m) : Inf m ≤ μ :=
have Inf (to_outer_measure '' m) ≤ μ.to_outer_measure := Inf_le (mem_image_of_mem _ h),
assume s hs, by rw [Inf_apply hs, ← to_outer_measure_apply]; exact this s

private lemma le_Inf (h : ∀μ' ∈ m, μ ≤ μ') : μ ≤ Inf m :=
have μ.to_outer_measure ≤ Inf (to_outer_measure '' m) :=
  le_Inf $ ball_image_of_ball $ assume μ hμ, to_outer_measure_le.2 $ h _ hμ,
assume s hs, by rw [Inf_apply hs, ← to_outer_measure_apply]; exact this s

instance : complete_lattice (measure α) :=
{ bot := 0,
  bot_le := assume a s hs, by exact bot_le,
/- Adding an explicit `top` makes `leanchecker` fail, see lean#364, disable for now

  top := (⊤ : outer_measure α).to_measure (by rw [outer_measure.top_caratheodory]; exact le_top),
  le_top := assume a s hs,
    by cases s.eq_empty_or_nonempty with h  h;
      simp [h, to_measure_apply ⊤ _ hs, outer_measure.top_apply],
-/
  .. complete_lattice_of_Inf (measure α) (λ ms, ⟨λ _, Inf_le, λ _, le_Inf⟩) }

end

/-- The pushforward of a measure. It is defined to be `0` if `f` is not a measurable function. -/
def map (f : α → β) (μ : measure α) : measure β :=
if hf : measurable f then
  (μ.to_outer_measure.map f).to_measure $ λ s hs t,
  le_to_outer_measure_caratheodory μ _ (hf _ hs) (f ⁻¹' t)
else 0

variables {μ ν : measure α}

@[simp] theorem map_apply {f : α → β} (hf : measurable f)
  {s : set β} (hs : is_measurable s) :
  (map f μ : measure β) s = μ (f ⁻¹' s) :=
by rw [map, dif_pos hf, to_measure_apply _ _ hs]; refl

@[simp] lemma map_id : map id μ = μ :=
ext $ λ s, map_apply measurable_id

lemma map_map {g : β → γ} {f : α → β} (hg : measurable g) (hf : measurable f) :
  map g (map f μ) = map (g ∘ f) μ :=
ext $ λ s hs,
by simp [hf, hg, hs, hg.preimage hs, hg.comp hf];
   rw ← preimage_comp

/-- The dirac measure. -/
def dirac (a : α) : measure α :=
(outer_measure.dirac a).to_measure (by simp)

@[simp] lemma dirac_apply (a : α) {s : set α} (hs : is_measurable s) :
  (dirac a : measure α) s = ⨆ h : a ∈ s, 1 :=
to_measure_apply _ _ hs

/-- Sum of an indexed family of measures. -/
def sum {ι : Type*} (f : ι → measure α) : measure α :=
(outer_measure.sum (λ i, (f i).to_outer_measure)).to_measure $
le_trans
  (by exact le_infi (λ i, le_to_outer_measure_caratheodory _))
  (outer_measure.le_sum_caratheodory _)

/-- Counting measure on any measurable space. -/
def count : measure α := sum dirac

/-- A measure is complete if every null set is also measurable.
  A null set is a subset of a measurable set with measure `0`.
  Since every measure is defined as a special case of an outer measure, we can more simply state
  that a set `s` is null if `μ s = 0`. -/
@[class] def is_complete {α} {_:measurable_space α} (μ : measure α) : Prop :=
∀ s, μ s = 0 → is_measurable s

/-- The "almost everywhere" filter of co-null sets. -/
def ae (μ : measure α) : filter α :=
{ sets := {s | μ sᶜ = 0},
  univ_sets := by simp [measure_empty],
  inter_sets := λ s t hs ht, by simp [compl_inter]; exact measure_union_null hs ht,
  sets_of_superset := λ s t hs hst, measure_mono_null (set.compl_subset_compl.2 hst) hs }

end measure

variables {α : Type*} {β : Type*} [measurable_space α] {μ : measure α}

notation `∀ₘ` binders `∂` μ `, ` r:(scoped P, μ.ae.eventually P) := r

lemma mem_ae_iff (s : set α) : s ∈ μ.ae.sets ↔ μ sᶜ = 0 := iff.rfl

lemma ae_iff {p : α → Prop} : (∀ₘ a ∂ μ, p a) ↔ μ { a | ¬ p a } = 0 := iff.rfl

lemma measure_zero_iff_ae_nmem {s : set α} : μ s = 0 ↔ ∀ₘ a ∂ μ, a ∉ s :=
by simp only [ae_iff, not_not, set_of_mem_eq]

lemma ae_of_all {p : α → Prop} (μ : measure α) : (∀a, p a) → ∀ₘ a ∂ μ, p a :=
eventually_of_forall _

instance : countable_Inter_filter μ.ae :=
⟨begin
  intros S hSc hS,
  simp only [mem_ae_iff, compl_sInter, sUnion_image, bUnion_eq_Union] at hS ⊢,
  haveI := hSc.to_encodable,
  exact measure_Union_null (subtype.forall.2 hS)
end⟩

lemma ae_all_iff {ι : Type*} [encodable ι] {p : α → ι → Prop} :
  (∀ₘ a ∂ μ, ∀i, p a i) ↔ (∀i, ∀ₘ a ∂ μ, p a i) :=
eventually_countable_forall

lemma ae_ball_iff {ι} {S : set ι} (hS : countable S) {p : Π (x : α) (i ∈ S), Prop} :
  (∀ₘ x ∂ μ, ∀ i ∈ S, p x i ‹_›) ↔ ∀ i ∈ S, ∀ₘ x ∂ μ, p x i ‹_› :=
eventually_countable_ball hS

lemma ae_eq_refl (f : α → β) : ∀ₘ a ∂ μ, f a = f a :=
ae_of_all μ $ λ a, rfl

lemma ae_eq_symm {f g : α → β} (h : ∀ₘ a ∂ μ, f a = g a) : (∀ₘ a ∂ μ, g a = f a) :=
h.mono $ λ a, eq.symm

lemma ae_eq_trans {f g h: α → β} (h₁ : ∀ₘ a ∂ μ, f a = g a) (h₂ : ∀ₘ a ∂ μ, g a = h a) :
  ∀ₘ a ∂ μ, f a = h a :=
by { filter_upwards [h₁, h₂], intro a, exact eq.trans }

end measure_theory

section is_complete
open measure_theory

variables {α : Type*} [measurable_space α] (μ : measure α)

/-- A set is null measurable if it is the union of a null set and a measurable set. -/
def is_null_measurable (s : set α) : Prop :=
∃ t z, s = t ∪ z ∧ is_measurable t ∧ μ z = 0

theorem is_null_measurable_iff {μ : measure α} {s : set α} :
  is_null_measurable μ s ↔
  ∃ t, t ⊆ s ∧ is_measurable t ∧ μ (s \ t) = 0 :=
begin
  split,
  { rintro ⟨t, z, rfl, ht, hz⟩,
    refine ⟨t, set.subset_union_left _ _, ht, measure_mono_null _ hz⟩,
    simp [union_diff_left, diff_subset] },
  { rintro ⟨t, st, ht, hz⟩,
    exact ⟨t, _, (union_diff_cancel st).symm, ht, hz⟩ }
end

theorem is_null_measurable_measure_eq {μ : measure α} {s t : set α}
  (st : t ⊆ s) (hz : μ (s \ t) = 0) : μ s = μ t :=
begin
  refine le_antisymm _ (measure_mono st),
  have := measure_union_le t (s \ t),
  rw [union_diff_cancel st, hz] at this, simpa
end

theorem is_measurable.is_null_measurable
  {s : set α} (hs : is_measurable s) : is_null_measurable μ s :=
⟨s, ∅, by simp, hs, μ.empty⟩

theorem is_null_measurable_of_complete [c : μ.is_complete]
  {s : set α} : is_null_measurable μ s ↔ is_measurable s :=
⟨by rintro ⟨t, z, rfl, ht, hz⟩; exact
  is_measurable.union ht (c _ hz),
 λ h, h.is_null_measurable _⟩

variables {μ}
theorem is_null_measurable.union_null {s z : set α}
  (hs : is_null_measurable μ s) (hz : μ z = 0) :
  is_null_measurable μ (s ∪ z) :=
begin
  rcases hs with ⟨t, z', rfl, ht, hz'⟩,
  exact ⟨t, z' ∪ z, set.union_assoc _ _ _, ht, le_zero_iff_eq.1
    (le_trans (measure_union_le _ _) $ by simp [hz, hz'])⟩
end

theorem null_is_null_measurable {z : set α}
  (hz : μ z = 0) : is_null_measurable μ z :=
by simpa using (is_measurable.empty.is_null_measurable _).union_null hz

theorem is_null_measurable.Union_nat {s : ℕ → set α}
  (hs : ∀ i, is_null_measurable μ (s i)) :
  is_null_measurable μ (Union s) :=
begin
  choose t ht using assume i, is_null_measurable_iff.1 (hs i),
  simp [forall_and_distrib] at ht,
  rcases ht with ⟨st, ht, hz⟩,
  refine is_null_measurable_iff.2
    ⟨Union t, Union_subset_Union st, is_measurable.Union ht,
      measure_mono_null _ (measure_Union_null hz)⟩,
  rw [diff_subset_iff, ← Union_union_distrib],
  exact Union_subset_Union (λ i, by rw ← diff_subset_iff)
end

theorem is_measurable.diff_null {s z : set α}
  (hs : is_measurable s) (hz : μ z = 0) :
  is_null_measurable μ (s \ z) :=
begin
  rw measure_eq_infi at hz,
  choose f hf using show ∀ q : {q:ℚ//q>0}, ∃ t:set α,
    z ⊆ t ∧ is_measurable t ∧ μ t < (nnreal.of_real q.1 : ennreal),
  { rintro ⟨ε, ε0⟩,
    have : 0 < (nnreal.of_real ε : ennreal), { simpa using ε0 },
    rw ← hz at this, simpa [infi_lt_iff] },
  refine is_null_measurable_iff.2 ⟨s \ Inter f,
    diff_subset_diff_right (subset_Inter (λ i, (hf i).1)),
    hs.diff (is_measurable.Inter (λ i, (hf i).2.1)),
    measure_mono_null _ (le_zero_iff_eq.1 $ le_of_not_lt $ λ h, _)⟩,
  { exact Inter f },
  { rw [diff_subset_iff, diff_union_self],
    exact subset.trans (diff_subset _ _) (subset_union_left _ _) },
  rcases ennreal.lt_iff_exists_rat_btwn.1 h with ⟨ε, ε0', ε0, h⟩,
  simp at ε0,
  apply not_le_of_lt (lt_trans (hf ⟨ε, ε0⟩).2.2 h),
  exact measure_mono (Inter_subset _ _)
end

theorem is_null_measurable.diff_null {s z : set α}
  (hs : is_null_measurable μ s) (hz : μ z = 0) :
  is_null_measurable μ (s \ z) :=
begin
  rcases hs with ⟨t, z', rfl, ht, hz'⟩,
  rw [set.union_diff_distrib],
  exact (ht.diff_null hz).union_null (measure_mono_null (diff_subset _ _) hz')
end

theorem is_null_measurable.compl {s : set α}
  (hs : is_null_measurable μ s) :
  is_null_measurable μ sᶜ :=
begin
  rcases hs with ⟨t, z, rfl, ht, hz⟩,
  rw compl_union,
  exact ht.compl.diff_null hz
end

/-- The measurable space of all null measurable sets. -/
def null_measurable {α : Type u} [measurable_space α]
  (μ : measure α) : measurable_space α :=
{ is_measurable := is_null_measurable μ,
  is_measurable_empty := is_measurable.empty.is_null_measurable _,
  is_measurable_compl := λ s hs, hs.compl,
  is_measurable_Union := λ f, is_null_measurable.Union_nat }

/-- Given a measure we can complete it to a (complete) measure on all null measurable sets. -/
def completion {α : Type u} [measurable_space α] (μ : measure α) :
  @measure_theory.measure α (null_measurable μ) :=
{ to_outer_measure := μ.to_outer_measure,
  m_Union := λ s hs hd, show μ (Union s) = ∑' i, μ (s i), begin
    choose t ht using assume i, is_null_measurable_iff.1 (hs i),
    simp [forall_and_distrib] at ht, rcases ht with ⟨st, ht, hz⟩,
    rw is_null_measurable_measure_eq (Union_subset_Union st),
    { rw measure_Union _ ht,
      { congr, funext i,
        exact (is_null_measurable_measure_eq (st i) (hz i)).symm },
      { rintro i j ij x ⟨h₁, h₂⟩,
        exact hd i j ij ⟨st i h₁, st j h₂⟩ } },
    { refine measure_mono_null _ (measure_Union_null hz),
      rw [diff_subset_iff, ← Union_union_distrib],
      exact Union_subset_Union (λ i, by rw ← diff_subset_iff) }
  end,
  trimmed := begin
    letI := null_measurable μ,
    refine le_antisymm (λ s, _) (outer_measure.trim_ge _),
    rw outer_measure.trim_eq_infi,
    dsimp,
    clear _inst,
    resetI,
    rw measure_eq_infi s,
    exact infi_le_infi (λ t, infi_le_infi $ λ st,
      infi_le_infi2 $ λ ht, ⟨ht.is_null_measurable _, le_refl _⟩)
  end }

instance completion.is_complete {α : Type u} [measurable_space α] (μ : measure α) :
  (completion μ).is_complete :=
λ z hz, null_is_null_measurable hz

end is_complete

namespace measure_theory

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A measure space is a measurable space equipped with a
  measure, referred to as `volume`. -/
class measure_space (α : Type*) extends measurable_space α :=
(volume : measure α)
end prio

export measure_space (volume)

/-- `volume` is the canonical  measure on `α`. -/
add_decl_doc volume

section measure_space
variables {α : Type*} {ι : Type*} [measure_space α] {s₁ s₂ : set α}

notation `∀ₘ` binders `, ` r:(scoped P, volume.ae.eventually P) := r

end measure_space

end measure_theory
