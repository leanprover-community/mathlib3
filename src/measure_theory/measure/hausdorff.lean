/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.metric_space.metric_separated
import measure_theory.constructions.borel_space
import measure_theory.measure.lebesgue
import analysis.special_functions.pow
import topology.metric_space.holder
import data.equiv.list

/-!
# Hausdorff measure and metric (outer) measures

In this file we define the `d`-dimensional Hausdorff measure on an (extended) metric space `X` and
the Hausdorff dimension of a set in an (extended) metric space. Let `μ d δ` be the maximal outer
measure such that `μ d δ s ≤ (emetric.diam s) ^ d` for every set of diameter less than `δ`. Then
the Hausdorff measure `μH[d] s` of `s` is defined as `⨆ δ > 0, μ d δ s`. By Caratheodory theorem
`measure_theory.outer_measure.is_metric.borel_le_caratheodory`, this is a Borel measure on `X`.

The value of `μH[d]`, `d > 0`, on a set `s` (measurable or not) is given by
```
μH[d] s = ⨆ (r : ℝ≥0∞) (hr : 0 < r), ⨅ (t : ℕ → set X) (hts : s ⊆ ⋃ n, t n)
    (ht : ∀ n, emetric.diam (t n) ≤ r), ∑' n, emetric.diam (t n) ^ d
```

For every set `s` for any `d < d'` we have either `μH[d] s = ∞` or `μH[d'] s = 0`, see
`measure_theory.measure.hausdorff_measure_zero_or_top`. The Hausdorff dimension `dimH s : ℝ≥0∞` of a
set `s` is the supremum of `d : ℝ≥0` such that `μH[d] s = ∞`. Then `μH[d] s = ∞` for `d < dimH s`
and `μH[d] s = 0` for `dimH s < d`.

We also define two generalizations of the Hausdorff measure. In one generalization (see
`measure_theory.measure.mk_metric`) we take any function `m (diam s)` instead of `(diam s) ^ d`. In
an even more general definition (see `measure_theory.measure.mk_metric'`) we use any function
of `m : set X → ℝ≥0∞`. Some authors start with a partial function `m` defined only on some sets
`s : set X` (e.g., only on balls or only on measurable sets). This is equivalent to our definition
applied to `measure_theory.extend m`.

We also define a predicate `measure_theory.outer_measure.is_metric` which says that an outer measure
is additive on metric separated pairs of sets: `μ (s ∪ t) = μ s + μ t` provided that
`⨅ (x ∈ s) (y ∈ t), edist x y ≠ 0`. This is the property required for the Caratheodory theorem
`measure_theory.outer_measure.is_metric.borel_le_caratheodory`, so we prove this theorem for any
metric outer measure, then prove that outer measures constructed using `mk_metric'` are metric outer
measures.

## Main definitions

* `measure_theory.outer_measure.is_metric`: an outer measure `μ` is called *metric* if
  `μ (s ∪ t) = μ s + μ t` for any two metric separated sets `s` and `t`. A metric outer measure in a
  Borel extended metric space is guaranteed to satisfy the Caratheodory condition, see
  `measure_theory.outer_measure.is_metric.borel_le_caratheodory`.
* `measure_theory.outer_measure.mk_metric'` and its particular case
  `measure_theory.outer_measure.mk_metric`: a construction of an outer measure that is guaranteed to
  be metric. Both constructions are generalizations of the Hausdorff measure. The same measures
  interpreted as Borel measures are called `measure_theory.measure.mk_metric'` and
  `measure_theory.measure.mk_metric`.
* `measure_theory.measure.hausdorff_measure` a.k.a. `μH[d]`: the `d`-dimensional Hausdorff measure.
  There are many definitions of the Hausdorff measure that differ from each other by a
  multiplicative constant. We put
  `μH[d] s = ⨆ r > 0, ⨅ (t : ℕ → set X) (hts : s ⊆ ⋃ n, t n) (ht : ∀ n, emetric.diam (t n) ≤ r),
    ∑' n, ⨆ (ht : ¬set.subsingleton (t n)), (emetric.diam (t n)) ^ d`,
  see `measure_theory.measure.hausdorff_measure_apply'`. In the most interesting case `0 < d` one
  can omit the `⨆ (ht : ¬set.subsingleton (t n))` part.
* `measure_theory.dimH`: the Hausdorff dimension of a set. For the Hausdorff dimension of the whole
  space we use `measure_theory.dimH (set.univ : set X)`.

## Main statements

### Basic properties

* `measure_theory.outer_measure.is_metric.borel_le_caratheodory`: if `μ` is a metric outer measure
  on an extended metric space `X` (that is, it is additive on pairs of metric separated sets), then
  every Borel set is Caratheodory measurable (hence, `μ` defines an actual
  `measure_theory.measure`). See also `measure_theory.measure.mk_metric`.
* `measure_theory.measure.hausdorff_measure_mono`: `μH[d] s` is a monotonically decreasing function
  of `d`.
* `measure_theory.measure.hausdorff_measure_zero_or_top`: if `d₁ < d₂`, then for any `s`, either
  `μH[d₂] s = 0` or `μH[d₁] s = ∞`. Together with the previous lemma, this means that `μH[d] s` is
  equal to infinity on some ray `(-∞, D)` and is equal to zero on `(D, +∞)`, where `D` is a possibly
  infinite number called the *Hausdorff dimension* of `s`; `μH[D] s` can be zero, infinity, or
  anything in between.
* `measure_theory.measure.hausdorff_measure_of_lt_dimH`,
  `measure_theory.measure.hausdorff_measure_of_dimH_lt`: if `d < dimH s`
  (resp., `dimH s < d`), then `μH[d] s = ∞` (resp., `μH[d] s = 0`).
* `measure_theory.measure.dimH_union`: the Hausdorff dimension of the union of two sets is the
  maximum of their Hausdorff dimensions.
* `measure_theory.measure.dimH_Union`, `measure_theory.measure.dimH_bUnion`,
  `measure_theory.measure.dimH_sUnion`: the Hausdorff dimension of a countable union of sets is the
  supremum of their Hausdorff dimensions.
* `measure_theory.measure.no_atoms_hausdorff`, `measure_theory.measure.dimH_empty`,
  `measure_theory.measure.dimH_singleton`, `set.subsingleton.dimH_zero`, `set.countable.dimH_zero`:
  Hausdorff measure has no atoms and `dimH s = 0` whenever `s` is countable.

### (Pre)images under (anti)lipschitz and Hölder continuous maps

* `holder_with.dimH_image_le` etc: if `f : X → Y` is Hölder continuous with exponent `r > 0`, then
  for any `s`, `dimH (f '' s) ≤ dimH s / r`. We prove versions of this statement for `holder_with`,
  `holder_on_with`, and locally Hölder maps, as well as for `set.image` and `set.range`.
* `lipschitz_with.dimH_image_le` etc: Lipschitz continuous maps do not increase the Hausdorff
  dimension of sets.
* for a map that is known to be both Lipschitz and antilipschitz (e.g., for an `isometry` or
  a `continuous_linear_equiv`) we also prove `dimH (f '' s) = dimH s`.

### Hausdorff measure in `ℝⁿ`

* `measure_theory.hausdorff_measure_pi_real`: for a nonempty `ι`, `μH[card ι]` on `ι → ℝ` equals
  Lebesgue measure.
* `real.dimH_of_nonempty_interior`: if `s` is a set in a finite dimensional real vector space `E`
  with nonempty interior, then the Hausdorff dimension of `s` is equal to the dimension of `E`.
* `dense_compl_of_dimH_lt_finrank`: if `s` is a set in a finite dimensional real vector space `E`
  with Hausdorff dimension strictly less than the dimension of `E`, the `s` has a dense complement.
* `times_cont_diff.dense_compl_range_of_finrank_lt_finrank`: the complement to the range of a `C¹`
  smooth map is dense provided that the dimension of the domain is strictly less than the dimension
  of the codomain.

## Notations

We use the following notation localized in `measure_theory`.

- `μH[d]` : `measure_theory.measure.hausdorff_measure d`

## Implementation notes

There are a few similar constructions called the `d`-dimensional Hausdorff measure. E.g., some
sources only allow coverings by balls and use `r ^ d` instead of `(diam s) ^ d`. While these
construction lead to different Hausdorff measures, they lead to the same notion of the Hausdorff
dimension.

Some sources define the `0`-dimensional Hausdorff measure to be the counting measure. We define it
to be zero on subsingletons because this way we can have a
`measure.has_no_atoms (measure.hausdorff_measure d)` instance.

## TODO

* prove that `1`-dimensional Hausdorff measure on `ℝ` equals `volume`;
* prove a similar statement for `ℝ × ℝ`.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.10][Federer1996]

## Tags

Hausdorff measure, Hausdorff dimension, dimension, measure, metric measure
-/

open_locale nnreal ennreal topological_space big_operators

open emetric set function filter encodable finite_dimensional topological_space

noncomputable theory

variables {ι X Y : Type*} [emetric_space X] [emetric_space Y]

namespace measure_theory

namespace outer_measure

/-!
### Metric outer measures

In this section we define metric outer measures and prove Caratheodory theorem: a metric outer
measure has the Caratheodory property.
-/

/-- We say that an outer measure `μ` in an (e)metric space is *metric* if `μ (s ∪ t) = μ s + μ t`
for any two metric separated sets `s`, `t`. -/
def is_metric (μ : outer_measure X) : Prop :=
∀ (s t : set X), is_metric_separated s t → μ (s ∪ t) = μ s + μ t

namespace is_metric

variables {μ : outer_measure X}

/-- A metric outer measure is additive on a finite set of pairwise metric separated sets. -/
lemma finset_Union_of_pairwise_separated (hm : is_metric μ) {I : finset ι} {s : ι → set X}
  (hI : ∀ (i ∈ I) (j ∈ I), i ≠ j → is_metric_separated (s i) (s j)) :
  μ (⋃ i ∈ I, s i) = ∑ i in I, μ (s i) :=
begin
  classical,
  induction I using finset.induction_on with i I hiI ihI hI, { simp },
  simp only [finset.mem_insert] at hI,
  rw [finset.set_bUnion_insert, hm, ihI, finset.sum_insert hiI],
  exacts [λ i hi j hj hij, (hI i (or.inr hi) j (or.inr hj) hij),
    is_metric_separated.finset_Union_right
      (λ j hj, hI i (or.inl rfl) j (or.inr hj) (ne_of_mem_of_not_mem hj hiI).symm)]
end

/-- Caratheodory theorem. If `m` is a metric outer measure, then every Borel measurable set `t` is
Caratheodory measurable: for any (not necessarily measurable) set `s` we have
`μ (s ∩ t) + μ (s \ t) = μ s`. -/
lemma borel_le_caratheodory (hm : is_metric μ) :
  borel X ≤ μ.caratheodory :=
begin
  rw [borel_eq_generate_from_is_closed],
  refine measurable_space.generate_from_le (λ t ht, μ.is_caratheodory_iff_le.2 $ λ s, _),
  set S : ℕ → set X := λ n, {x ∈ s | (↑n)⁻¹ ≤ inf_edist x t},
  have n0 : ∀ {n : ℕ}, (n⁻¹ : ℝ≥0∞) ≠ 0, from λ n, ennreal.inv_ne_zero.2 ennreal.coe_nat_ne_top,
  have Ssep : ∀ n, is_metric_separated (S n) t,
    from λ n, ⟨n⁻¹, n0, λ x hx y hy, hx.2.trans $ inf_edist_le_edist_of_mem hy⟩,
  have Ssep' : ∀ n, is_metric_separated (S n) (s ∩ t),
    from λ n, (Ssep n).mono subset.rfl (inter_subset_right _ _),
  have S_sub : ∀ n, S n ⊆ s \ t,
    from λ n, subset_inter (inter_subset_left _ _) (Ssep n).subset_compl_right,
  have hSs : ∀ n, μ (s ∩ t) + μ (S n) ≤ μ s, from λ n,
  calc μ (s ∩ t) + μ (S n) = μ (s ∩ t ∪ S n) :
    eq.symm $ hm _ _ $ (Ssep' n).symm
  ... ≤ μ (s ∩ t ∪ s \ t)  : by { mono*, exact le_rfl }
  ... = μ s : by rw [inter_union_diff],
  have Union_S : (⋃ n, S n) = s \ t,
  { refine subset.antisymm (Union_subset S_sub) _,
    rintro x ⟨hxs, hxt⟩,
    rw mem_iff_inf_edist_zero_of_closed ht at hxt,
    rcases ennreal.exists_inv_nat_lt hxt with ⟨n, hn⟩,
    exact mem_Union.2 ⟨n, hxs, hn.le⟩ },
  /- Now we have `∀ n, μ (s ∩ t) + μ (S n) ≤ μ s` and we need to prove
  `μ (s ∩ t) + μ (⋃ n, S n) ≤ μ s`. We can't pass to the limit because
  `μ` is only an outer measure. -/
  by_cases htop : μ (s \ t) = ∞,
  { rw [htop, ennreal.add_top, ← htop],
    exact μ.mono (diff_subset _ _) },
  suffices : μ (⋃ n, S n) ≤ ⨆ n, μ (S n),
  calc μ (s ∩ t) + μ (s \ t) = μ (s ∩ t) + μ (⋃ n, S n) :
    by rw Union_S
  ... ≤ μ (s ∩ t) + ⨆ n, μ (S n) :
    add_le_add le_rfl this
  ... = ⨆ n, μ (s ∩ t) + μ (S n) : ennreal.add_supr
  ... ≤ μ s : supr_le hSs,
  /- It suffices to show that `∑' k, μ (S (k + 1) \ S k) ≠ ∞`. Indeed, if we have this,
  then for all `N` we have `μ (⋃ n, S n) ≤ μ (S N) + ∑' k, m (S (N + k + 1) \ S (N + k))`
  and the second term tends to zero, see `outer_measure.Union_nat_of_monotone_of_tsum_ne_top`
  for details. -/
  have : ∀ n, S n ⊆ S (n + 1), from λ n x hx,
    ⟨hx.1, le_trans (ennreal.inv_le_inv.2 $ ennreal.coe_nat_le_coe_nat.2 n.le_succ) hx.2⟩,
  refine (μ.Union_nat_of_monotone_of_tsum_ne_top this _).le, clear this,
  /- While the sets `S (k + 1) \ S k` are not pairwise metric separated, the sets in each
  subsequence `S (2 * k + 1) \ S (2 * k)` and `S (2 * k + 2) \ S (2 * k)` are metric separated,
  so `m` is additive on each of those sequences. -/
  rw [← tsum_even_add_odd ennreal.summable ennreal.summable, ennreal.add_ne_top],
  suffices : ∀ a, (∑' (k : ℕ), μ (S (2 * k + 1 + a) \ S (2 * k + a))) ≠ ∞,
    from ⟨by simpa using this 0, by simpa using this 1⟩,
  refine λ r, ne_top_of_le_ne_top htop _,
  rw [← Union_S, ennreal.tsum_eq_supr_nat, supr_le_iff],
  intro n,
  rw [← hm.finset_Union_of_pairwise_separated],
  { exact μ.mono (Union_subset $ λ i, Union_subset $ λ hi x hx, mem_Union.2 ⟨_, hx.1⟩) },
  suffices : ∀ i  j, i < j → is_metric_separated (S (2 * i + 1 + r)) (s \ S (2 * j + r)),
    from λ i _ j _ hij, hij.lt_or_lt.elim
      (λ h, (this i j h).mono (inter_subset_left _ _) (λ x hx, ⟨hx.1.1, hx.2⟩))
      (λ h, (this j i h).symm.mono  (λ x hx, ⟨hx.1.1, hx.2⟩) (inter_subset_left _ _)),
  intros i j hj,
  have A : ((↑(2 * j + r))⁻¹ : ℝ≥0∞) < (↑(2 * i + 1 + r))⁻¹,
    by { rw [ennreal.inv_lt_inv, ennreal.coe_nat_lt_coe_nat], linarith },
  refine ⟨(↑(2 * i + 1 + r))⁻¹ - (↑(2 * j + r))⁻¹, by simpa using A, λ x hx y hy, _⟩,
  have : inf_edist y t < (↑(2 * j + r))⁻¹, from not_le.1 (λ hle, hy.2 ⟨hy.1, hle⟩),
  rcases exists_edist_lt_of_inf_edist_lt this with ⟨z, hzt, hyz⟩,
  have hxz : (↑(2 * i + 1 + r))⁻¹ ≤ edist x z, from le_inf_edist.1 hx.2 _ hzt,
  apply ennreal.le_of_add_le_add_right (hyz.trans_le le_top),
  refine le_trans _ (edist_triangle _ _ _),
  refine (add_le_add le_rfl hyz.le).trans (eq.trans_le _ hxz),
  rw [ennreal.sub_add_cancel_of_le A.le]
end

lemma le_caratheodory [measurable_space X] [borel_space X] (hm : is_metric μ) :
  ‹measurable_space X› ≤ μ.caratheodory :=
by { rw @borel_space.measurable_eq X _ _, exact hm.borel_le_caratheodory }

end is_metric

/-!
### Constructors of metric outer measures

In this section we provide constructors `measure_theory.outer_measure.mk_metric'` and
`measure_theory.outer_measure.mk_metric` and prove that these outer measures are metric outer
measures. We also prove basic lemmas about `map`/`comap` of these measures.
-/

/-- Auxiliary definition for `outer_measure.mk_metric'`: given a function on sets
`m : set X → ℝ≥0∞`, returns the maximal outer measure `μ` such that `μ s ≤ m s`
for any set `s` of diameter at most `r`.-/
def mk_metric'.pre (m : set X → ℝ≥0∞) (r : ℝ≥0∞) :
  outer_measure X :=
bounded_by $ extend (λ s (hs : diam s ≤ r), m s)

/-- Given a function `m : set X → ℝ≥0∞`, `mk_metric' m` is the supremum of `mk_metric'.pre m r`
over `r > 0`. Equivalently, it is the limit of `mk_metric'.pre m r` as `r` tends to zero from
the right. -/
def mk_metric' (m : set X → ℝ≥0∞) :
  outer_measure X :=
⨆ r > 0, mk_metric'.pre m r

/-- Given a function `m : ℝ≥0∞ → ℝ≥0∞` and `r > 0`, let `μ r` be the maximal outer measure such that
`μ s = 0` on subsingletons and `μ s ≤ m (emetric.diam s)` whenever `emetric.diam s < r`. Then
`mk_metric m = ⨆ r > 0, μ r`. We add `⨆ (hs : ¬s.subsingleton)` to ensure that in the case
`m x = x ^ d` the definition gives the expected result for `d = 0`. -/
def mk_metric (m : ℝ≥0∞ → ℝ≥0∞) : outer_measure X :=
mk_metric' (λ s, ⨆ (hs : ¬s.subsingleton), m (diam s))

namespace mk_metric'

variables {m : set X → ℝ≥0∞} {r : ℝ≥0∞} {μ : outer_measure X} {s : set X}

lemma le_pre : μ ≤ pre m r ↔ ∀ s : set X, diam s ≤ r → μ s ≤ m s :=
by simp only [pre, le_bounded_by, extend, le_infi_iff]

lemma pre_le (hs : diam s ≤ r) : pre m r s ≤ m s :=
(bounded_by_le _).trans $ infi_le _ hs

lemma mono_pre (m : set X → ℝ≥0∞) {r r' : ℝ≥0∞} (h : r ≤ r') :
  pre m r' ≤ pre m r :=
le_pre.2 $ λ s hs, pre_le (hs.trans h)

lemma mono_pre_nat (m : set X → ℝ≥0∞) :
  monotone (λ k : ℕ, pre m k⁻¹) :=
λ k l h, le_pre.2 $ λ s hs, pre_le (hs.trans $ by simpa)

lemma tendsto_pre (m : set X → ℝ≥0∞) (s : set X) :
  tendsto (λ r, pre m r s) (𝓝[Ioi 0] 0) (𝓝 $ mk_metric' m s) :=
begin
  rw [← map_coe_Ioi_at_bot, tendsto_map'_iff],
  simp only [mk_metric', outer_measure.supr_apply, supr_subtype'],
  exact tendsto_at_bot_supr (λ r r' hr, mono_pre _ hr _)
end

lemma tendsto_pre_nat (m : set X → ℝ≥0∞) (s : set X) :
  tendsto (λ n : ℕ, pre m n⁻¹ s) at_top (𝓝 $ mk_metric' m s) :=
begin
  refine (tendsto_pre m s).comp (tendsto_inf.2 ⟨ennreal.tendsto_inv_nat_nhds_zero, _⟩),
  refine tendsto_principal.2 (eventually_of_forall $ λ n, _),
  simp
end

lemma eq_supr_nat (m : set X → ℝ≥0∞) :
  mk_metric' m = ⨆ n : ℕ, mk_metric'.pre m n⁻¹ :=
begin
  ext1 s,
  rw supr_apply,
  refine tendsto_nhds_unique (mk_metric'.tendsto_pre_nat m s)
    (tendsto_at_top_supr $ λ k l hkl, mk_metric'.mono_pre_nat m hkl s)
end

/-- `measure_theory.outer_measure.mk_metric'.pre m r` is a trimmed measure provided that
`m (closure s) = m s` for any set `s`. -/
lemma trim_pre [measurable_space X] [opens_measurable_space X]
  (m : set X → ℝ≥0∞) (hcl : ∀ s, m (closure s) = m s) (r : ℝ≥0∞) :
  (pre m r).trim = pre m r :=
begin
  refine le_antisymm (le_pre.2 $ λ s hs, _) (le_trim _),
  rw trim_eq_infi,
  refine (infi_le_of_le (closure s) $ infi_le_of_le subset_closure $
    infi_le_of_le measurable_set_closure ((pre_le _).trans_eq (hcl _))),
  rwa diam_closure
end

end mk_metric'

/-- An outer measure constructed using `outer_measure.mk_metric'` is a metric outer measure. -/
lemma mk_metric'_is_metric (m : set X → ℝ≥0∞) :
  (mk_metric' m).is_metric :=
begin
  rintros s t ⟨r, r0, hr⟩,
  refine tendsto_nhds_unique_of_eventually_eq
    (mk_metric'.tendsto_pre _ _)
    ((mk_metric'.tendsto_pre _ _).add (mk_metric'.tendsto_pre _ _)) _,
  rw [← pos_iff_ne_zero] at r0,
  filter_upwards [Ioo_mem_nhds_within_Ioi ⟨le_rfl, r0⟩],
  rintro ε ⟨ε0, εr⟩,
  refine bounded_by_union_of_top_of_nonempty_inter _,
  rintro u ⟨x, hxs, hxu⟩ ⟨y, hyt, hyu⟩,
  have : ε < diam u, from εr.trans_le ((hr x hxs y hyt).trans $ edist_le_diam_of_mem hxu hyu),
  exact infi_eq_top.2 (λ h, (this.not_le h).elim)
end

/-- If `c ∉ {0, ∞}` and `m₁ d ≤ c * m₂ d` for `0 < d < ε` for some `ε > 0`
(we use `≤ᶠ[𝓝[Ioi 0]]` to state this), then `mk_metric m₁ hm₁ ≤ c • mk_metric m₂ hm₂`. -/
lemma mk_metric_mono_smul {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (h0 : c ≠ 0)
  (hle : m₁ ≤ᶠ[𝓝[Ioi 0] 0] c • m₂) :
  (mk_metric m₁ : outer_measure X) ≤ c • mk_metric m₂ :=
begin
  classical,
  rcases (mem_nhds_within_Ioi_iff_exists_Ioo_subset' ennreal.zero_lt_one).1 hle with ⟨r, hr0, hr⟩,
  refine λ s, le_of_tendsto_of_tendsto (mk_metric'.tendsto_pre _ s)
    (ennreal.tendsto.const_mul (mk_metric'.tendsto_pre _ s) (or.inr hc))
    (mem_of_superset (Ioo_mem_nhds_within_Ioi ⟨le_rfl, hr0⟩) (λ r' hr', _)),
  simp only [mem_set_of_eq, mk_metric'.pre],
  rw [← smul_apply, smul_bounded_by hc],
  refine le_bounded_by.2 (λ t, (bounded_by_le _).trans _) _,
  simp only [smul_eq_mul, pi.smul_apply, extend, infi_eq_if],
  split_ifs with ht ht,
  { refine supr_le (λ ht₁, _),
    rw [supr_eq_if, if_pos ht₁],
    refine hr ⟨_, ht.trans_lt hr'.2⟩,
    exact pos_iff_ne_zero.2 (mt diam_eq_zero_iff.1 ht₁) },
  { simp [h0] }
end

/-- If `m₁ d ≤ m₂ d` for `0 < d < ε` for some `ε > 0` (we use `≤ᶠ[𝓝[Ioi 0]]` to state this), then
`mk_metric m₁ hm₁ ≤ mk_metric m₂ hm₂`-/
lemma mk_metric_mono {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} (hle : m₁ ≤ᶠ[𝓝[Ioi 0] 0] m₂) :
  (mk_metric m₁ : outer_measure X) ≤ mk_metric m₂ :=
by { convert mk_metric_mono_smul ennreal.one_ne_top ennreal.zero_lt_one.ne' _; simp * }

lemma isometry_comap_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) {f : X → Y} (hf : isometry f)
  (H : monotone (λ d : {d : ℝ≥0∞ | d ≠ 0}, m d) ∨ surjective f) :
  comap f (mk_metric m) = mk_metric m :=
begin
  simp only [mk_metric, mk_metric', mk_metric'.pre, induced_outer_measure, comap_supr],
  refine supr_congr id surjective_id (λ ε, supr_congr id surjective_id $ λ hε, _),
  rw comap_bounded_by _ (H.imp (λ h_mono, _) id),
  { congr' with s : 1,
    apply extend_congr,
    { simp [hf.ediam_image] },
    { intros, simp [hf.injective.subsingleton_image_iff, hf.ediam_image] } },
  { refine λ s t hst, infi_le_infi2 (λ ht, ⟨(diam_mono hst).trans ht, supr_le $ λ hs, _⟩),
    have ht : ¬(t : set Y).subsingleton, from λ ht, hs (ht.mono hst),
    refine (@h_mono ⟨_, mt diam_eq_zero_iff.1 hs⟩ ⟨_, mt diam_eq_zero_iff.1 ht⟩
      (diam_mono hst)).trans _,
    exact le_supr (λ h : ¬(t : set Y).subsingleton, m (diam (t : set Y))) ht }
end

lemma isometry_map_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) {f : X → Y} (hf : isometry f)
  (H : monotone (λ d : {d : ℝ≥0∞ | d ≠ 0}, m d) ∨ surjective f) :
  map f (mk_metric m) = restrict (range f) (mk_metric m) :=
by rw [← isometry_comap_mk_metric _ hf H, map_comap]

lemma isometric_comap_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (f : X ≃ᵢ Y) :
  comap f (mk_metric m) = mk_metric m :=
isometry_comap_mk_metric _ f.isometry (or.inr f.surjective)

lemma isometric_map_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (f : X ≃ᵢ Y) :
  map f (mk_metric m) = mk_metric m :=
by rw [← isometric_comap_mk_metric _ f, map_comap_of_surjective f.surjective]

lemma trim_mk_metric [measurable_space X] [borel_space X] (m : ℝ≥0∞ → ℝ≥0∞) :
  (mk_metric m : outer_measure X).trim = mk_metric m :=
begin
  simp only [mk_metric, mk_metric'.eq_supr_nat, trim_supr],
  congr' 1 with n : 1,
  refine mk_metric'.trim_pre _ (λ s, _) _,
  simp
end

lemma le_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (μ : outer_measure X) (hμ : ∀ x, μ {x} = 0)
  (r : ℝ≥0∞) (h0 : 0 < r) (hr : ∀ s, diam s ≤ r → ¬s.subsingleton → μ s ≤ m (diam s)) :
  μ ≤ mk_metric m :=
le_bsupr_of_le r h0 $ mk_metric'.le_pre.2 $ λ s hs,
  begin
    by_cases h : s.subsingleton,
    exacts [h.induction_on (μ.empty'.trans_le (zero_le _)) (λ x, ((hμ x).trans_le (zero_le _))),
      le_supr_of_le h (hr _ hs h)]
  end

end outer_measure

/-!
### Metric measures

In this section we use `measure_theory.outer_measure.to_measure` and theorems about
`measure_theory.outer_measure.mk_metric'`/`measure_theory.outer_measure.mk_metric` to define
`measure_theory.measure.mk_metric'`/`measure_theory.measure.mk_metric`. We also restate some lemmas
about metric outer measures for metric measures.
-/

namespace measure

variables [measurable_space X] [borel_space X]

/-- Given a function `m : set X → ℝ≥0∞`, `mk_metric' m` is the supremum of `μ r`
over `r > 0`, where `μ r` is the maximal outer measure `μ` such that `μ s ≤ m s`
for all `s`. While each `μ r` is an *outer* measure, the supremum is a measure. -/
def mk_metric' (m : set X → ℝ≥0∞) : measure X :=
(outer_measure.mk_metric' m).to_measure (outer_measure.mk_metric'_is_metric _).le_caratheodory

/-- Given a function `m : ℝ≥0∞ → ℝ≥0∞`, `mk_metric m` is the supremum of `μ r` over `r > 0`, where
`μ r` is the maximal outer measure `μ` such that `μ s ≤ m s` for all sets `s` that contain at least
two points. While each `mk_metric'.pre` is an *outer* measure, the supremum is a measure. -/
def mk_metric (m : ℝ≥0∞ → ℝ≥0∞) : measure X :=
(outer_measure.mk_metric m).to_measure (outer_measure.mk_metric'_is_metric _).le_caratheodory

@[simp] lemma mk_metric'_to_outer_measure (m : set X → ℝ≥0∞) :
  (mk_metric' m).to_outer_measure = (outer_measure.mk_metric' m).trim :=
rfl

@[simp] lemma mk_metric_to_outer_measure (m : ℝ≥0∞ → ℝ≥0∞) :
  (mk_metric m : measure X).to_outer_measure = outer_measure.mk_metric m :=
outer_measure.trim_mk_metric m

end measure

lemma outer_measure.coe_mk_metric [measurable_space X] [borel_space X] (m : ℝ≥0∞ → ℝ≥0∞) :
  ⇑(outer_measure.mk_metric m : outer_measure X) = measure.mk_metric m :=
by rw [← measure.mk_metric_to_outer_measure, coe_to_outer_measure]

variables [measurable_space X] [borel_space X]

namespace measure

/-- If `c ∉ {0, ∞}` and `m₁ d ≤ c * m₂ d` for `0 < d < ε` for some `ε > 0`
(we use `≤ᶠ[𝓝[Ioi 0]]` to state this), then `mk_metric m₁ hm₁ ≤ c • mk_metric m₂ hm₂`. -/
lemma mk_metric_mono_smul {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (h0 : c ≠ 0)
  (hle : m₁ ≤ᶠ[𝓝[Ioi 0] 0] c • m₂) :
  (mk_metric m₁ : measure X) ≤ c • mk_metric m₂ :=
begin
  intros s hs,
  rw [← outer_measure.coe_mk_metric, coe_smul, ← outer_measure.coe_mk_metric],
  exact outer_measure.mk_metric_mono_smul hc h0 hle s
end

/-- If `m₁ d ≤ m₂ d` for `0 < d < ε` for some `ε > 0` (we use `≤ᶠ[𝓝[Ioi 0]]` to state this), then
`mk_metric m₁ hm₁ ≤ mk_metric m₂ hm₂`-/
lemma mk_metric_mono {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} (hle : m₁ ≤ᶠ[𝓝[Ioi 0] 0] m₂) :
  (mk_metric m₁ : measure X) ≤ mk_metric m₂ :=
by { convert mk_metric_mono_smul ennreal.one_ne_top ennreal.zero_lt_one.ne' _; simp * }

/-- A formula for `measure_theory.measure.mk_metric`. -/
lemma mk_metric_apply (m : ℝ≥0∞ → ℝ≥0∞) (s : set X) :
  mk_metric m s = ⨆ (r : ℝ≥0∞) (hr : 0 < r), ⨅ (t : ℕ → set X) (hts : s ⊆ ⋃ n, t n)
    (ht : ∀ n, diam (t n) ≤ r), ∑' n, ⨆ (ht : ¬(t n).subsingleton), m (diam (t n)) :=
begin
  -- We mostly unfold the definitions but we need to switch the order of `∑'` and `⨅`
  -- and merge `(t n).nonempty` with `¬subsingleton (t n)`
  classical,
  simp only [← outer_measure.coe_mk_metric, outer_measure.mk_metric, outer_measure.mk_metric',
    outer_measure.supr_apply, outer_measure.mk_metric'.pre, outer_measure.bounded_by_apply,
    extend],
  refine supr_congr (λ r, r) surjective_id (λ r, supr_congr_Prop iff.rfl $ λ hr,
    infi_congr _ surjective_id $ λ t, infi_congr_Prop iff.rfl $ λ ht, _),
  by_cases htr : ∀ n, diam (t n) ≤ r,
  { rw [infi_eq_if, if_pos htr],
    congr' 1 with n : 1,
    simp only [infi_eq_if, htr n, id, if_true, supr_and'],
    refine supr_congr_Prop (and_iff_right_of_imp $ λ h, _) (λ _, rfl),
    contrapose! h,
    rw [not_nonempty_iff_eq_empty.1 h],
    exact subsingleton_empty },
  { rw [infi_eq_if, if_neg htr],
    push_neg at htr, rcases htr with ⟨n, hn⟩,
    refine ennreal.tsum_eq_top_of_eq_top ⟨n, _⟩,
    rw [supr_eq_if, if_pos, infi_eq_if, if_neg],
    exact hn.not_le,
    rcases diam_pos_iff.1 ((zero_le r).trans_lt hn) with ⟨x, hx, -⟩,
    exact ⟨x, hx⟩ }
end

lemma le_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (μ : measure X) [has_no_atoms μ] (ε : ℝ≥0∞) (h₀ : 0 < ε)
  (h : ∀ s : set X, diam s ≤ ε → ¬s.subsingleton → μ s ≤ m (diam s)) :
  μ ≤ mk_metric m :=
begin
  rw [← to_outer_measure_le, mk_metric_to_outer_measure],
  exact outer_measure.le_mk_metric m μ.to_outer_measure measure_singleton ε h₀ h
end

/-- To bound the Hausdorff measure (or, more generally, for a measure defined using
`measure_theory.measure.mk_metric`) of a set, one may use coverings with maximum diameter tending to
`0`, indexed by any sequence of encodable types. -/
lemma mk_metric_le_liminf_tsum {β : Type*} {ι : β → Type*} [∀ n, encodable (ι n)] (s : set X)
  {l : filter β} (r : β → ℝ≥0∞) (hr : tendsto r l (𝓝 0)) (t : Π (n : β), ι n → set X)
  (ht : ∀ᶠ n in l, ∀ i, diam (t n i) ≤ r n) (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i)
  (m : ℝ≥0∞ → ℝ≥0∞) :
  mk_metric m s ≤ liminf l (λ n, ∑' i, m (diam (t n i))) :=
begin
  simp only [mk_metric_apply],
  refine bsupr_le (λ ε hε, _),
  refine le_of_forall_le_of_dense (λ c hc, _),
  rcases ((frequently_lt_of_liminf_lt (by apply_auto_param) hc).and_eventually
    ((hr.eventually (gt_mem_nhds hε)).and (ht.and hst))).exists with ⟨n, hn, hrn, htn, hstn⟩,
  set u : ℕ → set X := λ j, ⋃ b ∈ decode₂ (ι n) j, t n b,
  refine binfi_le_of_le u (by rwa Union_decode₂) _,
  refine infi_le_of_le (λ j, _) _,
  { rw emetric.diam_Union_mem_option,
    exact bsupr_le (λ _ _, (htn _).trans hrn.le) },
  { calc (∑' (j : ℕ), ⨆ (ht : ¬(u j).subsingleton), m (diam (u j))) = _ :
              tsum_Union_decode₂ (λ t : set X, ⨆ (h : ¬t.subsingleton), m (diam t)) (by simp) _
    ... ≤ _ : ennreal.tsum_le_tsum (λ b, supr_le $ λ htb, le_rfl)
    ... ≤ c : hn.le }
end

/-- To bound the Hausdorff measure (or, more generally, for a measure defined using
`measure_theory.measure.mk_metric`) of a set, one may use coverings with maximum diameter tending to
`0`, indexed by any sequence of finite types. -/
lemma mk_metric_le_liminf_sum {β : Type*} {ι : β → Type*} [hι : ∀ n, fintype (ι n)] (s : set X)
  {l : filter β} (r : β → ℝ≥0∞) (hr : tendsto r l (𝓝 0)) (t : Π (n : β), ι n → set X)
  (ht : ∀ᶠ n in l, ∀ i, diam (t n i) ≤ r n) (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i)
  (m : ℝ≥0∞ → ℝ≥0∞) :
  mk_metric m s ≤ liminf l (λ n, ∑ i, m (diam (t n i))) :=
begin
  haveI : ∀ n, encodable (ι n), from λ n, fintype.encodable _,
  simpa only [tsum_fintype] using mk_metric_le_liminf_tsum s r hr t ht hst m,
end

/-!
### Hausdorff measure and Hausdorff dimension
-/

/-- Hausdorff measure on an (e)metric space. -/
def hausdorff_measure (d : ℝ) : measure X := mk_metric (λ r, r ^ d)

localized "notation `μH[` d `]` := measure_theory.measure.hausdorff_measure d" in measure_theory

lemma le_hausdorff_measure (d : ℝ) (μ : measure X) [has_no_atoms μ] (ε : ℝ≥0∞) (h₀ : 0 < ε)
  (h : ∀ s : set X, diam s ≤ ε → ¬s.subsingleton → μ s ≤ diam s ^ d) :
  μ ≤ μH[d] :=
le_mk_metric _ μ ε h₀ h

/-- A formula for `μH[d] s` that works for all `d`. In case of a positive `d` a simpler formula
is available as `measure_theory.measure.hausdorff_measure_apply`. -/
lemma hausdorff_measure_apply' (d : ℝ) (s : set X) :
  μH[d] s = ⨆ (r : ℝ≥0∞) (hr : 0 < r), ⨅ (t : ℕ → set X) (hts : s ⊆ ⋃ n, t n)
    (ht : ∀ n, diam (t n) ≤ r), ∑' n, ⨆ (ht : ¬(t n).subsingleton), (diam (t n)) ^ d :=
mk_metric_apply _ _

/-- A formula for `μH[d] s` that works for all positive `d`. -/
lemma hausdorff_measure_apply {d : ℝ} (hd : 0 < d) (s : set X) :
  μH[d] s = ⨆ (r : ℝ≥0∞) (hr : 0 < r), ⨅ (t : ℕ → set X) (hts : s ⊆ ⋃ n, t n)
    (ht : ∀ n, diam (t n) ≤ r), ∑' n, diam (t n) ^ d :=
begin
  classical,
  rw hausdorff_measure_apply',
  -- I wish `congr'` was able to generate this
  refine supr_congr id surjective_id (λ r, supr_congr_Prop iff.rfl $ λ hr,
    infi_congr id surjective_id $ λ t, infi_congr_Prop iff.rfl $ λ hts,
    infi_congr_Prop iff.rfl $ λ ht, tsum_congr $ λ n, _),
  rw [supr_eq_if], split_ifs with ht',
  { erw [diam_eq_zero_iff.2 ht', ennreal.zero_rpow_of_pos hd, ennreal.bot_eq_zero] },
  { refl }
end

/-- To bound the Hausdorff measure of a set, one may use coverings with maximum diameter tending
to `0`, indexed by any sequence of encodable types. -/
lemma hausdorff_measure_le_liminf_tsum {β : Type*}  {ι : β → Type*} [hι : ∀ n, encodable (ι n)]
  (d : ℝ) (s : set X)
  {l : filter β} (r : β → ℝ≥0∞) (hr : tendsto r l (𝓝 0)) (t : Π (n : β), ι n → set X)
  (ht : ∀ᶠ n in l, ∀ i, diam (t n i) ≤ r n) (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i) :
  μH[d] s ≤ liminf l (λ n, ∑' i, diam (t n i) ^ d) :=
mk_metric_le_liminf_tsum s r hr t ht hst _

/-- To bound the Hausdorff measure of a set, one may use coverings with maximum diameter tending
to `0`, indexed by any sequence of finite types. -/
lemma hausdorff_measure_le_liminf_sum {β : Type*}  {ι : β → Type*} [hι : ∀ n, fintype (ι n)]
  (d : ℝ) (s : set X)
  {l : filter β} (r : β → ℝ≥0∞) (hr : tendsto r l (𝓝 0)) (t : Π (n : β), ι n → set X)
  (ht : ∀ᶠ n in l, ∀ i, diam (t n i) ≤ r n) (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i) :
  μH[d] s ≤ liminf l (λ n, ∑ i, diam (t n i) ^ d) :=
mk_metric_le_liminf_sum s r hr t ht hst _

/-- If `d₁ < d₂`, then for any set `s` we have either `μH[d₂] s = 0`, or `μH[d₁] s = ∞`. -/
lemma hausdorff_measure_zero_or_top {d₁ d₂ : ℝ} (h : d₁ < d₂) (s : set X) :
  μH[d₂] s = 0 ∨ μH[d₁] s = ∞ :=
begin
  by_contra H, push_neg at H,
  suffices : ∀ (c : ℝ≥0), c ≠ 0 → μH[d₂] s ≤ c * μH[d₁] s,
  { rcases ennreal.exists_nnreal_pos_mul_lt H.2 H.1 with ⟨c, hc0, hc⟩,
    exact hc.not_le (this c (pos_iff_ne_zero.1 hc0)) },
  intros c hc,
  refine le_iff'.1 (mk_metric_mono_smul ennreal.coe_ne_top (by exact_mod_cast hc) _) s,
  have : 0 <  (c ^ (d₂ - d₁)⁻¹ : ℝ≥0∞),
  { rw [ennreal.coe_rpow_of_ne_zero hc, pos_iff_ne_zero, ne.def, ennreal.coe_eq_zero,
      nnreal.rpow_eq_zero_iff],
    exact mt and.left hc },
  filter_upwards [Ioo_mem_nhds_within_Ioi ⟨le_rfl, this⟩],
  rintro r ⟨hr₀, hrc⟩,
  lift r to ℝ≥0 using ne_top_of_lt hrc,
  rw [pi.smul_apply, smul_eq_mul, ← ennreal.div_le_iff_le_mul (or.inr ennreal.coe_ne_top)
    (or.inr $ mt ennreal.coe_eq_zero.1 hc), ← ennreal.rpow_sub _ _ hr₀.ne' ennreal.coe_ne_top],
  refine (ennreal.rpow_lt_rpow hrc (sub_pos.2 h)).le.trans _,
  rw [← ennreal.rpow_mul, inv_mul_cancel (sub_pos.2 h).ne', ennreal.rpow_one],
  exact le_rfl
end

/-- Hausdorff measure `μH[d] s` is monotone in `d`. -/
lemma hausdorff_measure_mono {d₁ d₂ : ℝ} (h : d₁ ≤ d₂) (s : set X) : μH[d₂] s ≤ μH[d₁] s :=
begin
  rcases h.eq_or_lt with rfl|h, { exact le_rfl },
  cases hausdorff_measure_zero_or_top h s with hs hs,
  { rw hs, exact zero_le _ },
  { rw hs, exact le_top }
end

instance no_atoms_hausdorff (d : ℝ) : has_no_atoms (hausdorff_measure d : measure X) :=
begin
  refine ⟨λ x, _⟩,
  rw [← nonpos_iff_eq_zero, hausdorff_measure_apply'],
  refine bsupr_le (λ ε ε0, binfi_le_of_le (λ n, {x}) _ (infi_le_of_le (λ n, _) _)),
  { exact subset_Union (λ n, {x} : ℕ → set X) 0 },
  { simp only [emetric.diam_singleton, zero_le] },
  { simp }
end

end measure

open_locale measure_theory
open measure

/-- Hausdorff dimension of a set in an (e)metric space. -/
def dimH (s : set X) : ℝ≥0∞ := ⨆ (d : ℝ≥0) (hd : μH[d] s = ∞), d

lemma dimH_subsingleton {s : set X} (h : s.subsingleton) : dimH s = 0 :=
by simp [dimH, h.measure_zero]

alias dimH_subsingleton ← set.subsingleton.dimH_zero

@[simp] lemma dimH_empty : dimH (∅ : set X) = 0 := subsingleton_empty.dimH_zero

@[simp] lemma dimH_singleton (x : X) : dimH ({x} : set X) = 0 := subsingleton_singleton.dimH_zero

lemma hausdorff_measure_of_lt_dimH {s : set X} {d : ℝ≥0}
  (h : ↑d < dimH s) : μH[d] s = ∞ :=
begin
  simp only [dimH, lt_supr_iff] at h,
  rcases h with ⟨d', hsd', hdd'⟩,
  rw [ennreal.coe_lt_coe, ← nnreal.coe_lt_coe] at hdd',
  refine (hausdorff_measure_zero_or_top hdd' s).resolve_left (λ h, _),
  exact (ennreal.zero_ne_top $ h.symm.trans hsd').elim
end

lemma dimH_le_of_hausdorff_measure_ne_top {s : set X} {d : ℝ≥0} (h : μH[d] s ≠ ∞) :
  dimH s ≤ d :=
le_of_not_lt $ mt hausdorff_measure_of_lt_dimH h

lemma le_dimH_of_hausdorff_measure_eq_top {s : set X} {d : ℝ≥0} (h : μH[d] s = ∞) :
  ↑d ≤ dimH s :=
le_bsupr d h

lemma hausdorff_measure_of_dimH_lt {s : set X} {d : ℝ≥0}
  (h : dimH s < d) : μH[d] s = 0 :=
begin
  rcases ennreal.lt_iff_exists_nnreal_btwn.1 h with ⟨d', hsd', hd'd⟩,
  rw [ennreal.coe_lt_coe, ← nnreal.coe_lt_coe] at hd'd,
  exact (hausdorff_measure_zero_or_top hd'd s).resolve_right
    (λ h, hsd'.not_le (le_bsupr d' h))
end

lemma measure_zero_of_dimH_lt {μ : measure X} {d : ℝ≥0}
  (h : μ ≪ μH[d]) {s : set X} (hd : dimH s < d) :
  μ s = 0 :=
h $ hausdorff_measure_of_dimH_lt hd

lemma le_dimH_of_hausdorff_measure_ne_zero {s : set X} {d : ℝ≥0} (h : μH[d] s ≠ 0) :
  ↑d ≤ dimH s :=
le_of_not_lt $ mt hausdorff_measure_of_dimH_lt h

lemma dimH_of_hausdorff_measure_ne_zero_ne_top {d : ℝ≥0} {s : set X} (h : μH[d] s ≠ 0)
  (h' : μH[d] s ≠ ∞) : dimH s = d :=
le_antisymm (dimH_le_of_hausdorff_measure_ne_top h') (le_dimH_of_hausdorff_measure_ne_zero h)

@[mono] lemma dimH_mono {s t : set X} (h : s ⊆ t) : dimH s ≤ dimH t :=
bsupr_le $ λ d hd, le_dimH_of_hausdorff_measure_eq_top $
  top_unique $ hd ▸ measure_mono h

@[simp] lemma dimH_Union [encodable ι] (s : ι → set X) :
  dimH (⋃ i, s i) = ⨆ i, dimH (s i) :=
begin
  refine le_antisymm (bsupr_le $ λ d hd, _) (supr_le $ λ i, dimH_mono $ subset_Union _ _),
  contrapose! hd,
  have : ∀ i, μH[d] (s i) = 0,
    from λ i, hausdorff_measure_of_dimH_lt ((le_supr (λ i, dimH (s i)) i).trans_lt hd),
  rw measure_Union_null this,
  exact ennreal.zero_ne_top
end

@[simp] lemma dimH_bUnion {s : set ι} (hs : countable s) (t : ι → set X) :
  dimH (⋃ i ∈ s, t i) = ⨆ i ∈ s, dimH (t i) :=
begin
  haveI := hs.to_encodable,
  rw [← Union_subtype, dimH_Union, ← supr_subtype'']
end

@[simp] lemma dimH_sUnion {S : set (set X)} (hS : countable S) : dimH (⋃₀ S) = ⨆ s ∈ S, dimH s :=
by rw [sUnion_eq_bUnion, dimH_bUnion hS]

@[simp] lemma dimH_union (s t : set X) : dimH (s ∪ t) = max (dimH s) (dimH t) :=
by rw [union_eq_Union, dimH_Union, supr_bool_eq, cond, cond, ennreal.sup_eq_max]

lemma dimH_countable {s : set X} (hs : countable s) : dimH s = 0 :=
bUnion_of_singleton s ▸ by simp only [dimH_bUnion hs, dimH_singleton, ennreal.supr_zero_eq_zero]

alias dimH_countable ← set.countable.dimH_zero

/-!
### Hausdorff measure and Lebesgue measure
-/

/-- In the space `ι → ℝ`, Hausdorff measure coincides exactly with Lebesgue measure. -/
@[simp] theorem hausdorff_measure_pi_real {ι : Type*} [fintype ι] [nonempty ι] :
  (μH[fintype.card ι] : measure (ι → ℝ)) = volume :=
begin
  classical,
  -- it suffices to check that the two measures coincide on products of rational intervals
  refine (pi_eq_generate_from (λ i, real.borel_eq_generate_from_Ioo_rat.symm)
    (λ i, real.is_pi_system_Ioo_rat) (λ i, real.finite_spanning_sets_in_Ioo_rat _)
    _).symm,
  simp only [mem_Union, mem_singleton_iff],
  -- fix such a product `s` of rational intervals, of the form `Π (a i, b i)`.
  intros s hs,
  choose a b H using hs,
  obtain rfl : s = λ i, Ioo (a i) (b i), from funext (λ i, (H i).2), replace H := λ i, (H i).1,
  apply le_antisymm _,
  -- first check that `volume s ≤ μH s`
  { have Hle : volume ≤ (μH[fintype.card ι] : measure (ι → ℝ)),
    { refine le_hausdorff_measure _ _ ∞ ennreal.coe_lt_top (λ s h₁ h₂, _),
      rw [ennreal.rpow_nat_cast],
      exact real.volume_pi_le_diam_pow s },
    rw [← volume_pi_pi (λ i, Ioo (a i : ℝ) (b i)) (λ i, measurable_set_Ioo)],
    exact measure.le_iff'.1 Hle _ },
  /- For the other inequality `μH s ≤ volume s`, we use a covering of `s` by sets of small diameter
  `1/n`, namely cubes with left-most point of the form `a i + f i / n` with `f i` ranging between
  `0` and `⌈(b i - a i) * n⌉`. Their number is asymptotic to `n^d * Π (b i - a i)`. -/
  have I : ∀ i, 0 ≤ (b i : ℝ) - a i := λ i, by simpa only [sub_nonneg, rat.cast_le] using (H i).le,
  let γ := λ (n : ℕ), (Π (i : ι), fin ⌈((b i : ℝ) - a i) * n⌉₊),
  let t : Π (n : ℕ), γ n → set (ι → ℝ) :=
    λ n f, set.pi univ (λ i, Icc (a i + f i / n) (a i + (f i + 1) / n)),
  have A : tendsto (λ (n : ℕ), 1/(n : ℝ≥0∞)) at_top (𝓝 0),
    by simp only [one_div, ennreal.tendsto_inv_nat_nhds_zero],
  have B : ∀ᶠ n in at_top, ∀ (i : γ n), diam (t n i) ≤ 1 / n,
  { apply eventually_at_top.2 ⟨1, λ n hn, _⟩,
    assume f,
    apply diam_pi_le_of_le (λ b, _),
    simp only [real.ediam_Icc, add_div, ennreal.of_real_div_of_pos (nat.cast_pos.mpr hn), le_refl,
      add_sub_add_left_eq_sub, add_sub_cancel', ennreal.of_real_one, ennreal.of_real_coe_nat] },
  have C : ∀ᶠ n in at_top, set.pi univ (λ (i : ι), Ioo (a i : ℝ) (b i)) ⊆ ⋃ (i : γ n), t n i,
  { apply eventually_at_top.2 ⟨1, λ n hn, _⟩,
    have npos : (0 : ℝ) < n := nat.cast_pos.2 hn,
    assume x hx,
    simp only [mem_Ioo, mem_univ_pi] at hx,
    simp only [mem_Union, mem_Ioo, mem_univ_pi, coe_coe],
    let f : γ n := λ i, ⟨⌊(x i - a i) * n⌋₊,
    begin
      apply nat_floor_lt_nat_ceil_of_lt_of_pos,
      { refine (mul_lt_mul_right npos).2 _,
        simp only [(hx i).right, sub_lt_sub_iff_right] },
      { refine mul_pos _ npos,
        simpa only [rat.cast_lt, sub_pos] using H i }
    end⟩,
    refine ⟨f, λ i, ⟨_, _⟩⟩,
    { calc (a i : ℝ) + ⌊(x i - a i) * n⌋₊ / n
      ≤ (a i : ℝ) + ((x i - a i) * n) / n :
          begin
            refine add_le_add le_rfl ((div_le_div_right npos).2 _),
            exact nat_floor_le (mul_nonneg (sub_nonneg.2 (hx i).1.le) npos.le),
          end
      ... = x i : by field_simp [npos.ne'] },
    { calc x i
      = (a i : ℝ) + ((x i - a i) * n) / n : by field_simp [npos.ne']
      ... ≤ (a i : ℝ) + (⌊(x i - a i) * n⌋₊ + 1) / n :
        add_le_add le_rfl ((div_le_div_right npos).2 (lt_nat_floor_add_one _).le) } },
  calc μH[fintype.card ι] (set.pi univ (λ (i : ι), Ioo (a i : ℝ) (b i)))
    ≤ liminf at_top (λ (n : ℕ), ∑ (i : γ n), diam (t n i) ^ ↑(fintype.card ι)) :
      hausdorff_measure_le_liminf_sum _ (set.pi univ (λ i, Ioo (a i : ℝ) (b i)))
        (λ (n : ℕ), 1/(n : ℝ≥0∞)) A t B C
  ... ≤ liminf at_top (λ (n : ℕ), ∑ (i : γ n), (1/n) ^ (fintype.card ι)) :
    begin
      refine liminf_le_liminf _ (by is_bounded_default),
      filter_upwards [B],
      assume n hn,
      apply finset.sum_le_sum (λ i _, _),
      rw ennreal.rpow_nat_cast,
      exact pow_le_pow_of_le_left' (hn i) _,
    end
  ... = liminf at_top (λ (n : ℕ), ∏ (i : ι), (⌈((b i : ℝ) - a i) * n⌉₊ : ℝ≥0∞) / n) :
  begin
    simp only [finset.card_univ, nat.cast_prod, one_mul, fintype.card_fin,
      finset.sum_const, nsmul_eq_mul, fintype.card_pi, div_eq_mul_inv, finset.prod_mul_distrib,
      finset.prod_const]
  end
  ... = ∏ (i : ι), volume (Ioo (a i : ℝ) (b i)) :
  begin
    simp only [real.volume_Ioo],
    apply tendsto.liminf_eq,
    refine ennreal.tendsto_finset_prod_of_ne_top _ (λ i hi, _) (λ i hi, _),
    { apply tendsto.congr' _ ((ennreal.continuous_of_real.tendsto _).comp
        ((tendsto_nat_ceil_mul_div_at_top (I i)).comp tendsto_coe_nat_at_top_at_top)),
      apply eventually_at_top.2 ⟨1, λ n hn, _⟩,
      simp only [ennreal.of_real_div_of_pos (nat.cast_pos.mpr hn), comp_app,
        ennreal.of_real_coe_nat] },
    { simp only [ennreal.of_real_ne_top, ne.def, not_false_iff] }
  end
end

end measure_theory

/-!
### Hausdorff measure, Hausdorff dimension, and Hölder or Lipschitz continuous maps
-/

open_locale measure_theory
open measure_theory measure_theory.measure

variables [measurable_space X] [borel_space X] [measurable_space Y] [borel_space Y]

namespace holder_on_with

variables {C r : ℝ≥0} {f : X → Y} {s t : set X}

/-- If `f : X → Y` is Hölder continuous on `s` with a positive exponent `r`, then
`μH[d] (f '' s) ≤ C ^ d * μH[r * d] s`. -/
lemma hausdorff_measure_image_le (h : holder_on_with C r f s) (hr : 0 < r) {d : ℝ} (hd : 0 ≤ d) :
  μH[d] (f '' s) ≤ C ^ d * μH[r * d] s :=
begin
  -- We start with the trivial case `C = 0`
  rcases (zero_le C).eq_or_lt with rfl|hC0,
  { have : (f '' s).subsingleton, by simpa [diam_eq_zero_iff] using h.ediam_image_le,
    rw this.measure_zero,
    exact zero_le _ },
  { have hCd0 : (C : ℝ≥0∞) ^ d ≠ 0, by simp [hC0.ne'],
    have hCd : (C : ℝ≥0∞) ^ d ≠ ∞, by simp [hd],
    simp only [hausdorff_measure_apply', ennreal.mul_supr, ennreal.mul_infi_of_ne hCd0 hCd,
      ← ennreal.tsum_mul_left],
    refine supr_le (λ R, supr_le $ λ hR, _),
    have : tendsto (λ d : ℝ≥0∞, (C : ℝ≥0∞) * d ^ (r : ℝ)) (𝓝 0) (𝓝 0),
      from ennreal.tendsto_const_mul_rpow_nhds_zero_of_pos ennreal.coe_ne_top hr,
    rcases ennreal.nhds_zero_basis_Iic.eventually_iff.1 (this.eventually (gt_mem_nhds hR))
      with ⟨δ, δ0, H⟩,
    refine le_supr_of_le δ (le_supr_of_le δ0 $ le_binfi $ λ t hst, le_infi $ λ htδ, _),
    refine binfi_le_of_le (λ n, f '' (t n ∩ s)) _ (infi_le_of_le (λ n, _) _),
    { rw [← image_Union, ← Union_inter],
      exact image_subset _ (subset_inter hst subset.rfl) },
    { exact (h.ediam_image_inter_le (t n)).trans (H (htδ n)).le },
    { refine ennreal.tsum_le_tsum (λ n, supr_le $ λ hft,
        le_supr_of_le (λ ht, hft $ (ht.mono (inter_subset_left _ _)).image f) _),
      rw [ennreal.rpow_mul, ← ennreal.mul_rpow_of_nonneg _ _ hd],
      exact ennreal.rpow_le_rpow (h.ediam_image_inter_le _) hd } }
end

/-- If `f` is a Hölder continuous map with exponent `r > 0`, then `dimH (f '' s) ≤ dimH s / r`. -/
lemma dimH_image_le (h : holder_on_with C r f s) (hr : 0 < r) :
  dimH (f '' s) ≤ dimH s / r :=
begin
  refine bsupr_le (λ d hd, _),
  have := h.hausdorff_measure_image_le hr d.coe_nonneg,
  rw [hd, ennreal.coe_rpow_of_nonneg _ d.coe_nonneg, top_le_iff] at this,
  have Hrd : μH[(r * d : ℝ≥0)] s = ⊤,
  { contrapose this, exact ennreal.mul_ne_top ennreal.coe_ne_top this },
  rw [ennreal.le_div_iff_mul_le, mul_comm, ← ennreal.coe_mul],
  exacts [le_dimH_of_hausdorff_measure_eq_top Hrd, or.inl (mt ennreal.coe_eq_zero.1 hr.ne'),
    or.inl ennreal.coe_ne_top]
end

end holder_on_with

namespace holder_with

variables {C r : ℝ≥0} {f : X → Y} {s : set X}

/-- If `f : X → Y` is Hölder continuous with a positive exponent `r`, then the Hausdorff dimension
of the image of a set `s` is at most `dimH s / r`. -/
lemma dimH_image_le (h : holder_with C r f) (hr : 0 < r) (s : set X) :
  dimH (f '' s) ≤ dimH s / r :=
(h.holder_on_with s).dimH_image_le hr

/-- If `f` is a Hölder continuous map with exponent `r > 0`, then the Hausdorff dimension of its
range is at most the Hausdorff dimension of its domain divided by `r`. -/
lemma dimH_range_le (h : holder_with C r f) (hr : 0 < r) :
  dimH (range f) ≤ dimH (univ : set X) / r :=
@image_univ _ _ f ▸ h.dimH_image_le hr univ

end holder_with

/-- If `s` is a set in a space `X` with second countable topology and `f : X → Y` is Hölder
continuous in a neighborhood within `s` of every point `x ∈ s` with the same positive exponent `r`
but possibly different coefficients, then the Hausdorff dimension of the image `f '' s` is at most
the Hausdorff dimension of `s` divided by `r`. -/
lemma dimH_image_le_of_locally_holder_on [second_countable_topology X] {r : ℝ≥0} {f : X → Y}
  (hr : 0 < r) {s : set X} (hf : ∀ x ∈ s, ∃ (C : ℝ≥0) (t ∈ 𝓝[s] x), holder_on_with C r f t) :
  dimH (f '' s) ≤ dimH s / r :=
begin
  choose! C t htn hC using hf,
  rcases countable_cover_nhds_within htn with ⟨u, hus, huc, huU⟩,
  replace huU := inter_eq_self_of_subset_left huU, rw inter_bUnion at huU,
  rw [← huU, image_bUnion, dimH_bUnion huc, dimH_bUnion huc], simp only [ennreal.supr_div],
  exact bsupr_le_bsupr (λ x hx, ((hC x (hus hx)).mono (inter_subset_right _ _)).dimH_image_le hr)
end

/-- If `f : X → Y` is Hölder continuous in a neighborhood of every point `x : X` with the same
positive exponent `r` but possibly different coefficients, then the Hausdorff dimension of the range
of `f` is at most the Hausdorff dimension of `X` divided by `r`. -/
lemma dimH_range_le_of_locally_holder_on [second_countable_topology X] {r : ℝ≥0} {f : X → Y}
  (hr : 0 < r) (hf : ∀ x : X, ∃ (C : ℝ≥0) (s ∈ 𝓝 x), holder_on_with C r f s) :
  dimH (range f) ≤ dimH (univ : set X) / r :=
begin
  rw ← image_univ,
  refine dimH_image_le_of_locally_holder_on hr (λ x _, _),
  simpa only [exists_prop, nhds_within_univ] using hf x
end

namespace lipschitz_on_with

variables {K : ℝ≥0} {f : X → Y} {s t : set X}

/-- If `f : X → Y` is `K`-Lipschitz on `s`, then `μH[d] (f '' s) ≤ K ^ d * μH[d] s`. -/
lemma hausdorff_measure_image_le (h : lipschitz_on_with K f s) {d : ℝ} (hd : 0 ≤ d) :
  μH[d] (f '' s) ≤ K ^ d * μH[d] s :=
by simpa only [nnreal.coe_one, one_mul]
  using h.holder_on_with.hausdorff_measure_image_le zero_lt_one hd

/-- If `f : X → Y` is Lipschitz continuous on `s`, then `dimH (f '' s) ≤ dimH s`. -/
lemma dimH_image_le (h : lipschitz_on_with K f s) : dimH (f '' s) ≤ dimH s :=
by simpa using h.holder_on_with.dimH_image_le zero_lt_one

end lipschitz_on_with

namespace lipschitz_with

variables {K : ℝ≥0} {f : X → Y}

/-- If `f` is a `K`-Lipschitz map, then it increases the Hausdorff `d`-measures of sets at most
by the factor of `K ^ d`.-/
lemma hausdorff_measure_image_le (h : lipschitz_with K f) {d : ℝ} (hd : 0 ≤ d) (s : set X) :
  μH[d] (f '' s) ≤ K ^ d * μH[d] s :=
(h.lipschitz_on_with s).hausdorff_measure_image_le hd

/-- If `f` is a Lipschitz continuous map, then `dimH (f '' s) ≤ dimH s`. -/
lemma dimH_image_le (h : lipschitz_with K f) (s : set X) : dimH (f '' s) ≤ dimH s :=
(h.lipschitz_on_with s).dimH_image_le

/-- If `f` is a Lipschitz continuous map, then the Hausdorff dimension of its range is at most the
Hausdorff dimension of its domain. -/
lemma dimH_range_le (h : lipschitz_with K f) : dimH (range f) ≤ dimH (univ : set X) :=
@image_univ _ _ f ▸ h.dimH_image_le univ

end lipschitz_with

/-- If `s` is a set in an extended metric space `X` with second countable topology and `f : X → Y`
is Lipschitz in a neighborhood within `s` of every point `x ∈ s`, then the Hausdorff dimension of
the image `f '' s` is at most the Hausdorff dimension of `s`. -/
lemma dimH_image_le_of_locally_lipschitz_on [second_countable_topology X] {f : X → Y}
  {s : set X} (hf : ∀ x ∈ s, ∃ (C : ℝ≥0) (t ∈ 𝓝[s] x), lipschitz_on_with C f t) :
  dimH (f '' s) ≤ dimH s :=
begin
  have : ∀ x ∈ s, ∃ (C : ℝ≥0) (t ∈ 𝓝[s] x), holder_on_with C 1 f t,
    by simpa only [holder_on_with_one] using hf,
  simpa only [ennreal.coe_one, ennreal.div_one]
    using dimH_image_le_of_locally_holder_on zero_lt_one this
end

/-- If `f : X → Y` is Lipschitz in a neighborhood of each point `x : X`, then the Hausdorff
dimension of `range f` is at most the Hausdorff dimension of `X`. -/
lemma dimH_range_le_of_locally_lipschitz_on [second_countable_topology X] {f : X → Y}
  (hf : ∀ x : X, ∃ (C : ℝ≥0) (s ∈ 𝓝 x), lipschitz_on_with C f s) :
  dimH (range f) ≤ dimH (univ : set X) :=
begin
  rw ← image_univ,
  refine dimH_image_le_of_locally_lipschitz_on (λ x _, _),
  simpa only [exists_prop, nhds_within_univ] using hf x
end

/-!
### Antilipschitz maps do not decrease Hausdorff measures and dimension
-/

namespace antilipschitz_with

variables {f : X → Y} {K : ℝ≥0} {d : ℝ}

lemma hausdorff_measure_preimage_le (hf : antilipschitz_with K f) (hd : 0 ≤ d) (s : set Y) :
  μH[d] (f ⁻¹' s) ≤ K ^ d * μH[d] s :=
begin
  rcases eq_or_ne K 0 with rfl|h0,
  { haveI : subsingleton X := hf.subsingleton,
    have : (f ⁻¹' s).subsingleton, from subsingleton_univ.mono (subset_univ _),
    rw this.measure_zero,
    exact zero_le _ },
  have hKd0 : (K : ℝ≥0∞) ^ d ≠ 0, by simp [h0],
  have hKd : (K : ℝ≥0∞) ^ d ≠ ∞, by simp [hd],
  simp only [hausdorff_measure_apply', ennreal.mul_supr, ennreal.mul_infi_of_ne hKd0 hKd,
    ← ennreal.tsum_mul_left],
  refine bsupr_le (λ ε ε0, _),
  refine le_bsupr_of_le (ε / K) (by simp [ε0.ne']) _,
  refine le_binfi (λ t hst, le_infi $ λ htε, _),
  replace hst : f ⁻¹' s ⊆ _ := preimage_mono hst, rw preimage_Union at hst,
  refine binfi_le_of_le _ hst (infi_le_of_le (λ n, _) _),
  { exact (hf.ediam_preimage_le _).trans (ennreal.mul_le_of_le_div' $ htε n) },
  { refine ennreal.tsum_le_tsum (λ n, supr_le $
      λ H, le_supr_of_le (λ h, H $ h.preimage hf.injective) _),
    rw [← ennreal.mul_rpow_of_nonneg _ _ hd],
    exact ennreal.rpow_le_rpow (hf.ediam_preimage_le _) hd }
end

lemma le_hausdorff_measure_image (hf : antilipschitz_with K f) (hd : 0 ≤ d) (s : set X) :
  μH[d] s ≤ K ^ d * μH[d] (f '' s) :=
calc μH[d] s ≤ μH[d] (f ⁻¹' (f '' s)) : measure_mono (subset_preimage_image _ _)
         ... ≤ K ^ d * μH[d] (f '' s) : hf.hausdorff_measure_preimage_le hd (f '' s)

lemma dimH_preimage_le (hf : antilipschitz_with K f) (s : set Y) :
  dimH (f ⁻¹' s) ≤ dimH s :=
begin
  refine bsupr_le (λ d hd, le_dimH_of_hausdorff_measure_eq_top _),
  have := hf.hausdorff_measure_preimage_le d.coe_nonneg s,
  rw [hd, top_le_iff] at this,
  contrapose! this,
  exact ennreal.mul_ne_top (by simp) this
end

lemma le_dimH_image (hf : antilipschitz_with K f) (s : set X) :
  dimH s ≤ dimH (f '' s) :=
calc dimH s ≤ dimH (f ⁻¹' (f '' s)) : dimH_mono (subset_preimage_image _ _)
        ... ≤ dimH (f '' s)         : hf.dimH_preimage_le _

end antilipschitz_with

/-!
### Isometries preserve the Hausdorff measure and Hausdorff dimension
-/

namespace isometry

variables {f : X → Y} {d : ℝ}

lemma hausdorff_measure_image (hf : isometry f) (hd : 0 ≤ d ∨ surjective f) (s : set X) :
  μH[d] (f '' s) = μH[d] s :=
begin
  simp only [hausdorff_measure, ← outer_measure.coe_mk_metric, ← outer_measure.comap_apply],
  rw [outer_measure.isometry_comap_mk_metric _ hf (hd.imp_left _)],
  exact λ hd x y hxy, ennreal.rpow_le_rpow hxy hd
end

lemma hausdorff_measure_preimage (hf : isometry f) (hd : 0 ≤ d ∨ surjective f) (s : set Y) :
  μH[d] (f ⁻¹' s) = μH[d] (s ∩ range f) :=
by rw [← hf.hausdorff_measure_image hd, image_preimage_eq_inter_range]

lemma map_hausdorff_measure (hf : isometry f) (hd : 0 ≤ d ∨ surjective f) :
  measure.map f μH[d] = (μH[d]).restrict (range f) :=
begin
  ext1 s hs,
  rw [map_apply hf.continuous.measurable hs, restrict_apply hs, hf.hausdorff_measure_preimage hd]
end

lemma dimH_image (hf : isometry f) (s : set X) : dimH (f '' s) = dimH s :=
le_antisymm (hf.lipschitz.dimH_image_le _) (hf.antilipschitz.le_dimH_image _)

end isometry

namespace isometric

@[simp] lemma hausdorff_measure_image (e : X ≃ᵢ Y) (d : ℝ) (s : set X) :
  μH[d] (e '' s) = μH[d] s :=
e.isometry.hausdorff_measure_image (or.inr e.surjective) s

@[simp] lemma hausdorff_measure_preimage (e : X ≃ᵢ Y) (d : ℝ) (s : set Y) :
  μH[d] (e ⁻¹' s) = μH[d] s :=
by rw [← e.image_symm, e.symm.hausdorff_measure_image]

@[simp] lemma dimH_image (e : X ≃ᵢ Y) (s : set X) : dimH (e '' s) = dimH s :=
e.isometry.dimH_image s

@[simp] lemma dimH_preimage (e : X ≃ᵢ Y) (s : set Y) : dimH (e ⁻¹' s) = dimH s :=
by rw [← e.image_symm, e.symm.dimH_image]

lemma dimH_univ (e : X ≃ᵢ Y) : dimH (univ : set X) = dimH (univ : set Y) :=
by rw [← e.dimH_preimage univ, preimage_univ]

end isometric

namespace continuous_linear_equiv

variables {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜]
  [normed_group E] [normed_space 𝕜 E] [measurable_space E] [borel_space E]
  [normed_group F] [normed_space 𝕜 F] [measurable_space F] [borel_space F]

@[simp] lemma dimH_image (e : E ≃L[𝕜] F) (s : set E) : dimH (e '' s) = dimH s :=
le_antisymm (e.lipschitz.dimH_image_le s) $
  by simpa only [e.symm_image_image] using e.symm.lipschitz.dimH_image_le (e '' s)

@[simp] lemma dimH_preimage (e : E ≃L[𝕜] F) (s : set F) : dimH (e ⁻¹' s) = dimH s :=
by rw [← e.image_symm_eq_preimage, e.symm.dimH_image]

lemma dimH_univ (e : E ≃L[𝕜] F) : dimH (univ : set E) = dimH (univ : set F) :=
by rw [← e.dimH_preimage, preimage_univ]

end continuous_linear_equiv

namespace real

variables {E : Type*} [fintype ι] [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  [measurable_space E] [borel_space E]

open measure_theory

open_locale measure_theory

theorem dimH_ball_pi (x : ι → ℝ) {r : ℝ} (hr : 0 < r) :
  dimH (metric.ball x r) = fintype.card ι :=
begin
  casesI is_empty_or_nonempty ι,
  { rwa [dimH_subsingleton, eq_comm, nat.cast_eq_zero, fintype.card_eq_zero_iff],
    exact λ x _ y _, subsingleton.elim x y },
  { rw ← ennreal.coe_nat,
    have : μH[fintype.card ι] (metric.ball x r) = ennreal.of_real ((2 * r) ^ fintype.card ι),
      by rw [hausdorff_measure_pi_real, real.volume_pi_ball _ hr],
    refine dimH_of_hausdorff_measure_ne_zero_ne_top _ _; rw [nnreal.coe_nat_cast, this],
    { simp [pow_pos (mul_pos zero_lt_two hr)] },
    { exact ennreal.of_real_ne_top } }
end

theorem dimH_ball_pi_fin {n : ℕ} (x : fin n → ℝ) {r : ℝ} (hr : 0 < r) :
  dimH (metric.ball x r) = n :=
by rw [dimH_ball_pi x hr, fintype.card_fin]

theorem dimH_univ_pi (ι : Type*) [fintype ι] : dimH (univ : set (ι → ℝ)) = fintype.card ι :=
by simp only [← metric.Union_ball_nat_succ (0 : ι → ℝ), dimH_Union,
  dimH_ball_pi _ (nat.cast_add_one_pos _), supr_const]

theorem dimH_univ_pi_fin (n : ℕ) : dimH (univ : set (fin n → ℝ)) = n :=
by rw [dimH_univ_pi, fintype.card_fin]

theorem dimH_of_mem_nhds {x : E} {s : set E} (h : s ∈ 𝓝 x) :
  dimH s = finrank ℝ E :=
begin
  haveI : finite_dimensional ℝ (fin (finrank ℝ E) → ℝ), from is_noetherian_pi',
  have e : E ≃L[ℝ] (fin (finrank ℝ E) → ℝ),
    from continuous_linear_equiv.of_finrank_eq (finite_dimensional.finrank_fin_fun ℝ).symm,
  rw ← e.dimH_image,
  refine le_antisymm _ _,
  { exact (dimH_mono (subset_univ _)).trans_eq (dimH_univ_pi_fin _) },
  { have : e '' s ∈ 𝓝 (e x), by { rw ← e.map_nhds_eq, exact image_mem_map h },
    rcases metric.nhds_basis_ball.mem_iff.1 this with ⟨r, hr0, hr⟩,
    simpa only [dimH_ball_pi_fin (e x) hr0] using dimH_mono hr }
end

theorem dimH_of_nonempty_interior {s : set E} (h : (interior s).nonempty) :
  dimH s = finrank ℝ E :=
let ⟨x, hx⟩ := h in dimH_of_mem_nhds (mem_interior_iff_mem_nhds.1 hx)

variable (E)

theorem dimH_univ_eq_finrank : dimH (univ : set E) = finrank ℝ E :=
dimH_of_mem_nhds (@univ_mem _ (𝓝 0))

theorem dimH_univ : dimH (univ : set ℝ) = 1 :=
by rw [dimH_univ_eq_finrank ℝ, finite_dimensional.finrank_of_field, nat.cast_one]

end real

variables {E F : Type*}
  [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E] [measurable_space E] [borel_space E]
  [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F]

theorem dense_compl_of_dimH_lt_finrank {s : set E} (hs : dimH s < finrank ℝ E) : dense sᶜ :=
begin
  refine λ x, mem_closure_iff_nhds.2 (λ t ht, ne_empty_iff_nonempty.1 $ λ he, hs.not_le _),
  rw [← diff_eq, diff_eq_empty] at he,
  rw [← real.dimH_of_mem_nhds ht],
  exact dimH_mono he
end

/-!
### Hausdorff dimension and `C¹`-smooth maps

`C¹`-smooth maps are locally Lipschitz continuous, hence they do not increase the Hausdorff
dimension of sets.
-/

/-- Let `f` be a function defined on a finite dimensional real normed space. If `f` is `C¹`-smooth
on a convex set `s`, then the Hausdorff dimension of `f '' s` is less than or equal to the Hausdorff
dimension of `s`.

TODO: do we actually need `convex s`? -/
lemma times_cont_diff_on.dimH_image_le {f : E → F} {s t : set E} (hf : times_cont_diff_on ℝ 1 f s)
  (hc : convex s) (ht : t ⊆ s) :
  dimH (f '' t) ≤ dimH t :=
dimH_image_le_of_locally_lipschitz_on $ λ x hx,
  let ⟨C, u, hu, hf⟩ := (hf x (ht hx)).exists_lipschitz_on_with hc
  in ⟨C, u, nhds_within_mono _ ht hu, hf⟩

/-- The Hausdorff dimension of the range of a `C¹`-smooth function defined on a finite dimensional
real normed space is at most the dimension of its domain as a vector space over `ℝ`. -/
lemma times_cont_diff.dimH_range_le {f : E → F} (h : times_cont_diff ℝ 1 f) :
  dimH (range f) ≤ finrank ℝ E :=
calc dimH (range f) = dimH (f '' univ) : by rw image_univ
... ≤ dimH (univ : set E) : h.times_cont_diff_on.dimH_image_le convex_univ subset.rfl
... = finrank ℝ E : real.dimH_univ_eq_finrank E

/-- A particular case of Sard's Theorem. Let `f : E → F` be a map between finite dimensional real
vector spaces. Suppose that `f` is `C¹` smooth on a convex set `s` of Hausdorff dimension strictly
less than the dimension of `F`. Then the complement of the image `f '' s` is dense in `F`. -/
lemma times_cont_diff_on.dense_compl_image_of_dimH_lt_finrank [finite_dimensional ℝ F] {f : E → F}
  {s t : set E} (h : times_cont_diff_on ℝ 1 f s) (hc : convex s) (ht : t ⊆ s)
  (htF : dimH t < finrank ℝ F) :
  dense (f '' t)ᶜ :=
dense_compl_of_dimH_lt_finrank $ (h.dimH_image_le hc ht).trans_lt htF

/-- A particular case of Sard's Theorem. If `f` is a `C¹` smooth map from a real vector space to a
real vector space `F` of strictly larger dimension, then the complement of the range of `f` is dense
in `F`. -/
lemma times_cont_diff.dense_compl_range_of_finrank_lt_finrank [finite_dimensional ℝ F] {f : E → F}
  (h : times_cont_diff ℝ 1 f) (hEF : finrank ℝ E < finrank ℝ F) :
  dense (range f)ᶜ :=
dense_compl_of_dimH_lt_finrank $ h.dimH_range_le.trans_lt $ ennreal.coe_nat_lt_coe_nat.2 hEF
