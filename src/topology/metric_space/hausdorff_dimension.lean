/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import measure_theory.measure.hausdorff

/-!
# Hausdorff dimension

The Hausdorff dimension of a set `X` in an (extended) metric space is the unique number
`dimH s : ℝ≥0∞` such that for any `d : ℝ≥0` we have

- `μH[d] s = 0` if `dimH s < d`, and
- `μH[d] s = ∞` if `d < dimH s`.

In this file we define `dimH s` to be the Hausdorff dimension of `s`, then prove some basic
properties of Hausdorff dimension.

## Main definitions

* `measure_theory.dimH`: the Hausdorff dimension of a set. For the Hausdorff dimension of the whole
  space we use `measure_theory.dimH (set.univ : set X)`.

## Main results

### Basic properties of Hausdorff dimension

* `hausdorff_measure_of_lt_dimH`, `dimH_le_of_hausdorff_measure_ne_top`,
  `le_dimH_of_hausdorff_measure_eq_top`, `hausdorff_measure_of_dimH_lt`, `measure_zero_of_dimH_lt`,
  `le_dimH_of_hausdorff_measure_ne_zero`, `dimH_of_hausdorff_measure_ne_zero_ne_top`: various forms
  of the characteristic property of the Hausdorff dimension;
* `dimH_union`: the Hausdorff dimension of the union of two sets is the maximum of their Hausdorff
  dimensions.
* `dimH_Union`, `dimH_bUnion`, `dimH_sUnion`: the Hausdorff dimension of a countable union of sets
  is the supremum of their Hausdorff dimensions;
* `dimH_empty`, `dimH_singleton`, `set.subsingleton.dimH_zero`, `set.countable.dimH_zero` : `dimH s
  = 0` whenever `s` is countable;

### (Pre)images under (anti)lipschitz and Hölder continuous maps

* `holder_with.dimH_image_le` etc: if `f : X → Y` is Hölder continuous with exponent `r > 0`, then
  for any `s`, `dimH (f '' s) ≤ dimH s / r`. We prove versions of this statement for `holder_with`,
  `holder_on_with`, and locally Hölder maps, as well as for `set.image` and `set.range`.
* `lipschitz_with.dimH_image_le` etc: Lipschitz continuous maps do not increase the Hausdorff
  dimension of sets.
* for a map that is known to be both Lipschitz and antilipschitz (e.g., for an `isometry` or
  a `continuous_linear_equiv`) we also prove `dimH (f '' s) = dimH s`.

### Hausdorff measure in `ℝⁿ`

* `real.dimH_of_nonempty_interior`: if `s` is a set in a finite dimensional real vector space `E`
  with nonempty interior, then the Hausdorff dimension of `s` is equal to the dimension of `E`.
* `dense_compl_of_dimH_lt_finrank`: if `s` is a set in a finite dimensional real vector space `E`
  with Hausdorff dimension strictly less than the dimension of `E`, the `s` has a dense complement.
* `times_cont_diff.dense_compl_range_of_finrank_lt_finrank`: the complement to the range of a `C¹`
  smooth map is dense provided that the dimension of the domain is strictly less than the dimension
  of the codomain.

## Notations

We use the following notation localized in `measure_theory`. It is defined in
`measure_theory.measure.hausdorff`.

- `μH[d]` : `measure_theory.measure.hausdorff_measure d`

## Implementation notes

* The definition of `dimH` explicitly uses `borel X` as a measurable space structure. This way we
  can formulate lemmas about Hausdorff dimension without assuming that the environment has a
  `[measurable_space X]` instance that is equal but possibly not defeq to `borel X`.

  Lemma `dimH_def` unfolds this definition using whatever `[measurable_space X]` instance we have in
  the environment (as long as it is equal to `borel X`).

* The definition `dimH` is irreducible; use API lemmas or `dimH_def` instead.

## Tags

Hausdorff measure, Hausdorff dimension, dimension
-/
open_locale measure_theory ennreal nnreal topological_space
open measure_theory measure_theory.measure set topological_space finite_dimensional filter

variables {ι X Y : Type*} [emetric_space X] [emetric_space Y]

/-- Hausdorff dimension of a set in an (e)metric space. -/
@[irreducible] noncomputable def dimH (s : set X) : ℝ≥0∞ :=
by letI := borel X; exact ⨆ (d : ℝ≥0) (hd : @hausdorff_measure X _ _ ⟨rfl⟩ d s = ∞), d

/-!
### Basic properties
-/
section measurable

variables [measurable_space X] [borel_space X]

/-- Unfold the definition of `dimH` using `[measurable_space X] [borel_space X]` from the
environment. -/
lemma dimH_def (s : set X) : dimH s = ⨆ (d : ℝ≥0) (hd : μH[d] s = ∞), d :=
begin
  unfreezingI { obtain rfl : ‹measurable_space X› = borel X := borel_space.measurable_eq },
  rw dimH
end

lemma hausdorff_measure_of_lt_dimH {s : set X} {d : ℝ≥0} (h : ↑d < dimH s) : μH[d] s = ∞ :=
begin
  simp only [dimH_def, lt_supr_iff] at h,
  rcases h with ⟨d', hsd', hdd'⟩,
  rw [ennreal.coe_lt_coe, ← nnreal.coe_lt_coe] at hdd',
  exact top_unique (hsd' ▸ hausdorff_measure_mono hdd'.le _)
end

lemma dimH_le {s : set X} {d : ℝ≥0∞} (H : ∀ d' : ℝ≥0, μH[d'] s = ∞ → ↑d' ≤ d) : dimH s ≤ d :=
(dimH_def s).trans_le $ bsupr_le H

lemma dimH_le_of_hausdorff_measure_ne_top {s : set X} {d : ℝ≥0} (h : μH[d] s ≠ ∞) :
  dimH s ≤ d :=
le_of_not_lt $ mt hausdorff_measure_of_lt_dimH h

lemma le_dimH_of_hausdorff_measure_eq_top {s : set X} {d : ℝ≥0} (h : μH[d] s = ∞) :
  ↑d ≤ dimH s :=
by { rw dimH_def, exact le_bsupr d h }

lemma hausdorff_measure_of_dimH_lt {s : set X} {d : ℝ≥0}
  (h : dimH s < d) : μH[d] s = 0 :=
begin
  rw dimH_def at h,
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

end measurable

@[mono] lemma dimH_mono {s t : set X} (h : s ⊆ t) : dimH s ≤ dimH t :=
begin
  letI := borel X, haveI : borel_space X := ⟨rfl⟩,
  exact dimH_le (λ d hd, le_dimH_of_hausdorff_measure_eq_top $
    top_unique $ hd ▸ measure_mono h)
end

lemma dimH_subsingleton {s : set X} (h : s.subsingleton) : dimH s = 0 :=
by simp [dimH, h.measure_zero]

alias dimH_subsingleton ← set.subsingleton.dimH_zero

@[simp] lemma dimH_empty : dimH (∅ : set X) = 0 := subsingleton_empty.dimH_zero

@[simp] lemma dimH_singleton (x : X) : dimH ({x} : set X) = 0 := subsingleton_singleton.dimH_zero

@[simp] lemma dimH_Union [encodable ι] (s : ι → set X) :
  dimH (⋃ i, s i) = ⨆ i, dimH (s i) :=
begin
  letI := borel X, haveI : borel_space X := ⟨rfl⟩,
  refine le_antisymm (dimH_le $ λ d hd, _) (supr_le $ λ i, dimH_mono $ subset_Union _ _),
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
  rw [bUnion_eq_Union, dimH_Union, ← supr_subtype'']
end

@[simp] lemma dimH_sUnion {S : set (set X)} (hS : countable S) : dimH (⋃₀ S) = ⨆ s ∈ S, dimH s :=
by rw [sUnion_eq_bUnion, dimH_bUnion hS]

@[simp] lemma dimH_union (s t : set X) : dimH (s ∪ t) = max (dimH s) (dimH t) :=
by rw [union_eq_Union, dimH_Union, supr_bool_eq, cond, cond, ennreal.sup_eq_max]

lemma dimH_countable {s : set X} (hs : countable s) : dimH s = 0 :=
bUnion_of_singleton s ▸ by simp only [dimH_bUnion hs, dimH_singleton, ennreal.supr_zero_eq_zero]

alias dimH_countable ← set.countable.dimH_zero

lemma dimH_finite {s : set X} (hs : finite s) : dimH s = 0 := hs.countable.dimH_zero

alias dimH_finite ← set.finite.dimH_zero

@[simp] lemma dimH_coe_finset (s : finset X) : dimH (s : set X) = 0 := s.finite_to_set.dimH_zero

alias dimH_coe_finset ← finset.dimH_zero

/-!
### Hausdorff dimension as the supremum of local Hausdorff dimensions
-/

section

variables [second_countable_topology X]

/-- If `r` is less than the Hausdorff dimension of a set `s` in an (extended) metric space with
second countable topology, then there exists a point `x ∈ s` such that every neighborhood
`t` of `x` within `s` has Hausdorff dimension greater than `r`. -/
lemma exists_mem_nhds_within_lt_dimH_of_lt_dimH {s : set X} {r : ℝ≥0∞} (h : r < dimH s) :
  ∃ x ∈ s, ∀ t ∈ 𝓝[s] x, r < dimH t :=
begin
  contrapose! h, choose! t htx htr using h,
  rcases countable_cover_nhds_within htx with ⟨S, hSs, hSc, hSU⟩,
  calc dimH s ≤ dimH (⋃ x ∈ S, t x) : dimH_mono hSU
  ... = ⨆ x ∈ S, dimH (t x) : dimH_bUnion hSc _
  ... ≤ r : bsupr_le (λ x hx, htr x (hSs hx))
end

/-- In an (extended) metric space with second countable topology, the Hausdorff dimension
of a set `s` is the supremum over `x ∈ s` of the limit superiors of `dimH t` along
`(𝓝[s] x).lift' powerset`. -/
lemma bsupr_limsup_dimH (s : set X) : (⨆ x ∈ s, limsup ((𝓝[s] x).lift' powerset) dimH) = dimH s :=
begin
  refine le_antisymm (bsupr_le $ λ x hx, _) _,
  { refine Limsup_le_of_le (by apply_auto_param) (eventually_map.2 _),
    exact eventually_lift'_powerset.2 ⟨s, self_mem_nhds_within, λ t, dimH_mono⟩ },
  { refine le_of_forall_ge_of_dense (λ r hr, _),
    rcases exists_mem_nhds_within_lt_dimH_of_lt_dimH hr with ⟨x, hxs, hxr⟩,
    refine le_bsupr_of_le x hxs _, rw limsup_eq, refine le_Inf (λ b hb, _),
    rcases eventually_lift'_powerset.1 hb with ⟨t, htx, ht⟩,
    exact (hxr t htx).le.trans (ht t subset.rfl) }
end

/-- In an (extended) metric space with second countable topology, the Hausdorff dimension
of a set `s` is the supremum over all `x` of the limit superiors of `dimH t` along
`(𝓝[s] x).lift' powerset`. -/
lemma supr_limsup_dimH (s : set X) : (⨆ x, limsup ((𝓝[s] x).lift' powerset) dimH) = dimH s :=
begin
  refine le_antisymm (supr_le $ λ x, _) _,
  { refine Limsup_le_of_le (by apply_auto_param) (eventually_map.2 _),
    exact eventually_lift'_powerset.2 ⟨s, self_mem_nhds_within, λ t, dimH_mono⟩ },
  { rw ← bsupr_limsup_dimH, exact bsupr_le_supr _ _ }
end

end

/-!
### Hausdorff dimension and Hölder continuity
-/

variables {C K r : ℝ≥0} {f : X → Y} {s t : set X}

/-- If `f` is a Hölder continuous map with exponent `r > 0`, then `dimH (f '' s) ≤ dimH s / r`. -/
lemma holder_on_with.dimH_image_le (h : holder_on_with C r f s) (hr : 0 < r) :
  dimH (f '' s) ≤ dimH s / r :=
begin
  letI := borel X, haveI : borel_space X := ⟨rfl⟩,
  letI := borel Y, haveI : borel_space Y := ⟨rfl⟩,
  refine dimH_le (λ d hd, _),
  have := h.hausdorff_measure_image_le hr d.coe_nonneg,
  rw [hd, ennreal.coe_rpow_of_nonneg _ d.coe_nonneg, top_le_iff] at this,
  have Hrd : μH[(r * d : ℝ≥0)] s = ⊤,
  { contrapose this, exact ennreal.mul_ne_top ennreal.coe_ne_top this },
  rw [ennreal.le_div_iff_mul_le, mul_comm, ← ennreal.coe_mul],
  exacts [le_dimH_of_hausdorff_measure_eq_top Hrd, or.inl (mt ennreal.coe_eq_zero.1 hr.ne'),
    or.inl ennreal.coe_ne_top]
end

namespace holder_with

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

/-!
### Hausdorff dimension and Lipschitz continuity
-/

/-- If `f : X → Y` is Lipschitz continuous on `s`, then `dimH (f '' s) ≤ dimH s`. -/
lemma lipschitz_on_with.dimH_image_le (h : lipschitz_on_with K f s) : dimH (f '' s) ≤ dimH s :=
by simpa using h.holder_on_with.dimH_image_le zero_lt_one

namespace lipschitz_with

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

namespace antilipschitz_with

lemma dimH_preimage_le (hf : antilipschitz_with K f) (s : set Y) :
  dimH (f ⁻¹' s) ≤ dimH s :=
begin
  letI := borel X, haveI : borel_space X := ⟨rfl⟩,
  letI := borel Y, haveI : borel_space Y := ⟨rfl⟩,
  refine dimH_le (λ d hd, le_dimH_of_hausdorff_measure_eq_top _),
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
### Isometries preserve Hausdorff dimension
-/

lemma isometry.dimH_image (hf : isometry f) (s : set X) : dimH (f '' s) = dimH s :=
le_antisymm (hf.lipschitz.dimH_image_le _) (hf.antilipschitz.le_dimH_image _)

namespace isometric

@[simp] lemma dimH_image (e : X ≃ᵢ Y) (s : set X) : dimH (e '' s) = dimH s :=
e.isometry.dimH_image s

@[simp] lemma dimH_preimage (e : X ≃ᵢ Y) (s : set Y) : dimH (e ⁻¹' s) = dimH s :=
by rw [← e.image_symm, e.symm.dimH_image]

lemma dimH_univ (e : X ≃ᵢ Y) : dimH (univ : set X) = dimH (univ : set Y) :=
by rw [← e.dimH_preimage univ, preimage_univ]

end isometric

namespace continuous_linear_equiv

variables {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜]
  [normed_group E] [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F]

@[simp] lemma dimH_image (e : E ≃L[𝕜] F) (s : set E) : dimH (e '' s) = dimH s :=
le_antisymm (e.lipschitz.dimH_image_le s) $
  by simpa only [e.symm_image_image] using e.symm.lipschitz.dimH_image_le (e '' s)

@[simp] lemma dimH_preimage (e : E ≃L[𝕜] F) (s : set F) : dimH (e ⁻¹' s) = dimH s :=
by rw [← e.image_symm_eq_preimage, e.symm.dimH_image]

lemma dimH_univ (e : E ≃L[𝕜] F) : dimH (univ : set E) = dimH (univ : set F) :=
by rw [← e.dimH_preimage, preimage_univ]

end continuous_linear_equiv

/-!
### Hausdorff dimension in a real vector space
-/

namespace real

variables {E : Type*} [fintype ι] [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]

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
by rw [dimH_univ_eq_finrank ℝ, finite_dimensional.finrank_self, nat.cast_one]

end real

variables {E F : Type*}
  [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  [normed_group F] [normed_space ℝ F]

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

TODO: do we actually need `convex ℝ s`? -/
lemma times_cont_diff_on.dimH_image_le {f : E → F} {s t : set E} (hf : times_cont_diff_on ℝ 1 f s)
  (hc : convex ℝ s) (ht : t ⊆ s) :
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
  {s t : set E} (h : times_cont_diff_on ℝ 1 f s) (hc : convex ℝ s) (ht : t ⊆ s)
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
