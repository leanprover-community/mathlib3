/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import linear_algebra.affine_space.independent
import linear_algebra.finite_dimensional

/-!
# Finite-dimensional subspaces of affine spaces.

This file provides a few results relating to finite-dimensional
subspaces of affine spaces.

## Main definitions

* `collinear` defines collinear sets of points as those that span a
  subspace of dimension at most 1.

-/

noncomputable theory
open_locale big_operators classical affine

section affine_space'

variables (k : Type*) {V : Type*} {P : Type*} [field k] [add_comm_group V] [module k V]
          [affine_space V P]
variables {ι : Type*}
include V

open affine_subspace finite_dimensional vector_space

/-- The `vector_span` of a finite set is finite-dimensional. -/
lemma finite_dimensional_vector_span_of_finite {s : set P} (h : set.finite s) :
  finite_dimensional k (vector_span k s) :=
span_of_finite k $ h.vsub h

/-- The `vector_span` of a family indexed by a `fintype` is
finite-dimensional. -/
instance finite_dimensional_vector_span_of_fintype [fintype ι] (p : ι → P) :
  finite_dimensional k (vector_span k (set.range p)) :=
finite_dimensional_vector_span_of_finite k (set.finite_range _)

/-- The `vector_span` of a subset of a family indexed by a `fintype`
is finite-dimensional. -/
instance finite_dimensional_vector_span_image_of_fintype [fintype ι] (p : ι → P)
  (s : set ι) : finite_dimensional k (vector_span k (p '' s)) :=
finite_dimensional_vector_span_of_finite k ((set.finite.of_fintype _).image _)

/-- The direction of the affine span of a finite set is
finite-dimensional. -/
lemma finite_dimensional_direction_affine_span_of_finite {s : set P} (h : set.finite s) :
  finite_dimensional k (affine_span k s).direction :=
(direction_affine_span k s).symm ▸ finite_dimensional_vector_span_of_finite k h

/-- The direction of the affine span of a family indexed by a
`fintype` is finite-dimensional. -/
instance finite_dimensional_direction_affine_span_of_fintype [fintype ι] (p : ι → P) :
  finite_dimensional k (affine_span k (set.range p)).direction :=
finite_dimensional_direction_affine_span_of_finite k (set.finite_range _)

/-- The direction of the affine span of a subset of a family indexed
by a `fintype` is finite-dimensional. -/
instance finite_dimensional_direction_affine_span_image_of_fintype [fintype ι] (p : ι → P)
  (s : set ι) : finite_dimensional k (affine_span k (p '' s)).direction :=
finite_dimensional_direction_affine_span_of_finite k ((set.finite.of_fintype _).image _)

variables {k}

/-- The `vector_span` of a finite subset of an affinely independent
family has dimension one less than its cardinality. -/
lemma findim_vector_span_image_finset_of_affine_independent {p : ι → P}
  (hi : affine_independent k p) {s : finset ι} {n : ℕ} (hc : finset.card s = n + 1) :
  findim k (vector_span k (p '' ↑s)) = n :=
begin
  have hi' := affine_independent_of_subset_affine_independent
    (affine_independent_set_of_affine_independent hi) (set.image_subset_range p ↑s),
  have hc' : fintype.card (p '' ↑s) = n + 1,
  { rwa [set.card_image_of_injective ↑s (injective_of_affine_independent hi), fintype.card_coe] },
  have hn : (p '' ↑s).nonempty,
  { simp [hc, ←finset.card_pos] },
  rcases hn with ⟨p₁, hp₁⟩,
  rw affine_independent_set_iff_linear_independent_vsub k hp₁ at hi',
  have hfr : (p '' ↑s \ {p₁}).finite := ((set.finite_mem_finset _).image _).subset
    (set.diff_subset _ _),
  haveI := hfr.fintype,
  have hf : set.finite ((λ (p : P), p -ᵥ p₁) '' (p '' ↑s \ {p₁})) := hfr.image _,
  haveI := hf.fintype,
  have hc : hf.to_finset.card = n,
  { rw [hf.card_to_finset,
        set.card_image_of_injective (p '' ↑s \ {p₁}) (vsub_left_injective _)],
    have hd : insert p₁ (p '' ↑s \ {p₁}) = p '' ↑s,
    { rw [set.insert_diff_singleton, set.insert_eq_of_mem hp₁] },
    have hc'' : fintype.card ↥(insert p₁ (p '' ↑s \ {p₁})) = n + 1,
    { convert hc' },
    rw set.card_insert (p '' ↑s \ {p₁}) (λ h, ((set.mem_diff p₁).2 h).2 rfl) at hc'',
    simpa using hc'' },
  rw [vector_span_eq_span_vsub_set_right_ne k hp₁, findim_span_set_eq_card _ hi', ←hc],
  congr
end

/-- The `vector_span` of a finite affinely independent family has
dimension one less than its cardinality. -/
lemma findim_vector_span_of_affine_independent [fintype ι] {p : ι → P}
  (hi : affine_independent k p) {n : ℕ} (hc : fintype.card ι = n + 1) :
  findim k (vector_span k (set.range p)) = n :=
begin
  rw ←finset.card_univ at hc,
  rw [←set.image_univ, ←finset.coe_univ],
  exact findim_vector_span_image_finset_of_affine_independent hi hc
end

/-- If the `vector_span` of a finite subset of an affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
lemma vector_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_findim_add_one
  {p : ι → P} (hi : affine_independent k p) {s : finset ι} {sm : submodule k V}
  [finite_dimensional k sm] (hle : vector_span k (p '' ↑s) ≤ sm)
  (hc : finset.card s = findim k sm + 1) : vector_span k (p '' ↑s) = sm :=
eq_of_le_of_findim_eq hle $ findim_vector_span_image_finset_of_affine_independent hi hc

/-- If the `vector_span` of a finite affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
lemma vector_span_eq_of_le_of_affine_independent_of_card_eq_findim_add_one [fintype ι]
  {p : ι → P} (hi : affine_independent k p) {sm : submodule k V} [finite_dimensional k sm]
  (hle : vector_span k (set.range p) ≤ sm) (hc : fintype.card ι = findim k sm + 1) :
  vector_span k (set.range p) = sm :=
eq_of_le_of_findim_eq hle $ findim_vector_span_of_affine_independent hi hc

/-- If the `affine_span` of a finite subset of an affinely independent
family lies in an affine subspace whose direction has dimension one
less than its cardinality, it equals that subspace. -/
lemma affine_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_findim_add_one
  {p : ι → P} (hi : affine_independent k p) {s : finset ι} {sp : affine_subspace k P}
  [finite_dimensional k sp.direction] (hle : affine_span k (p '' ↑s) ≤ sp)
  (hc : finset.card s = findim k sp.direction + 1) : affine_span k (p '' ↑s) = sp :=
begin
  have hn : (p '' ↑s).nonempty, { simp [hc, ←finset.card_pos] },
  refine eq_of_direction_eq_of_nonempty_of_le _ ((affine_span_nonempty k _).2 hn) hle,
  have hd := direction_le hle,
  rw direction_affine_span at ⊢ hd,
  exact vector_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_findim_add_one hi hd hc
end

/-- If the `affine_span` of a finite affinely independent family lies
in an affine subspace whose direction has dimension one less than its
cardinality, it equals that subspace. -/
lemma affine_span_eq_of_le_of_affine_independent_of_card_eq_findim_add_one [fintype ι]
  {p : ι → P} (hi : affine_independent k p) {sp : affine_subspace k P}
  [finite_dimensional k sp.direction] (hle : affine_span k (set.range p) ≤ sp)
  (hc : fintype.card ι = findim k sp.direction + 1) : affine_span k (set.range p) = sp :=
begin
  rw ←finset.card_univ at hc,
  rw [←set.image_univ, ←finset.coe_univ] at ⊢ hle,
  exact affine_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_findim_add_one hi hle hc
end

/-- The `vector_span` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
lemma vector_span_eq_top_of_affine_independent_of_card_eq_findim_add_one [finite_dimensional k V]
  [fintype ι] {p : ι → P} (hi : affine_independent k p) (hc : fintype.card ι = findim k V + 1) :
  vector_span k (set.range p) = ⊤ :=
eq_top_of_findim_eq $ findim_vector_span_of_affine_independent hi hc

/-- The `affine_span` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
lemma affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one [finite_dimensional k V]
  [fintype ι] {p : ι → P} (hi : affine_independent k p) (hc : fintype.card ι = findim k V + 1) :
  affine_span k (set.range p) = ⊤ :=
begin
  rw [←findim_top, ←direction_top k V P] at hc,
  exact affine_span_eq_of_le_of_affine_independent_of_card_eq_findim_add_one hi le_top hc
end

variables (k)

/-- The `vector_span` of `n + 1` points in an indexed family has
dimension at most `n`. -/
lemma findim_vector_span_image_finset_le (p : ι → P) (s : finset ι) {n : ℕ}
  (hc : finset.card s = n + 1) : findim k (vector_span k (p '' ↑s)) ≤ n :=
begin
  have hn : (p '' ↑s).nonempty,
  { simp [hc, ←finset.card_pos] },
  rcases hn with ⟨p₁, hp₁⟩,
  rw [vector_span_eq_span_vsub_set_right_ne k hp₁],
  have hfp₁ : (p '' ↑s \ {p₁}).finite :=
    ((finset.finite_to_set _).image _).subset (set.diff_subset _ _),
  haveI := hfp₁.fintype,
  have hf : ((λ p, p -ᵥ p₁) '' (p '' ↑s \ {p₁})).finite := hfp₁.image _,
  haveI := hf.fintype,
  convert le_trans (findim_span_le_card ((λ p, p -ᵥ p₁) '' (p '' ↑s \ {p₁}))) _,
  have hm : p₁ ∉ p '' ↑s \ {p₁}, by simp,
  haveI := set.fintype_insert' (p '' ↑s \ {p₁}) hm,
  rw [set.to_finset_card, set.card_image_of_injective (p '' ↑s \ {p₁}) (vsub_left_injective p₁),
      ←add_le_add_iff_right 1, ←set.card_fintype_insert' _ hm],
  have h : fintype.card (↑(s.image p) : set P) ≤ n + 1,
  { rw [fintype.card_coe, ←hc],
    exact finset.card_image_le },
  convert h,
  simp [hp₁]
end

/-- The `vector_span` of an indexed family of `n + 1` points has
dimension at most `n`. -/
lemma findim_vector_span_range_le [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 1) : findim k (vector_span k (set.range p)) ≤ n :=
begin
  rw [←set.image_univ, ←finset.coe_univ],
  rw ←finset.card_univ at hc,
  exact findim_vector_span_image_finset_le _ _ _ hc
end

/-- `n + 1` points are affinely independent if and only if their
`vector_span` has dimension `n`. -/
lemma affine_independent_iff_findim_vector_span_eq [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 1) :
  affine_independent k p ↔ findim k (vector_span k (set.range p)) = n :=
begin
  have hn : nonempty ι, by simp [←fintype.card_pos_iff, hc],
  cases hn with i₁,
  rw [affine_independent_iff_linear_independent_vsub _ _ i₁,
      linear_independent_iff_card_eq_findim_span, eq_comm,
      vector_span_range_eq_span_range_vsub_right_ne k p i₁],
  congr',
  rw ←finset.card_univ at hc,
  rw fintype.subtype_card,
  simp [finset.filter_ne', finset.card_erase_of_mem, hc]
end

/-- `n + 1` points are affinely independent if and only if their
`vector_span` has dimension at least `n`. -/
lemma affine_independent_iff_le_findim_vector_span [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 1) :
  affine_independent k p ↔ n ≤ findim k (vector_span k (set.range p)) :=
begin
  rw affine_independent_iff_findim_vector_span_eq k p hc,
  split,
  { rintro rfl,
    refl },
  { exact λ hle, le_antisymm (findim_vector_span_range_le k p hc) hle }
end

/-- `n + 2` points are affinely independent if and only if their
`vector_span` does not have dimension at most `n`. -/
lemma affine_independent_iff_not_findim_vector_span_le [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 2) :
  affine_independent k p ↔ ¬ findim k (vector_span k (set.range p)) ≤ n :=
by rw [affine_independent_iff_le_findim_vector_span k p hc, ←nat.lt_iff_add_one_le, lt_iff_not_ge]

/-- `n + 2` points have a `vector_span` with dimension at most `n` if
and only if they are not affinely independent. -/
lemma findim_vector_span_le_iff_not_affine_independent [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 2) :
  findim k (vector_span k (set.range p)) ≤ n ↔ ¬ affine_independent k p :=
(not_iff_comm.1 (affine_independent_iff_not_findim_vector_span_le k p hc).symm).symm

/-- A set of points is collinear if their `vector_span` has dimension
at most `1`. -/
def collinear (s : set P) : Prop := dim k (vector_span k s) ≤ 1

/-- The definition of `collinear`. -/
lemma collinear_iff_dim_le_one (s : set P) : collinear k s ↔ dim k (vector_span k s) ≤ 1 :=
iff.rfl

/-- A set of points, whose `vector_span` is finite-dimensional, is
collinear if and only if their `vector_span` has dimension at most
`1`. -/
lemma collinear_iff_findim_le_one (s : set P) [finite_dimensional k (vector_span k s)] :
  collinear k s ↔ findim k (vector_span k s) ≤ 1 :=
begin
  have h := collinear_iff_dim_le_one k s,
  rw ←findim_eq_dim at h,
  exact_mod_cast h
end

variables (P)

/-- The empty set is collinear. -/
lemma collinear_empty : collinear k (∅ : set P) :=
begin
  rw [collinear_iff_dim_le_one, vector_span_empty],
  simp
end

variables {P}

/-- A single point is collinear. -/
lemma collinear_singleton (p : P) : collinear k ({p} : set P) :=
begin
  rw [collinear_iff_dim_le_one, vector_span_singleton],
  simp
end

/-- Given a point `p₀` in a set of points, that set is collinear if and
only if the points can all be expressed as multiples of the same
vector, added to `p₀`. -/
lemma collinear_iff_of_mem {s : set P} {p₀ : P} (h : p₀ ∈ s) :
  collinear k s ↔ ∃ v : V, ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ :=
begin
  simp_rw [collinear_iff_dim_le_one, dim_submodule_le_one_iff', submodule.le_span_singleton_iff],
  split,
  { rintro ⟨v₀, hv⟩,
    use v₀,
    intros p hp,
    obtain ⟨r, hr⟩ := hv (p -ᵥ p₀) (vsub_mem_vector_span k hp h),
    use r,
    rw eq_vadd_iff_vsub_eq,
    exact hr.symm },
  { rintro ⟨v, hp₀v⟩,
    use v,
    intros w hw,
    have hs : vector_span k s ≤ k ∙ v,
    { rw [vector_span_eq_span_vsub_set_right k h, submodule.span_le, set.subset_def],
      intros x hx,
      rw [set_like.mem_coe, submodule.mem_span_singleton],
      rw set.mem_image at hx,
      rcases hx with ⟨p, hp, rfl⟩,
      rcases hp₀v p hp with ⟨r, rfl⟩,
      use r,
      simp },
    have hw' := set_like.le_def.1 hs w hw,
    rwa submodule.mem_span_singleton at hw' }
end

/-- A set of points is collinear if and only if they can all be
expressed as multiples of the same vector, added to the same base
point. -/
lemma collinear_iff_exists_forall_eq_smul_vadd (s : set P) :
  collinear k s ↔ ∃ (p₀ : P) (v : V), ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ :=
begin
  rcases set.eq_empty_or_nonempty s with rfl | ⟨⟨p₁, hp₁⟩⟩,
  { simp [collinear_empty] },
  { rw collinear_iff_of_mem k hp₁,
    split,
    { exact λ h, ⟨p₁, h⟩ },
    { rintros ⟨p, v, hv⟩,
      use v,
      intros p₂ hp₂,
      rcases hv p₂ hp₂ with ⟨r, rfl⟩,
      rcases hv p₁ hp₁ with ⟨r₁, rfl⟩,
      use r - r₁,
      simp [vadd_assoc, ←add_smul] } }
end

/-- Two points are collinear. -/
lemma collinear_insert_singleton (p₁ p₂ : P) : collinear k ({p₁, p₂} : set P) :=
begin
  rw collinear_iff_exists_forall_eq_smul_vadd,
  use [p₁, p₂ -ᵥ p₁],
  intros p hp,
  rw [set.mem_insert_iff, set.mem_singleton_iff] at hp,
  cases hp,
  { use 0,
    simp [hp] },
  { use 1,
    simp [hp] }
end

/-- Three points are affinely independent if and only if they are not
collinear. -/
lemma affine_independent_iff_not_collinear (p : fin 3 → P) :
  affine_independent k p ↔ ¬ collinear k (set.range p) :=
by rw [collinear_iff_findim_le_one,
       affine_independent_iff_not_findim_vector_span_le k p (fintype.card_fin 3)]

/-- Three points are collinear if and only if they are not affinely
independent. -/
lemma collinear_iff_not_affine_independent (p : fin 3 → P) :
  collinear k (set.range p) ↔ ¬ affine_independent k p :=
by rw [collinear_iff_findim_le_one,
       findim_vector_span_le_iff_not_affine_independent k p (fintype.card_fin 3)]

end affine_space'
