/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import linear_algebra.affine_space.basis
import linear_algebra.finite_dimensional

/-!
# Finite-dimensional subspaces of affine spaces.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides a few results relating to finite-dimensional
subspaces of affine spaces.

## Main definitions

* `collinear` defines collinear sets of points as those that span a
  subspace of dimension at most 1.

-/

noncomputable theory
open_locale big_operators affine

section affine_space'

variables (k : Type*) {V : Type*} {P : Type*}
variables {ι : Type*}
include V

open affine_subspace finite_dimensional module

variables [division_ring k] [add_comm_group V] [module k V] [affine_space V P]

/-- The `vector_span` of a finite set is finite-dimensional. -/
lemma finite_dimensional_vector_span_of_finite {s : set P} (h : set.finite s) :
  finite_dimensional k (vector_span k s) :=
span_of_finite k $ h.vsub h

/-- The `vector_span` of a family indexed by a `fintype` is
finite-dimensional. -/
instance finite_dimensional_vector_span_range [_root_.finite ι] (p : ι → P) :
  finite_dimensional k (vector_span k (set.range p)) :=
finite_dimensional_vector_span_of_finite k (set.finite_range _)

/-- The `vector_span` of a subset of a family indexed by a `fintype`
is finite-dimensional. -/
instance finite_dimensional_vector_span_image_of_finite [_root_.finite ι] (p : ι → P)
  (s : set ι) : finite_dimensional k (vector_span k (p '' s)) :=
finite_dimensional_vector_span_of_finite k (set.to_finite _)

/-- The direction of the affine span of a finite set is
finite-dimensional. -/
lemma finite_dimensional_direction_affine_span_of_finite {s : set P} (h : set.finite s) :
  finite_dimensional k (affine_span k s).direction :=
(direction_affine_span k s).symm ▸ finite_dimensional_vector_span_of_finite k h

/-- The direction of the affine span of a family indexed by a
`fintype` is finite-dimensional. -/
instance finite_dimensional_direction_affine_span_range [_root_.finite ι] (p : ι → P) :
  finite_dimensional k (affine_span k (set.range p)).direction :=
finite_dimensional_direction_affine_span_of_finite k (set.finite_range _)

/-- The direction of the affine span of a subset of a family indexed
by a `fintype` is finite-dimensional. -/
instance finite_dimensional_direction_affine_span_image_of_finite [_root_.finite ι] (p : ι → P)
  (s : set ι) : finite_dimensional k (affine_span k (p '' s)).direction :=
finite_dimensional_direction_affine_span_of_finite k (set.to_finite _)

/-- An affine-independent family of points in a finite-dimensional affine space is finite. -/
lemma finite_of_fin_dim_affine_independent [finite_dimensional k V] {p : ι → P}
  (hi : affine_independent k p) : _root_.finite ι :=
begin
  nontriviality ι, inhabit ι,
  rw affine_independent_iff_linear_independent_vsub k p default at hi,
  letI : is_noetherian k V := is_noetherian.iff_fg.2 infer_instance,
  exact (set.finite_singleton default).finite_of_compl
    (set.finite_coe_iff.1 hi.finite_of_is_noetherian)
end

/-- An affine-independent subset of a finite-dimensional affine space is finite. -/
lemma finite_set_of_fin_dim_affine_independent [finite_dimensional k V] {s : set ι} {f : s → P}
  (hi : affine_independent k f) : s.finite :=
@set.to_finite _ s (finite_of_fin_dim_affine_independent k hi)

open_locale classical
variables {k}

/-- The `vector_span` of a finite subset of an affinely independent
family has dimension one less than its cardinality. -/
lemma affine_independent.finrank_vector_span_image_finset {p : ι → P}
  (hi : affine_independent k p) {s : finset ι} {n : ℕ} (hc : finset.card s = n + 1) :
  finrank k (vector_span k (s.image p : set P)) = n :=
begin
  have hi' := hi.range.mono (set.image_subset_range p ↑s),
  have hc' : (s.image p).card = n + 1,
  { rwa s.card_image_of_injective hi.injective },
  have hn : (s.image p).nonempty,
  { simp [hc', ←finset.card_pos] },
  rcases hn with ⟨p₁, hp₁⟩,
  have hp₁' : p₁ ∈ p '' s := by simpa using hp₁,
  rw [affine_independent_set_iff_linear_independent_vsub k hp₁', ← finset.coe_singleton,
      ← finset.coe_image, ← finset.coe_sdiff, finset.sdiff_singleton_eq_erase,
      ← finset.coe_image] at hi',
  have hc : (finset.image (λ (p : P), p -ᵥ p₁) ((finset.image p s).erase p₁)).card = n,
  { rw [finset.card_image_of_injective _ (vsub_left_injective _),
        finset.card_erase_of_mem hp₁],
    exact nat.pred_eq_of_eq_succ hc' },
  rwa [vector_span_eq_span_vsub_finset_right_ne k hp₁, finrank_span_finset_eq_card, hc]
end

/-- The `vector_span` of a finite affinely independent family has
dimension one less than its cardinality. -/
lemma affine_independent.finrank_vector_span [fintype ι] {p : ι → P}
  (hi : affine_independent k p) {n : ℕ} (hc : fintype.card ι = n + 1) :
  finrank k (vector_span k (set.range p)) = n :=
begin
  rw ← finset.card_univ at hc,
  rw [← set.image_univ, ← finset.coe_univ, ← finset.coe_image],
  exact hi.finrank_vector_span_image_finset hc
end

/-- The `vector_span` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
lemma affine_independent.vector_span_eq_top_of_card_eq_finrank_add_one [finite_dimensional k V]
  [fintype ι] {p : ι → P} (hi : affine_independent k p) (hc : fintype.card ι = finrank k V + 1) :
  vector_span k (set.range p) = ⊤ :=
eq_top_of_finrank_eq $ hi.finrank_vector_span hc

variables (k)

/-- The `vector_span` of `n + 1` points in an indexed family has
dimension at most `n`. -/
lemma finrank_vector_span_image_finset_le (p : ι → P) (s : finset ι) {n : ℕ}
  (hc : finset.card s = n + 1) : finrank k (vector_span k (s.image p : set P)) ≤ n :=
begin
  have hn : (s.image p).nonempty,
  { rw [finset.nonempty.image_iff, ← finset.card_pos, hc], apply nat.succ_pos },
  rcases hn with ⟨p₁, hp₁⟩,
  rw [vector_span_eq_span_vsub_finset_right_ne k hp₁],
  refine le_trans (finrank_span_finset_le_card (((s.image p).erase p₁).image (λ p, p -ᵥ p₁))) _,
  rw [finset.card_image_of_injective _ (vsub_left_injective p₁), finset.card_erase_of_mem hp₁,
      tsub_le_iff_right, ← hc],
  apply finset.card_image_le
end

/-- The `vector_span` of an indexed family of `n + 1` points has
dimension at most `n`. -/
lemma finrank_vector_span_range_le [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 1) : finrank k (vector_span k (set.range p)) ≤ n :=
begin
  rw [←set.image_univ, ←finset.coe_univ, ← finset.coe_image],
  rw ←finset.card_univ at hc,
  exact finrank_vector_span_image_finset_le _ _ _ hc
end

/-- `n + 1` points are affinely independent if and only if their
`vector_span` has dimension `n`. -/
lemma affine_independent_iff_finrank_vector_span_eq [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 1) :
  affine_independent k p ↔ finrank k (vector_span k (set.range p)) = n :=
begin
  have hn : nonempty ι, by simp [←fintype.card_pos_iff, hc],
  cases hn with i₁,
  rw [affine_independent_iff_linear_independent_vsub _ _ i₁,
      linear_independent_iff_card_eq_finrank_span, eq_comm,
      vector_span_range_eq_span_range_vsub_right_ne k p i₁],
  congr',
  rw ←finset.card_univ at hc,
  rw fintype.subtype_card,
  simp [finset.filter_ne', finset.card_erase_of_mem, hc]
end

/-- `n + 1` points are affinely independent if and only if their
`vector_span` has dimension at least `n`. -/
lemma affine_independent_iff_le_finrank_vector_span [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 1) :
  affine_independent k p ↔ n ≤ finrank k (vector_span k (set.range p)) :=
begin
  rw affine_independent_iff_finrank_vector_span_eq k p hc,
  split,
  { rintro rfl,
    refl },
  { exact λ hle, le_antisymm (finrank_vector_span_range_le k p hc) hle }
end

/-- `n + 2` points are affinely independent if and only if their
`vector_span` does not have dimension at most `n`. -/
lemma affine_independent_iff_not_finrank_vector_span_le [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 2) :
  affine_independent k p ↔ ¬ finrank k (vector_span k (set.range p)) ≤ n :=
by rw [affine_independent_iff_le_finrank_vector_span k p hc, ←nat.lt_iff_add_one_le, lt_iff_not_ge]

/-- `n + 2` points have a `vector_span` with dimension at most `n` if
and only if they are not affinely independent. -/
lemma finrank_vector_span_le_iff_not_affine_independent [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 2) :
  finrank k (vector_span k (set.range p)) ≤ n ↔ ¬ affine_independent k p :=
(not_iff_comm.1 (affine_independent_iff_not_finrank_vector_span_le k p hc).symm).symm

variables {k}

/-- If the `vector_span` of a finite subset of an affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
lemma affine_independent.vector_span_image_finset_eq_of_le_of_card_eq_finrank_add_one
  {p : ι → P} (hi : affine_independent k p) {s : finset ι} {sm : submodule k V}
  [finite_dimensional k sm] (hle : vector_span k (s.image p : set P) ≤ sm)
  (hc : finset.card s = finrank k sm + 1) : vector_span k (s.image p : set P) = sm :=
eq_of_le_of_finrank_eq hle $ hi.finrank_vector_span_image_finset hc

/-- If the `vector_span` of a finite affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
lemma affine_independent.vector_span_eq_of_le_of_card_eq_finrank_add_one [fintype ι]
  {p : ι → P} (hi : affine_independent k p) {sm : submodule k V} [finite_dimensional k sm]
  (hle : vector_span k (set.range p) ≤ sm) (hc : fintype.card ι = finrank k sm + 1) :
  vector_span k (set.range p) = sm :=
eq_of_le_of_finrank_eq hle $ hi.finrank_vector_span hc

/-- If the `affine_span` of a finite subset of an affinely independent
family lies in an affine subspace whose direction has dimension one
less than its cardinality, it equals that subspace. -/
lemma affine_independent.affine_span_image_finset_eq_of_le_of_card_eq_finrank_add_one
  {p : ι → P} (hi : affine_independent k p) {s : finset ι} {sp : affine_subspace k P}
  [finite_dimensional k sp.direction] (hle : affine_span k (s.image p : set P) ≤ sp)
  (hc : finset.card s = finrank k sp.direction + 1) : affine_span k (s.image p : set P) = sp :=
begin
  have hn : s.nonempty,
  { rw [←finset.card_pos, hc], apply nat.succ_pos },
  refine eq_of_direction_eq_of_nonempty_of_le _ ((hn.image _).to_set.affine_span _)hle,
  have hd := direction_le hle,
  rw direction_affine_span at ⊢ hd,
  exact hi.vector_span_image_finset_eq_of_le_of_card_eq_finrank_add_one hd hc
end

/-- If the `affine_span` of a finite affinely independent family lies
in an affine subspace whose direction has dimension one less than its
cardinality, it equals that subspace. -/
lemma affine_independent.affine_span_eq_of_le_of_card_eq_finrank_add_one [fintype ι]
  {p : ι → P} (hi : affine_independent k p) {sp : affine_subspace k P}
  [finite_dimensional k sp.direction] (hle : affine_span k (set.range p) ≤ sp)
  (hc : fintype.card ι = finrank k sp.direction + 1) : affine_span k (set.range p) = sp :=
begin
  rw ←finset.card_univ at hc,
  rw [←set.image_univ, ←finset.coe_univ, ← finset.coe_image] at ⊢ hle,
  exact hi.affine_span_image_finset_eq_of_le_of_card_eq_finrank_add_one hle hc
end

/-- The `affine_span` of a finite affinely independent family is `⊤` iff the
family's cardinality is one more than that of the finite-dimensional space. -/
lemma affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one [finite_dimensional k V]
  [fintype ι] {p : ι → P} (hi : affine_independent k p) :
  affine_span k (set.range p) = ⊤ ↔ fintype.card ι = finrank k V + 1 :=
begin
  split,
  { intros h_tot,
    let n := fintype.card ι - 1,
    have hn : fintype.card ι = n + 1,
    { exact (nat.succ_pred_eq_of_pos (card_pos_of_affine_span_eq_top k V P h_tot)).symm, },
    rw [hn, ← finrank_top, ← (vector_span_eq_top_of_affine_span_eq_top k V P) h_tot,
      ← hi.finrank_vector_span hn], },
  { intros hc,
    rw [← finrank_top, ← direction_top k V P] at hc,
    exact hi.affine_span_eq_of_le_of_card_eq_finrank_add_one le_top hc, },
end

lemma affine.simplex.span_eq_top [finite_dimensional k V] {n : ℕ} (T : affine.simplex k V n)
  (hrank : finrank k V = n) :
  affine_span k (set.range T.points) = ⊤ :=
by rw [affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one T.independent,
  fintype.card_fin, hrank]

/-- The `vector_span` of adding a point to a finite-dimensional subspace is finite-dimensional. -/
instance finite_dimensional_vector_span_insert (s : affine_subspace k P)
  [finite_dimensional k s.direction] (p : P) :
  finite_dimensional k (vector_span k (insert p (s : set P))) :=
begin
  rw [←direction_affine_span, ←affine_span_insert_affine_span],
  rcases (s : set P).eq_empty_or_nonempty with hs | ⟨p₀, hp₀⟩,
  { rw coe_eq_bot_iff at hs,
    rw [hs, bot_coe, span_empty, bot_coe, direction_affine_span],
    convert finite_dimensional_bot _ _;
      simp },
  { rw [affine_span_coe, direction_affine_span_insert hp₀],
    apply_instance }
end

/-- The direction of the affine span of adding a point to a finite-dimensional subspace is
finite-dimensional. -/
instance finite_dimensional_direction_affine_span_insert (s : affine_subspace k P)
  [finite_dimensional k s.direction] (p : P) :
  finite_dimensional k (affine_span k (insert p (s : set P))).direction :=
(direction_affine_span k (insert p (s : set P))).symm ▸ finite_dimensional_vector_span_insert s p

variables (k)

/-- The `vector_span` of adding a point to a set with a finite-dimensional `vector_span` is
finite-dimensional. -/
instance finite_dimensional_vector_span_insert_set (s : set P)
  [finite_dimensional k (vector_span k s)] (p : P) :
  finite_dimensional k (vector_span k (insert p s)) :=
begin
  haveI : finite_dimensional k (affine_span k s).direction :=
    (direction_affine_span k s).symm ▸ infer_instance,
  rw [←direction_affine_span, ←affine_span_insert_affine_span, direction_affine_span],
  exact finite_dimensional_vector_span_insert (affine_span k s) p
end

/-- A set of points is collinear if their `vector_span` has dimension
at most `1`. -/
def collinear (s : set P) : Prop := module.rank k (vector_span k s) ≤ 1

/-- The definition of `collinear`. -/
lemma collinear_iff_rank_le_one (s : set P) : collinear k s ↔ module.rank k (vector_span k s) ≤ 1 :=
iff.rfl

variables {k}

/-- A set of points, whose `vector_span` is finite-dimensional, is
collinear if and only if their `vector_span` has dimension at most
`1`. -/
lemma collinear_iff_finrank_le_one {s : set P} [finite_dimensional k (vector_span k s)] :
  collinear k s ↔ finrank k (vector_span k s) ≤ 1 :=
begin
  have h := collinear_iff_rank_le_one k s,
  rw ←finrank_eq_rank at h,
  exact_mod_cast h
end

alias collinear_iff_finrank_le_one ↔ collinear.finrank_le_one _

/-- A subset of a collinear set is collinear. -/
lemma collinear.subset {s₁ s₂ : set P} (hs : s₁ ⊆ s₂) (h : collinear k s₂) : collinear k s₁ :=
(rank_le_of_submodule (vector_span k s₁) (vector_span k s₂) (vector_span_mono k hs)).trans h

/-- The `vector_span` of collinear points is finite-dimensional. -/
lemma collinear.finite_dimensional_vector_span {s : set P} (h : collinear k s) :
  finite_dimensional k (vector_span k s) :=
is_noetherian.iff_fg.1
  (is_noetherian.iff_rank_lt_aleph_0.2 (lt_of_le_of_lt h cardinal.one_lt_aleph_0))

/-- The direction of the affine span of collinear points is finite-dimensional. -/
lemma collinear.finite_dimensional_direction_affine_span {s : set P} (h : collinear k s) :
  finite_dimensional k (affine_span k s).direction :=
(direction_affine_span k s).symm ▸ h.finite_dimensional_vector_span

variables (k P)

/-- The empty set is collinear. -/
lemma collinear_empty : collinear k (∅ : set P) :=
begin
  rw [collinear_iff_rank_le_one, vector_span_empty],
  simp
end

variables {P}

/-- A single point is collinear. -/
lemma collinear_singleton (p : P) : collinear k ({p} : set P) :=
begin
  rw [collinear_iff_rank_le_one, vector_span_singleton],
  simp
end

variables {k}

/-- Given a point `p₀` in a set of points, that set is collinear if and
only if the points can all be expressed as multiples of the same
vector, added to `p₀`. -/
lemma collinear_iff_of_mem {s : set P} {p₀ : P} (h : p₀ ∈ s) :
  collinear k s ↔ ∃ v : V, ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ :=
begin
  simp_rw [collinear_iff_rank_le_one, rank_submodule_le_one_iff', submodule.le_span_singleton_iff],
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
    have hw' := set_like.le_def.1 hs hw,
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
  { rw collinear_iff_of_mem hp₁,
    split,
    { exact λ h, ⟨p₁, h⟩ },
    { rintros ⟨p, v, hv⟩,
      use v,
      intros p₂ hp₂,
      rcases hv p₂ hp₂ with ⟨r, rfl⟩,
      rcases hv p₁ hp₁ with ⟨r₁, rfl⟩,
      use r - r₁,
      simp [vadd_vadd, ←add_smul] } }
end

variables (k)

/-- Two points are collinear. -/
lemma collinear_pair (p₁ p₂ : P) : collinear k ({p₁, p₂} : set P) :=
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

variables {k}

/-- Three points are affinely independent if and only if they are not
collinear. -/
lemma affine_independent_iff_not_collinear {p : fin 3 → P} :
  affine_independent k p ↔ ¬ collinear k (set.range p) :=
by rw [collinear_iff_finrank_le_one,
       affine_independent_iff_not_finrank_vector_span_le k p (fintype.card_fin 3)]

/-- Three points are collinear if and only if they are not affinely
independent. -/
lemma collinear_iff_not_affine_independent {p : fin 3 → P} :
  collinear k (set.range p) ↔ ¬ affine_independent k p :=
by rw [collinear_iff_finrank_le_one,
       finrank_vector_span_le_iff_not_affine_independent k p (fintype.card_fin 3)]

/-- Three points are affinely independent if and only if they are not collinear. -/
lemma affine_independent_iff_not_collinear_set {p₁ p₂ p₃ : P} :
  affine_independent k ![p₁, p₂, p₃] ↔ ¬collinear k ({p₁, p₂, p₃} : set P) :=
by simp [affine_independent_iff_not_collinear, -set.union_singleton]

/-- Three points are collinear if and only if they are not affinely independent. -/
lemma collinear_iff_not_affine_independent_set {p₁ p₂ p₃ : P} :
  collinear k ({p₁, p₂, p₃} : set P) ↔ ¬affine_independent k ![p₁, p₂, p₃] :=
affine_independent_iff_not_collinear_set.not_left.symm

/-- Three points are affinely independent if and only if they are not collinear. -/
lemma affine_independent_iff_not_collinear_of_ne {p : fin 3 → P} {i₁ i₂ i₃ : fin 3} (h₁₂ : i₁ ≠ i₂)
  (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
  affine_independent k p ↔ ¬collinear k ({p i₁, p i₂, p i₃} : set P) :=
begin
  have hu : (finset.univ : finset (fin 3)) = {i₁, i₂, i₃}, by dec_trivial!,
  rw [affine_independent_iff_not_collinear, ←set.image_univ, ←finset.coe_univ, hu,
      finset.coe_insert, finset.coe_insert, finset.coe_singleton, set.image_insert_eq,
      set.image_pair]
end

/-- Three points are collinear if and only if they are not affinely independent. -/
lemma collinear_iff_not_affine_independent_of_ne {p : fin 3 → P} {i₁ i₂ i₃ : fin 3} (h₁₂ : i₁ ≠ i₂)
  (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
  collinear k ({p i₁, p i₂, p i₃} : set P) ↔ ¬affine_independent k p:=
(affine_independent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃).not_left.symm

/-- If three points are not collinear, the first and second are different. -/
lemma ne₁₂_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬collinear k ({p₁, p₂, p₃} : set P)) : p₁ ≠ p₂ :=
by { rintro rfl, simpa [collinear_pair] using h }

/-- If three points are not collinear, the first and third are different. -/
lemma ne₁₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬collinear k ({p₁, p₂, p₃} : set P)) : p₁ ≠ p₃ :=
by { rintro rfl, simpa [collinear_pair] using h }

/-- If three points are not collinear, the second and third are different. -/
lemma ne₂₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬collinear k ({p₁, p₂, p₃} : set P)) : p₂ ≠ p₃ :=
by { rintro rfl, simpa [collinear_pair] using h }

/-- A point in a collinear set of points lies in the affine span of any two distinct points of
that set. -/
lemma collinear.mem_affine_span_of_mem_of_ne {s : set P} (h : collinear k s) {p₁ p₂ p₃ : P}
  (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) :
  p₃ ∈ line[k, p₁, p₂] :=
begin
  rw collinear_iff_of_mem hp₁ at h,
  rcases h with ⟨v, h⟩,
  rcases h p₂ hp₂ with ⟨r₂, rfl⟩,
  rcases h p₃ hp₃ with ⟨r₃, rfl⟩,
  rw vadd_left_mem_affine_span_pair,
  refine ⟨r₃ / r₂, _⟩,
  have h₂ : r₂ ≠ 0,
  { rintro rfl,
    simpa using hp₁p₂ },
  simp [smul_smul, h₂]
end

/-- The affine span of any two distinct points of a collinear set of points equals the affine
span of the whole set. -/
lemma collinear.affine_span_eq_of_ne {s : set P} (h : collinear k s) {p₁ p₂ : P}
  (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₁p₂ : p₁ ≠ p₂) :
  line[k, p₁, p₂] = affine_span k s :=
le_antisymm (affine_span_mono _
  (set.insert_subset.2 ⟨hp₁, set.singleton_subset_iff.2 hp₂⟩))
  (affine_span_le.2 (λ p hp, h.mem_affine_span_of_mem_of_ne hp₁ hp₂ hp hp₁p₂))

/-- Given a collinear set of points, and two distinct points `p₂` and `p₃` in it, a point `p₁` is
collinear with the set if and only if it is collinear with `p₂` and `p₃`. -/
lemma collinear.collinear_insert_iff_of_ne {s : set P} (h : collinear k s) {p₁ p₂ p₃ : P}
  (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₃ : p₂ ≠ p₃) :
  collinear k (insert p₁ s) ↔ collinear k ({p₁, p₂, p₃} : set P) :=
begin
  have hv : vector_span k (insert p₁ s) = vector_span k ({p₁, p₂, p₃} : set P),
  { conv_lhs { rw [←direction_affine_span, ←affine_span_insert_affine_span] },
    conv_rhs { rw [←direction_affine_span, ←affine_span_insert_affine_span] },
    rw h.affine_span_eq_of_ne hp₂ hp₃ hp₂p₃ },
  rw [collinear, collinear, hv]
end

/-- Adding a point in the affine span of a set does not change whether that set is collinear. -/
lemma collinear_insert_iff_of_mem_affine_span {s : set P} {p : P} (h : p ∈ affine_span k s) :
  collinear k (insert p s) ↔ collinear k s :=
by rw [collinear, collinear, vector_span_insert_eq_vector_span h]

/-- If a point lies in the affine span of two points, those three points are collinear. -/
lemma collinear_insert_of_mem_affine_span_pair {p₁ p₂ p₃ : P} (h : p₁ ∈ line[k, p₂, p₃]) :
  collinear k ({p₁, p₂, p₃} : set P) :=
begin
  rw collinear_insert_iff_of_mem_affine_span h,
  exact collinear_pair _ _ _
end

/-- If two points lie in the affine span of two points, those four points are collinear. -/
lemma collinear_insert_insert_of_mem_affine_span_pair {p₁ p₂ p₃ p₄ : P}
  (h₁ : p₁ ∈ line[k, p₃, p₄]) (h₂ : p₂ ∈ line[k, p₃, p₄]) :
  collinear k ({p₁, p₂, p₃, p₄} : set P) :=
begin
  rw [collinear_insert_iff_of_mem_affine_span ((affine_subspace.le_def' _ _).1
        (affine_span_mono k (set.subset_insert _ _)) _ h₁),
      collinear_insert_iff_of_mem_affine_span h₂],
  exact collinear_pair _ _ _
end

/-- If three points lie in the affine span of two points, those five points are collinear. -/
lemma collinear_insert_insert_insert_of_mem_affine_span_pair {p₁ p₂ p₃ p₄ p₅ : P}
  (h₁ : p₁ ∈ line[k, p₄, p₅]) (h₂ : p₂ ∈ line[k, p₄, p₅]) (h₃ : p₃ ∈ line[k, p₄, p₅]) :
  collinear k ({p₁, p₂, p₃, p₄, p₅} : set P) :=
begin
  rw [collinear_insert_iff_of_mem_affine_span ((affine_subspace.le_def' _ _).1
        (affine_span_mono k ((set.subset_insert _ _).trans (set.subset_insert _ _))) _ h₁),
      collinear_insert_iff_of_mem_affine_span ((affine_subspace.le_def' _ _).1
        (affine_span_mono k (set.subset_insert _ _)) _ h₂),
      collinear_insert_iff_of_mem_affine_span h₃],
  exact collinear_pair _ _ _
end

/-- If three points lie in the affine span of two points, the first four points are collinear. -/
lemma collinear_insert_insert_insert_left_of_mem_affine_span_pair {p₁ p₂ p₃ p₄ p₅ : P}
  (h₁ : p₁ ∈ line[k, p₄, p₅]) (h₂ : p₂ ∈ line[k, p₄, p₅]) (h₃ : p₃ ∈ line[k, p₄, p₅]) :
  collinear k ({p₁, p₂, p₃, p₄} : set P) :=
begin
  refine (collinear_insert_insert_insert_of_mem_affine_span_pair h₁ h₂ h₃).subset _,
  simp [set.insert_subset_insert]
end

/-- If three points lie in the affine span of two points, the first three points are collinear. -/
lemma collinear_triple_of_mem_affine_span_pair {p₁ p₂ p₃ p₄ p₅ : P}
  (h₁ : p₁ ∈ line[k, p₄, p₅]) (h₂ : p₂ ∈ line[k, p₄, p₅]) (h₃ : p₃ ∈ line[k, p₄, p₅]) :
  collinear k ({p₁, p₂, p₃} : set P) :=
begin
  refine (collinear_insert_insert_insert_left_of_mem_affine_span_pair h₁ h₂ h₃).subset _,
  simp [set.insert_subset_insert]
end

variables (k)

/-- A set of points is coplanar if their `vector_span` has dimension at most `2`. -/
def coplanar (s : set P) : Prop := module.rank k (vector_span k s) ≤ 2

variables {k}

/-- The `vector_span` of coplanar points is finite-dimensional. -/
lemma coplanar.finite_dimensional_vector_span {s : set P} (h : coplanar k s) :
  finite_dimensional k (vector_span k s) :=
begin
  refine is_noetherian.iff_fg.1 (is_noetherian.iff_rank_lt_aleph_0.2 (lt_of_le_of_lt h _)),
  simp,
end

/-- The direction of the affine span of coplanar points is finite-dimensional. -/
lemma coplanar.finite_dimensional_direction_affine_span {s : set P} (h : coplanar k s) :
  finite_dimensional k (affine_span k s).direction :=
(direction_affine_span k s).symm ▸ h.finite_dimensional_vector_span

/-- A set of points, whose `vector_span` is finite-dimensional, is coplanar if and only if their
`vector_span` has dimension at most `2`. -/
lemma coplanar_iff_finrank_le_two {s : set P} [finite_dimensional k (vector_span k s)] :
  coplanar k s ↔ finrank k (vector_span k s) ≤ 2 :=
begin
  have h : coplanar k s ↔ module.rank k (vector_span k s) ≤ 2 := iff.rfl,
  rw ←finrank_eq_rank at h,
  exact_mod_cast h
end

alias coplanar_iff_finrank_le_two ↔ coplanar.finrank_le_two _

/-- A subset of a coplanar set is coplanar. -/
lemma coplanar.subset {s₁ s₂ : set P} (hs : s₁ ⊆ s₂) (h : coplanar k s₂) : coplanar k s₁ :=
(rank_le_of_submodule (vector_span k s₁) (vector_span k s₂) (vector_span_mono k hs)).trans h

/-- Collinear points are coplanar. -/
lemma collinear.coplanar {s : set P} (h : collinear k s) : coplanar k s :=
le_trans h one_le_two

variables (k) (P)

/-- The empty set is coplanar. -/
lemma coplanar_empty : coplanar k (∅ : set P) :=
(collinear_empty k P).coplanar

variables {P}

/-- A single point is coplanar. -/
lemma coplanar_singleton (p : P) : coplanar k ({p} : set P) :=
(collinear_singleton k p).coplanar

/-- Two points are coplanar. -/
lemma coplanar_pair (p₁ p₂ : P) : coplanar k ({p₁, p₂} : set P) :=
(collinear_pair k p₁ p₂).coplanar

variables {k}

/-- Adding a point in the affine span of a set does not change whether that set is coplanar. -/
lemma coplanar_insert_iff_of_mem_affine_span {s : set P} {p : P} (h : p ∈ affine_span k s) :
  coplanar k (insert p s) ↔ coplanar k s :=
by rw [coplanar, coplanar, vector_span_insert_eq_vector_span h]

end affine_space'

section division_ring

variables {k : Type*} {V : Type*} {P : Type*}
include V

open affine_subspace finite_dimensional module

variables [division_ring k] [add_comm_group V] [module k V] [affine_space V P]

/-- Adding a point to a finite-dimensional subspace increases the dimension by at most one. -/
lemma finrank_vector_span_insert_le (s : affine_subspace k P) (p : P) :
  finrank k (vector_span k (insert p (s : set P))) ≤ finrank k s.direction + 1 :=
begin
  by_cases hf : finite_dimensional k s.direction, swap,
  { have hf' : ¬finite_dimensional k (vector_span k (insert p (s : set P))),
    { intro h,
      have h' : s.direction ≤ vector_span k (insert p (s : set P)),
      { conv_lhs { rw [←affine_span_coe s, direction_affine_span] },
        exact vector_span_mono k (set.subset_insert _ _) },
      exactI hf (submodule.finite_dimensional_of_le h') },
    rw [finrank_of_infinite_dimensional hf, finrank_of_infinite_dimensional hf', zero_add],
    exact zero_le_one },
  haveI := hf,
  rw [←direction_affine_span, ←affine_span_insert_affine_span],
  rcases (s : set P).eq_empty_or_nonempty with hs | ⟨p₀, hp₀⟩,
  { rw coe_eq_bot_iff at hs,
    rw [hs, bot_coe, span_empty, bot_coe, direction_affine_span, direction_bot, finrank_bot,
        zero_add],
    convert zero_le_one' ℕ,
    rw ←finrank_bot k V,
    convert rfl;
      simp },
  { rw [affine_span_coe, direction_affine_span_insert hp₀, add_comm],
    refine (submodule.finrank_add_le_finrank_add_finrank _ _).trans (add_le_add_right _ _),
    refine finrank_le_one ⟨p -ᵥ p₀, submodule.mem_span_singleton_self _⟩ (λ v, _),
    have h := v.property,
    rw submodule.mem_span_singleton at h,
    rcases h with ⟨c, hc⟩,
    refine ⟨c, _⟩,
    ext,
    exact hc }
end

variables (k)

/-- Adding a point to a set with a finite-dimensional span increases the dimension by at most
one. -/
lemma finrank_vector_span_insert_le_set (s : set P) (p : P) :
  finrank k (vector_span k (insert p s)) ≤ finrank k (vector_span k s) + 1 :=
begin
  rw [←direction_affine_span, ←affine_span_insert_affine_span, direction_affine_span],
  refine (finrank_vector_span_insert_le _ _).trans (add_le_add_right _ _),
  rw direction_affine_span
end

variables {k}

/-- Adding a point to a collinear set produces a coplanar set. -/
lemma collinear.coplanar_insert {s : set P} (h : collinear k s) (p : P) :
  coplanar k (insert p s) :=
begin
  haveI := h.finite_dimensional_vector_span,
  rw [coplanar_iff_finrank_le_two],
  exact (finrank_vector_span_insert_le_set k s p).trans (add_le_add_right h.finrank_le_one _)
end

/-- A set of points in a two-dimensional space is coplanar. -/
lemma coplanar_of_finrank_eq_two (s : set P) (h : finrank k V = 2) : coplanar k s :=
begin
  haveI := finite_dimensional_of_finrank_eq_succ h,
  rw [coplanar_iff_finrank_le_two, ←h],
  exact submodule.finrank_le _
end

/-- A set of points in a two-dimensional space is coplanar. -/
lemma coplanar_of_fact_finrank_eq_two (s : set P) [h : fact (finrank k V = 2)] : coplanar k s :=
coplanar_of_finrank_eq_two s h.out

variables (k)

/-- Three points are coplanar. -/
lemma coplanar_triple (p₁ p₂ p₃ : P) : coplanar k ({p₁, p₂, p₃} : set P) :=
(collinear_pair k p₂ p₃).coplanar_insert p₁

end division_ring

namespace affine_basis

universes u₁ u₂ u₃ u₄

variables {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}
variables [add_comm_group V] [affine_space V P]

section division_ring

variables [division_ring k] [module k V]
include V

protected lemma finite_dimensional [finite ι] (b : affine_basis ι k P) : finite_dimensional k V :=
let ⟨i⟩ := b.nonempty in finite_dimensional.of_fintype_basis (b.basis_of i)

protected lemma finite [finite_dimensional k V] (b : affine_basis ι k P) : finite ι :=
finite_of_fin_dim_affine_independent k b.ind

protected lemma finite_set [finite_dimensional k V] {s : set ι} (b : affine_basis s k P) :
  s.finite :=
finite_set_of_fin_dim_affine_independent k b.ind

lemma card_eq_finrank_add_one [fintype ι] (b : affine_basis ι k P) :
  fintype.card ι = finite_dimensional.finrank k V + 1 :=
begin
  haveI := b.finite_dimensional,
  exact b.ind.affine_span_eq_top_iff_card_eq_finrank_add_one.mp b.tot
end

variables {k V P}

lemma exists_affine_basis_of_finite_dimensional [fintype ι] [finite_dimensional k V]
  (h : fintype.card ι = finite_dimensional.finrank k V + 1) :
  nonempty (affine_basis ι k P) :=
begin
  obtain ⟨s, b, hb⟩ := affine_basis.exists_affine_basis k V P,
  lift s to finset P using b.finite_set,
  refine ⟨b.reindex $ fintype.equiv_of_card_eq _⟩,
  rw [h, ← b.card_eq_finrank_add_one]
end

end division_ring

end affine_basis
