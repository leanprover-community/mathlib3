/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import data.finset.sort
import data.matrix.notation
import linear_algebra.affine_space.combination
import linear_algebra.basis

/-!
# Affine independence

This file defines affinely independent families of points.

## Main definitions

* `affine_independent` defines affinely independent families of points
  as those where no nontrivial weighted subtraction is 0.  This is
  proved equivalent to two other formulations: linear independence of
  the results of subtracting a base point in the family from the other
  points in the family, or any equal affine combinations having the
  same weights.  A bundled type `simplex` is provided for finite
  affinely independent families of points, with an abbreviation
  `triangle` for the case of three points.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/

noncomputable theory
open_locale big_operators classical affine
open function

section affine_independent


variables (k : Type*) {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
variables [affine_space V P] {ι : Type*}
include V

/-- An indexed family is said to be affinely independent if no
nontrivial weighted subtractions (where the sum of weights is 0) are
0. -/
def affine_independent (p : ι → P) : Prop :=
∀ (s : finset ι) (w : ι → k), ∑ i in s, w i = 0 → s.weighted_vsub p w = (0:V) → ∀ i ∈ s, w i = 0

/-- The definition of `affine_independent`. -/
lemma affine_independent_def (p : ι → P) :
  affine_independent k p ↔
    ∀ (s : finset ι) (w : ι → k),
      ∑ i in s, w i = 0 → s.weighted_vsub p w = (0 : V) → ∀ i ∈ s, w i = 0 :=
iff.rfl

/-- A family with at most one point is affinely independent. -/
lemma affine_independent_of_subsingleton [subsingleton ι] (p : ι → P) :
  affine_independent k p :=
λ s w h hs i hi, fintype.eq_of_subsingleton_of_sum_eq h i hi

/-- A family indexed by a `fintype` is affinely independent if and
only if no nontrivial weighted subtractions over `finset.univ` (where
the sum of the weights is 0) are 0. -/
lemma affine_independent_iff_of_fintype [fintype ι] (p : ι → P) :
  affine_independent k p ↔
    ∀ w : ι → k, ∑ i, w i = 0 → finset.univ.weighted_vsub p w = (0 : V) → ∀ i, w i = 0 :=
begin
  split,
  { exact λ h w hw hs i, h finset.univ w hw hs i (finset.mem_univ _) },
  { intros h s w hw hs i hi,
    rw finset.weighted_vsub_indicator_subset _ _ (finset.subset_univ s) at hs,
    rw set.sum_indicator_subset _ (finset.subset_univ s) at hw,
    replace h := h ((↑s : set ι).indicator w) hw hs i,
    simpa [hi] using h }
end

/-- A family is affinely independent if and only if the differences
from a base point in that family are linearly independent. -/
lemma affine_independent_iff_linear_independent_vsub (p : ι → P) (i1 : ι) :
  affine_independent k p ↔ linear_independent k (λ i : {x // x ≠ i1}, (p i -ᵥ p i1 : V)) :=
begin
  split,
  { intro h,
    rw linear_independent_iff',
    intros s g hg i hi,
    set f : ι → k := λ x, if hx : x = i1 then -∑ y in s, g y else g ⟨x, hx⟩ with hfdef,
    let s2 : finset ι := insert i1 (s.map (embedding.subtype _)),
    have hfg : ∀ x : {x // x ≠ i1}, g x = f x,
    { intro x,
      rw hfdef,
      dsimp only [],
      erw [dif_neg x.property, subtype.coe_eta] },
    rw hfg,
    have hf : ∑ ι in s2, f ι = 0,
    { rw [finset.sum_insert (finset.not_mem_map_subtype_of_not_property s (not_not.2 rfl)),
          finset.sum_subtype_map_embedding (λ x hx, (hfg x).symm)],
      rw hfdef,
      dsimp only [],
      rw dif_pos rfl,
      exact neg_add_self _ },
    have hs2 : s2.weighted_vsub p f = (0:V),
    { set f2 : ι → V := λ x, f x • (p x -ᵥ p i1) with hf2def,
      set g2 : {x // x ≠ i1} → V := λ x, g x • (p x -ᵥ p i1) with hg2def,
      have hf2g2 : ∀ x : {x // x ≠ i1}, f2 x = g2 x,
      { simp_rw [hf2def, hg2def, hfg],
        exact λ x, rfl },
      rw [finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero s2 f p hf (p i1),
          finset.weighted_vsub_of_point_insert, finset.weighted_vsub_of_point_apply,
          finset.sum_subtype_map_embedding (λ x hx, hf2g2 x)],
      exact hg },
    exact h s2 f hf hs2 i (finset.mem_insert_of_mem (finset.mem_map.2 ⟨i, hi, rfl⟩)) },
  { intro h,
    rw linear_independent_iff' at h,
    intros s w hw hs i hi,
    rw [finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero s w p hw (p i1),
        ←s.weighted_vsub_of_point_erase w p i1, finset.weighted_vsub_of_point_apply] at hs,
    let f : ι → V := λ i, w i • (p i -ᵥ p i1),
    have hs2 : ∑ i in (s.erase i1).subtype (λ i, i ≠ i1), f i = 0,
    { rw [←hs],
      convert finset.sum_subtype_of_mem f (λ x, finset.ne_of_mem_erase) },
    have h2 := h ((s.erase i1).subtype (λ i, i ≠ i1)) (λ x, w x) hs2,
    simp_rw [finset.mem_subtype] at h2,
    have h2b : ∀ i ∈ s, i ≠ i1 → w i = 0 :=
      λ i his hi, h2 ⟨i, hi⟩ (finset.mem_erase_of_ne_of_mem hi his),
    exact finset.eq_zero_of_sum_eq_zero hw h2b i hi }
end

/-- A set is affinely independent if and only if the differences from
a base point in that set are linearly independent. -/
lemma affine_independent_set_iff_linear_independent_vsub {s : set P} {p₁ : P} (hp₁ : p₁ ∈ s) :
  affine_independent k (λ p, p : s → P) ↔
  linear_independent k (λ v, v : (λ p, (p -ᵥ p₁ : V)) '' (s \ {p₁}) → V) :=
begin
  rw affine_independent_iff_linear_independent_vsub k (λ p, p : s → P) ⟨p₁, hp₁⟩,
  split,
  { intro h,
    have hv : ∀ v : (λ p, (p -ᵥ p₁ : V)) '' (s \ {p₁}), (v : V) +ᵥ p₁ ∈ s \ {p₁} :=
      λ v, (set.mem_image_of_injective (vsub_left_injective p₁)).1
             ((vadd_vsub (v : V) p₁).symm ▸ v.property),
    let f : (λ p : P, (p -ᵥ p₁ : V)) '' (s \ {p₁}) → {x : s // x ≠ ⟨p₁, hp₁⟩} :=
      λ x, ⟨⟨(x : V) +ᵥ p₁, set.mem_of_mem_diff (hv x)⟩,
            λ hx, set.not_mem_of_mem_diff (hv x) (subtype.ext_iff.1 hx)⟩,
    convert h.comp f
      (λ x1 x2 hx, (subtype.ext (vadd_right_cancel p₁ (subtype.ext_iff.1 (subtype.ext_iff.1 hx))))),
    ext v,
    exact (vadd_vsub (v : V) p₁).symm },
  { intro h,
    let f : {x : s // x ≠ ⟨p₁, hp₁⟩} → (λ p : P, (p -ᵥ p₁ : V)) '' (s \ {p₁}) :=
      λ x, ⟨((x : s) : P) -ᵥ p₁, ⟨x, ⟨⟨(x : s).property, λ hx, x.property (subtype.ext hx)⟩, rfl⟩⟩⟩,
    convert h.comp f
      (λ x1 x2 hx, subtype.ext (subtype.ext (vsub_left_cancel (subtype.ext_iff.1 hx)))) }
end

/-- A set of nonzero vectors is linearly independent if and only if,
given a point `p₁`, the vectors added to `p₁` and `p₁` itself are
affinely independent. -/
lemma linear_independent_set_iff_affine_independent_vadd_union_singleton {s : set V}
  (hs : ∀ v ∈ s, v ≠ (0 : V)) (p₁ : P) : linear_independent k (λ v, v : s → V) ↔
  affine_independent k (λ p, p : {p₁} ∪ ((λ v, v +ᵥ p₁) '' s) → P) :=
begin
  rw affine_independent_set_iff_linear_independent_vsub k
    (set.mem_union_left _ (set.mem_singleton p₁)),
  have h : (λ p, (p -ᵥ p₁ : V)) '' (({p₁} ∪ (λ v, v +ᵥ p₁) '' s) \ {p₁}) = s,
  { simp_rw [set.union_diff_left, set.image_diff (vsub_left_injective p₁), set.image_image,
             set.image_singleton, vsub_self, vadd_vsub, set.image_id'],
    exact set.diff_singleton_eq_self (λ h, hs 0 h rfl) },
  rw h
end

/-- A family is affinely independent if and only if any affine
combinations (with sum of weights 1) that evaluate to the same point
have equal `set.indicator`. -/
lemma affine_independent_iff_indicator_eq_of_affine_combination_eq (p : ι → P) :
  affine_independent k p ↔ ∀ (s1 s2 : finset ι) (w1 w2 : ι → k), ∑ i in s1, w1 i = 1 →
    ∑ i in s2, w2 i = 1 → s1.affine_combination p w1 = s2.affine_combination p w2 →
      set.indicator ↑s1 w1 = set.indicator ↑s2 w2 :=
begin
  split,
  { intros ha s1 s2 w1 w2 hw1 hw2 heq,
    ext i,
    by_cases hi : i ∈ (s1 ∪ s2),
    { rw ←sub_eq_zero,
      rw set.sum_indicator_subset _ (finset.subset_union_left s1 s2) at hw1,
      rw set.sum_indicator_subset _ (finset.subset_union_right s1 s2) at hw2,
      have hws : ∑ i in s1 ∪ s2, (set.indicator ↑s1 w1 - set.indicator ↑s2 w2) i = 0,
      { simp [hw1, hw2] },
      rw [finset.affine_combination_indicator_subset _ _ (finset.subset_union_left s1 s2),
          finset.affine_combination_indicator_subset _ _ (finset.subset_union_right s1 s2),
          ←@vsub_eq_zero_iff_eq V, finset.affine_combination_vsub] at heq,
      exact ha (s1 ∪ s2) (set.indicator ↑s1 w1 - set.indicator ↑s2 w2) hws heq i hi },
    { rw [←finset.mem_coe, finset.coe_union] at hi,
      simp [mt (set.mem_union_left ↑s2) hi, mt (set.mem_union_right ↑s1) hi] } },
  { intros ha s w hw hs i0 hi0,
    let w1 : ι → k := function.update (function.const ι 0) i0 1,
    have hw1 : ∑ i in s, w1 i = 1,
    { rw [finset.sum_update_of_mem hi0, finset.sum_const_zero, add_zero] },
    have hw1s : s.affine_combination p w1 = p i0 :=
      s.affine_combination_of_eq_one_of_eq_zero w1 p hi0 (function.update_same _ _ _)
                                                (λ _ _ hne, function.update_noteq hne _ _),
    let w2 := w + w1,
    have hw2 : ∑ i in s, w2 i = 1,
    { simp [w2, finset.sum_add_distrib, hw, hw1] },
    have hw2s : s.affine_combination p w2 = p i0,
    { simp [w2, ←finset.weighted_vsub_vadd_affine_combination, hs, hw1s] },
    replace ha := ha s s w2 w1 hw2 hw1 (hw1s.symm ▸ hw2s),
    have hws : w2 i0 - w1 i0 = 0,
    { rw ←finset.mem_coe at hi0,
      rw [←set.indicator_of_mem hi0 w2, ←set.indicator_of_mem hi0 w1, ha, sub_self] },
    simpa [w2] using hws }
end

variables {k}

/-- An affinely independent family is injective, if the underlying
ring is nontrivial. -/
lemma injective_of_affine_independent [nontrivial k] {p : ι → P} (ha : affine_independent k p) :
  function.injective p :=
begin
  intros i j hij,
  rw affine_independent_iff_linear_independent_vsub _ _ j at ha,
  by_contra hij',
  exact ha.ne_zero ⟨i, hij'⟩ (vsub_eq_zero_iff_eq.mpr hij)
end

/-- If a family is affinely independent, so is any subfamily given by
composition of an embedding into index type with the original
family. -/
lemma affine_independent_embedding_of_affine_independent {ι2 : Type*} (f : ι2 ↪ ι) {p : ι → P}
    (ha : affine_independent k p) : affine_independent k (p ∘ f) :=
begin
  intros fs w hw hs i0 hi0,
  let fs' := fs.map f,
  let w' := λ i, if h : ∃ i2, f i2 = i then w h.some else 0,
  have hw' : ∀ i2 : ι2, w' (f i2) = w i2,
  { intro i2,
    have h : ∃ i : ι2, f i = f i2 := ⟨i2, rfl⟩,
    have hs : h.some = i2 := f.injective h.some_spec,
    simp_rw [w', dif_pos h, hs] },
  have hw's : ∑ i in fs', w' i = 0,
  { rw [←hw, finset.sum_map],
    simp [hw'] },
  have hs' : fs'.weighted_vsub p w' = (0:V),
  { rw [←hs, finset.weighted_vsub_map],
    congr' with i,
    simp [hw'] },
  rw [←ha fs' w' hw's hs' (f i0) ((finset.mem_map' _).2 hi0), hw']
end

/-- If a family is affinely independent, so is any subfamily indexed
by a subtype of the index type. -/
lemma affine_independent_subtype_of_affine_independent {p : ι → P}
    (ha : affine_independent k p) (s : set ι) : affine_independent k (λ i : s, p i) :=
affine_independent_embedding_of_affine_independent (embedding.subtype _) ha

/-- If an indexed family of points is affinely independent, so is the
corresponding set of points. -/
lemma affine_independent_set_of_affine_independent {p : ι → P} (ha : affine_independent k p) :
  affine_independent k (λ x, x : set.range p → P) :=
begin
  let f : set.range p → ι := λ x, x.property.some,
  have hf : ∀ x, p (f x) = x := λ x, x.property.some_spec,
  let fe : set.range p ↪ ι := ⟨f, λ x₁ x₂ he, subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩,
  convert affine_independent_embedding_of_affine_independent fe ha,
  ext,
  simp [hf]
end

/-- If a set of points is affinely independent, so is any subset. -/
lemma affine_independent_of_subset_affine_independent {s t : set P}
  (ha : affine_independent k (λ x, x : t → P)) (hs : s ⊆ t) :
  affine_independent k (λ x, x : s → P) :=
affine_independent_embedding_of_affine_independent (set.embedding_of_subset s t hs) ha

/-- If the range of an injective indexed family of points is affinely
independent, so is that family. -/
lemma affine_independent_of_affine_independent_set_of_injective {p : ι → P}
  (ha : affine_independent k (λ x, x : set.range p → P)) (hi : function.injective p) :
  affine_independent k p :=
affine_independent_embedding_of_affine_independent
  (⟨λ i, ⟨p i, set.mem_range_self _⟩, λ x y h, hi (subtype.mk_eq_mk.1 h)⟩ : ι ↪ set.range p) ha

section composition

variables {V₂ P₂ : Type*} [add_comm_group V₂] [module k V₂] [affine_space V₂ P₂]
include V₂

/-- If the image of a family of points in affine space under an affine transformation is affine-
independent, then the original family of points is also affine-independent. -/
lemma affine_independent.of_comp {p : ι → P} (f : P →ᵃ[k] P₂) (hai : affine_independent k (f ∘ p)) :
  affine_independent k p :=
begin
  cases is_empty_or_nonempty ι with h h, { haveI := h, apply affine_independent_of_subsingleton, },
  obtain ⟨i⟩ := h,
  rw affine_independent_iff_linear_independent_vsub k p i,
  simp_rw [affine_independent_iff_linear_independent_vsub k (f ∘ p) i, function.comp_app,
    ← f.linear_map_vsub] at hai,
  exact linear_independent.of_comp f.linear hai,
end

/-- The image of a family of points in affine space, under an injective affine transformation, is
affine-independent. -/
lemma affine_independent.map'
  {p : ι → P} (hai : affine_independent k p) (f : P →ᵃ[k] P₂) (hf : function.injective f) :
  affine_independent k (f ∘ p) :=
begin
  cases is_empty_or_nonempty ι with h h, { haveI := h, apply affine_independent_of_subsingleton, },
  obtain ⟨i⟩ := h,
  rw affine_independent_iff_linear_independent_vsub k p i at hai,
  simp_rw [affine_independent_iff_linear_independent_vsub k (f ∘ p) i, function.comp_app,
    ← f.linear_map_vsub],
  have hf' : f.linear.ker = ⊥, { rwa [linear_map.ker_eq_bot, f.injective_iff_linear_injective], },
  exact linear_independent.map' hai f.linear hf',
end

lemma affine_map.affine_independent_iff {p : ι → P} (f : P →ᵃ[k] P₂) (hf : function.injective f) :
  affine_independent k (f ∘ p) ↔ affine_independent k p :=
⟨affine_independent.of_comp f, λ hai, affine_independent.map' hai f hf⟩

end composition

/-- If a family is affinely independent, and the spans of points
indexed by two subsets of the index type have a point in common, those
subsets of the index type have an element in common, if the underlying
ring is nontrivial. -/
lemma exists_mem_inter_of_exists_mem_inter_affine_span_of_affine_independent [nontrivial k]
    {p : ι → P} (ha : affine_independent k p) {s1 s2 : set ι} {p0 : P}
    (hp0s1 : p0 ∈ affine_span k (p '' s1)) (hp0s2 : p0 ∈ affine_span k (p '' s2)):
  ∃ (i : ι), i ∈ s1 ∩ s2 :=
begin
  rw set.image_eq_range at hp0s1 hp0s2,
  rw [mem_affine_span_iff_eq_affine_combination,
      ←finset.eq_affine_combination_subset_iff_eq_affine_combination_subtype] at hp0s1 hp0s2,
  rcases hp0s1 with ⟨fs1, hfs1, w1, hw1, hp0s1⟩,
  rcases hp0s2 with ⟨fs2, hfs2, w2, hw2, hp0s2⟩,
  rw affine_independent_iff_indicator_eq_of_affine_combination_eq at ha,
  replace ha := ha fs1 fs2 w1 w2 hw1 hw2 (hp0s1 ▸ hp0s2),
  have hnz : ∑ i in fs1, w1 i ≠ 0 := hw1.symm ▸ one_ne_zero,
  rcases finset.exists_ne_zero_of_sum_ne_zero hnz with ⟨i, hifs1, hinz⟩,
  simp_rw [←set.indicator_of_mem (finset.mem_coe.2 hifs1) w1, ha] at hinz,
  use [i, hfs1 hifs1, hfs2 (set.mem_of_indicator_ne_zero hinz)]
end

/-- If a family is affinely independent, the spans of points indexed
by disjoint subsets of the index type are disjoint, if the underlying
ring is nontrivial. -/
lemma affine_span_disjoint_of_disjoint_of_affine_independent [nontrivial k] {p : ι → P}
    (ha : affine_independent k p) {s1 s2 : set ι} (hd : s1 ∩ s2 = ∅) :
  (affine_span k (p '' s1) : set P) ∩ affine_span k (p '' s2) = ∅ :=
begin
  by_contradiction hne,
  change (affine_span k (p '' s1) : set P) ∩ affine_span k (p '' s2) ≠ ∅ at hne,
  rw set.ne_empty_iff_nonempty at hne,
  rcases hne with ⟨p0, hp0s1, hp0s2⟩,
  cases exists_mem_inter_of_exists_mem_inter_affine_span_of_affine_independent
    ha hp0s1 hp0s2 with i hi,
  exact set.not_mem_empty i (hd ▸ hi)
end

/-- If a family is affinely independent, a point in the family is in
the span of some of the points given by a subset of the index type if
and only if that point's index is in the subset, if the underlying
ring is nontrivial. -/
@[simp] lemma mem_affine_span_iff_mem_of_affine_independent [nontrivial k] {p : ι → P}
    (ha : affine_independent k p) (i : ι) (s : set ι) :
  p i ∈ affine_span k (p '' s) ↔ i ∈ s :=
begin
  split,
  { intro hs,
    have h := exists_mem_inter_of_exists_mem_inter_affine_span_of_affine_independent
      ha hs (mem_affine_span k (set.mem_image_of_mem _ (set.mem_singleton _))),
    rwa [←set.nonempty_def, set.inter_singleton_nonempty] at h },
  { exact λ h, mem_affine_span k (set.mem_image_of_mem p h) }
end

/-- If a family is affinely independent, a point in the family is not
in the affine span of the other points, if the underlying ring is
nontrivial. -/
lemma not_mem_affine_span_diff_of_affine_independent [nontrivial k] {p : ι → P}
    (ha : affine_independent k p) (i : ι) (s : set ι) :
  p i ∉ affine_span k (p '' (s \ {i})) :=
by simp [ha]

lemma exists_nontrivial_relation_sum_zero_of_not_affine_ind
  {t : finset V} (h : ¬ affine_independent k (coe : t → V)) :
  ∃ f : V → k, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x ∈ t, f x ≠ 0 :=
begin
  classical,
  rw affine_independent_iff_of_fintype at h,
  simp only [exists_prop, not_forall] at h,
  obtain ⟨w, hw, hwt, i, hi⟩ := h,
  simp only [finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ w (coe : t → V) hw 0,
    vsub_eq_sub, finset.weighted_vsub_of_point_apply, sub_zero] at hwt,
  let f : Π (x : V), x ∈ t → k := λ x hx, w ⟨x, hx⟩,
  refine ⟨λ x, if hx : x ∈ t then f x hx else (0 : k), _, _, by { use i, simp [hi, f], }⟩,
  suffices : ∑ (e : V) in t, dite (e ∈ t) (λ hx, (f e hx) • e) (λ hx, 0) = 0,
  { convert this, ext, by_cases hx : x ∈ t; simp [hx], },
  all_goals
  { simp only [finset.sum_dite_of_true (λx h, h), subtype.val_eq_coe, finset.mk_coe, f, hwt, hw], },
end

end affine_independent

section field

variables {k : Type*} {V : Type*} {P : Type*} [field k] [add_comm_group V] [module k V]
variables [affine_space V P] {ι : Type*}
include V

/-- An affinely independent set of points can be extended to such a
set that spans the whole space. -/
lemma exists_subset_affine_independent_affine_span_eq_top {s : set P}
  (h : affine_independent k (λ p, p : s → P)) :
  ∃ t : set P, s ⊆ t ∧ affine_independent k (λ p, p : t → P) ∧ affine_span k t = ⊤ :=
begin
  rcases s.eq_empty_or_nonempty with rfl | ⟨p₁, hp₁⟩,
  { have p₁ : P := add_torsor.nonempty.some,
    let hsv := basis.of_vector_space k V,
    have hsvi := hsv.linear_independent,
    have hsvt := hsv.span_eq,
    rw basis.coe_of_vector_space at hsvi hsvt,
    have h0 : ∀ v : V, v ∈ (basis.of_vector_space_index _ _) → v ≠ 0,
    { intros v hv, simpa using hsv.ne_zero ⟨v, hv⟩ },
    rw linear_independent_set_iff_affine_independent_vadd_union_singleton k h0 p₁ at hsvi,
    exact ⟨{p₁} ∪ (λ v, v +ᵥ p₁) '' _, set.empty_subset _, hsvi,
         affine_span_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt⟩ },
  { rw affine_independent_set_iff_linear_independent_vsub k hp₁ at h,
    let bsv := basis.extend h,
    have hsvi := bsv.linear_independent,
    have hsvt := bsv.span_eq,
    rw basis.coe_extend at hsvi hsvt,
    have hsv := h.subset_extend (set.subset_univ _),
    have h0 : ∀ v : V, v ∈ (h.extend _) → v ≠ 0,
    { intros v hv, simpa using bsv.ne_zero ⟨v, hv⟩ },
    rw linear_independent_set_iff_affine_independent_vadd_union_singleton k h0 p₁ at hsvi,
    refine ⟨{p₁} ∪ (λ v, v +ᵥ p₁) '' h.extend (set.subset_univ _), _, _⟩,
    { refine set.subset.trans _ (set.union_subset_union_right _ (set.image_subset _ hsv)),
      simp [set.image_image] },
    { use [hsvi, affine_span_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt] } }
end

variables (k)

/-- Two different points are affinely independent. -/
lemma affine_independent_of_ne {p₁ p₂ : P} (h : p₁ ≠ p₂) : affine_independent k ![p₁, p₂] :=
begin
  rw affine_independent_iff_linear_independent_vsub k ![p₁, p₂] 0,
  let i₁ : {x // x ≠ (0 : fin 2)} := ⟨1, by norm_num⟩,
  have he' : ∀ i, i = i₁,
  { rintro ⟨i, hi⟩,
    ext,
    fin_cases i,
    { simpa using hi } },
  haveI : unique {x // x ≠ (0 : fin 2)} := ⟨⟨i₁⟩, he'⟩,
  have hz : (![p₁, p₂] ↑(default {x // x ≠ (0 : fin 2)}) -ᵥ ![p₁, p₂] 0 : V) ≠ 0,
  { rw he' (default _), simp, cc },
  exact linear_independent_unique _ hz
end

end field

namespace affine

variables (k : Type*) {V : Type*} (P : Type*) [ring k] [add_comm_group V] [module k V]
variables [affine_space V P]
include V

/-- A `simplex k P n` is a collection of `n + 1` affinely
independent points. -/
structure simplex (n : ℕ) :=
(points : fin (n + 1) → P)
(independent : affine_independent k points)

/-- A `triangle k P` is a collection of three affinely independent points. -/
abbreviation triangle := simplex k P 2

namespace simplex

variables {P}

/-- Construct a 0-simplex from a point. -/
def mk_of_point (p : P) : simplex k P 0 :=
⟨λ _, p, affine_independent_of_subsingleton k _⟩

/-- The point in a simplex constructed with `mk_of_point`. -/
@[simp] lemma mk_of_point_points (p : P) (i : fin 1) : (mk_of_point k p).points i = p :=
rfl

instance [inhabited P] : inhabited (simplex k P 0) :=
⟨mk_of_point k $ default P⟩

instance nonempty : nonempty (simplex k P 0) :=
⟨mk_of_point k $ add_torsor.nonempty.some⟩

variables {k V}

/-- Two simplices are equal if they have the same points. -/
@[ext] lemma ext {n : ℕ} {s1 s2 : simplex k P n} (h : ∀ i, s1.points i = s2.points i) :
  s1 = s2 :=
begin
  cases s1,
  cases s2,
  congr' with i,
  exact h i
end

/-- Two simplices are equal if and only if they have the same points. -/
lemma ext_iff {n : ℕ} (s1 s2 : simplex k P n): s1 = s2 ↔ ∀ i, s1.points i = s2.points i :=
⟨λ h _, h ▸ rfl, ext⟩

/-- A face of a simplex is a simplex with the given subset of
points. -/
def face {n : ℕ} (s : simplex k P n) {fs : finset (fin (n + 1))} {m : ℕ} (h : fs.card = m + 1) :
  simplex k P m :=
⟨s.points ∘ fs.order_emb_of_fin h,
 affine_independent_embedding_of_affine_independent
   (fs.order_emb_of_fin h).to_embedding s.independent⟩

/-- The points of a face of a simplex are given by `mono_of_fin`. -/
lemma face_points {n : ℕ} (s : simplex k P n) {fs : finset (fin (n + 1))} {m : ℕ}
  (h : fs.card = m + 1) (i : fin (m + 1)) :
  (s.face h).points i = s.points (fs.order_emb_of_fin h i) :=
rfl

/-- The points of a face of a simplex are given by `mono_of_fin`. -/
lemma face_points' {n : ℕ} (s : simplex k P n) {fs : finset (fin (n + 1))} {m : ℕ}
  (h : fs.card = m + 1) : (s.face h).points = s.points ∘ (fs.order_emb_of_fin h) :=
rfl

/-- A single-point face equals the 0-simplex constructed with
`mk_of_point`. -/
@[simp] lemma face_eq_mk_of_point {n : ℕ} (s : simplex k P n) (i : fin (n + 1)) :
  s.face (finset.card_singleton i) = mk_of_point k (s.points i) :=
by { ext, simp [face_points] }

/-- The set of points of a face. -/
@[simp] lemma range_face_points {n : ℕ} (s : simplex k P n) {fs : finset (fin (n + 1))}
  {m : ℕ} (h : fs.card = m + 1) : set.range (s.face h).points = s.points '' ↑fs :=
by rw [face_points', set.range_comp, finset.range_order_emb_of_fin]

end simplex

end affine

namespace affine
namespace simplex

variables {k : Type*} {V : Type*} {P : Type*} [division_ring k]
          [add_comm_group V] [module k V] [affine_space V P]
include V

/-- The centroid of a face of a simplex as the centroid of a subset of
the points. -/
@[simp] lemma face_centroid_eq_centroid {n : ℕ} (s : simplex k P n) {fs : finset (fin (n + 1))}
  {m : ℕ} (h : fs.card = m + 1) :
  finset.univ.centroid k (s.face h).points = fs.centroid k s.points :=
begin
  convert (finset.univ.centroid_map k (fs.order_emb_of_fin h).to_embedding s.points).symm,
  rw [← finset.coe_inj, finset.coe_map, finset.coe_univ, set.image_univ],
  simp
end

/-- Over a characteristic-zero division ring, the centroids given by
two subsets of the points of a simplex are equal if and only if those
faces are given by the same subset of points. -/
@[simp] lemma centroid_eq_iff [char_zero k] {n : ℕ} (s : simplex k P n)
  {fs₁ fs₂ : finset (fin (n + 1))} {m₁ m₂ : ℕ} (h₁ : fs₁.card = m₁ + 1) (h₂ : fs₂.card = m₂ + 1) :
  fs₁.centroid k s.points = fs₂.centroid k s.points ↔ fs₁ = fs₂ :=
begin
  split,
  { intro h,
    rw [finset.centroid_eq_affine_combination_fintype,
        finset.centroid_eq_affine_combination_fintype] at h,
    have ha := (affine_independent_iff_indicator_eq_of_affine_combination_eq k s.points).1
      s.independent _ _ _ _ (fs₁.sum_centroid_weights_indicator_eq_one_of_card_eq_add_one k h₁)
      (fs₂.sum_centroid_weights_indicator_eq_one_of_card_eq_add_one k h₂) h,
    simp_rw [finset.coe_univ, set.indicator_univ, function.funext_iff,
             finset.centroid_weights_indicator_def, finset.centroid_weights, h₁, h₂] at ha,
    ext i,
    replace ha := ha i,
    split,
    all_goals
    { intro hi,
      by_contradiction hni,
      simp [hi, hni] at ha,
      norm_cast at ha } },
  { intro h,
    have hm : m₁ = m₂,
    { subst h,
      simpa [h₁] using h₂ },
    subst hm,
    congr,
    exact h }
end

/-- Over a characteristic-zero division ring, the centroids of two
faces of a simplex are equal if and only if those faces are given by
the same subset of points. -/
lemma face_centroid_eq_iff [char_zero k] {n : ℕ} (s : simplex k P n)
  {fs₁ fs₂ : finset (fin (n + 1))} {m₁ m₂ : ℕ} (h₁ : fs₁.card = m₁ + 1) (h₂ : fs₂.card = m₂ + 1) :
  finset.univ.centroid k (s.face h₁).points = finset.univ.centroid k (s.face h₂).points ↔
    fs₁ = fs₂ :=
begin
  rw [face_centroid_eq_centroid, face_centroid_eq_centroid],
  exact s.centroid_eq_iff h₁ h₂
end

/-- Two simplices with the same points have the same centroid. -/
lemma centroid_eq_of_range_eq {n : ℕ} {s₁ s₂ : simplex k P n}
  (h : set.range s₁.points = set.range s₂.points) :
  finset.univ.centroid k s₁.points = finset.univ.centroid k s₂.points :=
begin
  rw [←set.image_univ, ←set.image_univ, ←finset.coe_univ] at h,
  exact finset.univ.centroid_eq_of_inj_on_of_image_eq k _
    (λ _ _ _ _ he, injective_of_affine_independent s₁.independent he)
    (λ _ _ _ _ he, injective_of_affine_independent s₂.independent he) h
end

end simplex
end affine
