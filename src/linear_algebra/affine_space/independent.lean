/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import data.finset.sort
import data.fin.vec_notation
import data.sign
import linear_algebra.affine_space.combination
import linear_algebra.affine_space.affine_equiv
import linear_algebra.basis

/-!
# Affine independence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines affinely independent families of points.

## Main definitions

* `affine_independent` defines affinely independent families of points
  as those where no nontrivial weighted subtraction is `0`.  This is
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
open_locale big_operators affine
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
  classical,
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
      λ v, (vsub_left_injective p₁).mem_set_image.1
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
    ∑ i in s2, w2 i = 1 → s1.affine_combination k p w1 = s2.affine_combination k p w2 →
      set.indicator ↑s1 w1 = set.indicator ↑s2 w2 :=
begin
  classical,
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
    have hw1s : s.affine_combination k p w1 = p i0 :=
      s.affine_combination_of_eq_one_of_eq_zero w1 p hi0 (function.update_same _ _ _)
                                                (λ _ _ hne, function.update_noteq hne _ _),
    let w2 := w + w1,
    have hw2 : ∑ i in s, w2 i = 1,
    { simp [w2, finset.sum_add_distrib, hw, hw1] },
    have hw2s : s.affine_combination k p w2 = p i0,
    { simp [w2, ←finset.weighted_vsub_vadd_affine_combination, hs, hw1s] },
    replace ha := ha s s w2 w1 hw2 hw1 (hw1s.symm ▸ hw2s),
    have hws : w2 i0 - w1 i0 = 0,
    { rw ←finset.mem_coe at hi0,
      rw [←set.indicator_of_mem hi0 w2, ←set.indicator_of_mem hi0 w1, ha, sub_self] },
    simpa [w2] using hws }
end

/-- A finite family is affinely independent if and only if any affine
combinations (with sum of weights 1) that evaluate to the same point are equal. -/
lemma affine_independent_iff_eq_of_fintype_affine_combination_eq [fintype ι] (p : ι → P) :
  affine_independent k p ↔ ∀ (w1 w2 : ι → k), ∑ i, w1 i = 1 → ∑ i, w2 i = 1 →
    finset.univ.affine_combination k p w1 = finset.univ.affine_combination k p w2 → w1 = w2 :=
begin
  rw affine_independent_iff_indicator_eq_of_affine_combination_eq,
  split,
  { intros h w1 w2 hw1 hw2 hweq,
    simpa only [set.indicator_univ, finset.coe_univ] using h _ _ w1 w2 hw1 hw2 hweq, },
  { intros h s1 s2 w1 w2 hw1 hw2 hweq,
    have hw1' : ∑ i, (s1 : set ι).indicator w1 i = 1,
    { rwa set.sum_indicator_subset _ (finset.subset_univ s1) at hw1, },
    have hw2' : ∑ i, (s2 : set ι).indicator w2 i = 1,
    { rwa set.sum_indicator_subset _ (finset.subset_univ s2) at hw2, },
    rw [finset.affine_combination_indicator_subset w1 p (finset.subset_univ s1),
        finset.affine_combination_indicator_subset w2 p (finset.subset_univ s2)] at hweq,
    exact h _ _ hw1' hw2' hweq, },
end

variables {k}

/-- If we single out one member of an affine-independent family of points and affinely transport
all others along the line joining them to this member, the resulting new family of points is affine-
independent.

This is the affine version of `linear_independent.units_smul`. -/
lemma affine_independent.units_line_map
  {p : ι → P} (hp : affine_independent k p) (j : ι) (w : ι → units k) :
  affine_independent k (λ i, affine_map.line_map (p j) (p i) (w i : k)) :=
begin
  rw affine_independent_iff_linear_independent_vsub k _ j at hp ⊢,
  simp only [affine_map.line_map_vsub_left, affine_map.coe_const, affine_map.line_map_same],
  exact hp.units_smul (λ i, w i),
end

lemma affine_independent.indicator_eq_of_affine_combination_eq {p : ι → P}
  (ha : affine_independent k p) (s₁ s₂ : finset ι) (w₁ w₂ : ι → k) (hw₁ : ∑ i in s₁, w₁ i = 1)
  (hw₂ : ∑ i in s₂, w₂ i = 1) (h : s₁.affine_combination k p w₁ = s₂.affine_combination k p w₂) :
  set.indicator ↑s₁ w₁ = set.indicator ↑s₂ w₂ :=
(affine_independent_iff_indicator_eq_of_affine_combination_eq k p).1 ha s₁ s₂ w₁ w₂ hw₁ hw₂ h

/-- An affinely independent family is injective, if the underlying
ring is nontrivial. -/
protected lemma affine_independent.injective [nontrivial k] {p : ι → P}
  (ha : affine_independent k p) :
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
lemma affine_independent.comp_embedding {ι2 : Type*} (f : ι2 ↪ ι) {p : ι → P}
    (ha : affine_independent k p) : affine_independent k (p ∘ f) :=
begin
  classical,
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
protected lemma affine_independent.subtype {p : ι → P}
    (ha : affine_independent k p) (s : set ι) : affine_independent k (λ i : s, p i) :=
ha.comp_embedding (embedding.subtype _)

/-- If an indexed family of points is affinely independent, so is the
corresponding set of points. -/
protected lemma affine_independent.range {p : ι → P} (ha : affine_independent k p) :
  affine_independent k (λ x, x : set.range p → P) :=
begin
  let f : set.range p → ι := λ x, x.property.some,
  have hf : ∀ x, p (f x) = x := λ x, x.property.some_spec,
  let fe : set.range p ↪ ι := ⟨f, λ x₁ x₂ he, subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩,
  convert ha.comp_embedding fe,
  ext,
  simp [hf]
end

lemma affine_independent_equiv {ι' : Type*} (e : ι ≃ ι') {p : ι' → P} :
  affine_independent k (p ∘ e) ↔ affine_independent k p :=
begin
  refine ⟨_, affine_independent.comp_embedding e.to_embedding⟩,
  intros h,
  have : p = p ∘ e ∘ e.symm.to_embedding, { ext, simp, },
  rw this,
  exact h.comp_embedding e.symm.to_embedding,
end

/-- If a set of points is affinely independent, so is any subset. -/
protected lemma affine_independent.mono {s t : set P}
  (ha : affine_independent k (λ x, x : t → P)) (hs : s ⊆ t) :
  affine_independent k (λ x, x : s → P) :=
ha.comp_embedding (s.embedding_of_subset t hs)

/-- If the range of an injective indexed family of points is affinely
independent, so is that family. -/
lemma affine_independent.of_set_of_injective {p : ι → P}
  (ha : affine_independent k (λ x, x : set.range p → P)) (hi : function.injective p) :
  affine_independent k p :=
ha.comp_embedding
  (⟨λ i, ⟨p i, set.mem_range_self _⟩, λ x y h, hi (subtype.mk_eq_mk.1 h)⟩ : ι ↪ set.range p)

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
  have hf' : f.linear.ker = ⊥, { rwa [linear_map.ker_eq_bot, f.linear_injective_iff], },
  exact linear_independent.map' hai f.linear hf',
end

/-- Injective affine maps preserve affine independence. -/
lemma affine_map.affine_independent_iff {p : ι → P} (f : P →ᵃ[k] P₂) (hf : function.injective f) :
  affine_independent k (f ∘ p) ↔ affine_independent k p :=
⟨affine_independent.of_comp f, λ hai, affine_independent.map' hai f hf⟩

/-- Affine equivalences preserve affine independence of families of points. -/
lemma affine_equiv.affine_independent_iff {p : ι → P} (e : P ≃ᵃ[k] P₂) :
  affine_independent k (e ∘ p) ↔ affine_independent k p :=
e.to_affine_map.affine_independent_iff e.to_equiv.injective

/-- Affine equivalences preserve affine independence of subsets. -/
lemma affine_equiv.affine_independent_set_of_eq_iff {s : set P} (e : P ≃ᵃ[k] P₂) :
  affine_independent k (coe : (e '' s) → P₂) ↔ affine_independent k (coe : s → P) :=
begin
  have : e ∘ (coe : s → P) = (coe : e '' s → P₂) ∘ ((e : P ≃ P₂).image s) := rfl,
  rw [← e.affine_independent_iff, this, affine_independent_equiv],
end

end composition

/-- If a family is affinely independent, and the spans of points
indexed by two subsets of the index type have a point in common, those
subsets of the index type have an element in common, if the underlying
ring is nontrivial. -/
lemma affine_independent.exists_mem_inter_of_exists_mem_inter_affine_span [nontrivial k]
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
lemma affine_independent.affine_span_disjoint_of_disjoint [nontrivial k] {p : ι → P}
    (ha : affine_independent k p) {s1 s2 : set ι} (hd : disjoint s1 s2) :
  disjoint (affine_span k (p '' s1) : set P) (affine_span k (p '' s2)) :=
begin
  refine set.disjoint_left.2 (λ p0 hp0s1 hp0s2, _),
  cases ha.exists_mem_inter_of_exists_mem_inter_affine_span hp0s1 hp0s2 with i hi,
  exact set.disjoint_iff.1 hd hi,
end

/-- If a family is affinely independent, a point in the family is in
the span of some of the points given by a subset of the index type if
and only if that point's index is in the subset, if the underlying
ring is nontrivial. -/
@[simp] protected lemma affine_independent.mem_affine_span_iff [nontrivial k] {p : ι → P}
    (ha : affine_independent k p) (i : ι) (s : set ι) :
  p i ∈ affine_span k (p '' s) ↔ i ∈ s :=
begin
  split,
  { intro hs,
    have h := affine_independent.exists_mem_inter_of_exists_mem_inter_affine_span
      ha hs (mem_affine_span k (set.mem_image_of_mem _ (set.mem_singleton _))),
    rwa [←set.nonempty_def, set.inter_singleton_nonempty] at h },
  { exact λ h, mem_affine_span k (set.mem_image_of_mem p h) }
end

/-- If a family is affinely independent, a point in the family is not
in the affine span of the other points, if the underlying ring is
nontrivial. -/
lemma affine_independent.not_mem_affine_span_diff [nontrivial k] {p : ι → P}
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

/-- Viewing a module as an affine space modelled on itself, we can characterise affine independence
in terms of linear combinations. -/
lemma affine_independent_iff {ι} {p : ι → V} :
  affine_independent k p ↔
  ∀ (s : finset ι) (w : ι → k), s.sum w = 0 → ∑ e in s, w e • p e = 0 → ∀ (e ∈ s), w e = 0 :=
forall₃_congr (λ s w hw, by simp [s.weighted_vsub_eq_linear_combination hw])

/-- Given an affinely independent family of points, a weighted subtraction lies in the
`vector_span` of two points given as affine combinations if and only if it is a weighted
subtraction with weights a multiple of the difference between the weights of the two points. -/
lemma weighted_vsub_mem_vector_span_pair {p : ι → P} (h : affine_independent k p)
  {w w₁ w₂ : ι → k} {s : finset ι} (hw : ∑ i in s, w i = 0) (hw₁ : ∑ i in s, w₁ i = 1)
  (hw₂ : ∑ i in s, w₂ i = 1) :
  s.weighted_vsub p w ∈
    vector_span k ({s.affine_combination k p w₁, s.affine_combination k p w₂} : set P) ↔
    ∃ r : k, ∀ i ∈ s, w i = r * (w₁ i - w₂ i) :=
begin
  rw mem_vector_span_pair,
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨r, hr⟩,
    refine ⟨r, λ i hi, _⟩,
    rw [s.affine_combination_vsub, ←s.weighted_vsub_const_smul, ←sub_eq_zero, ←map_sub] at hr,
    have hw' : ∑ j in s, (r • (w₁ - w₂) - w) j = 0,
    { simp_rw [pi.sub_apply, pi.smul_apply, pi.sub_apply, smul_sub, finset.sum_sub_distrib,
               ←finset.smul_sum, hw, hw₁, hw₂, sub_self] },
    have hr' := h s _ hw' hr i hi,
    rw [eq_comm, ←sub_eq_zero, ←smul_eq_mul],
    exact hr' },
  { rcases h with ⟨r, hr⟩,
    refine ⟨r, _⟩,
    let w' := λ i, r * (w₁ i - w₂ i),
    change ∀ i ∈ s, w i = w' i at hr,
    rw [s.weighted_vsub_congr hr (λ _ _, rfl), s.affine_combination_vsub,
        ←s.weighted_vsub_const_smul],
    congr }
end

/-- Given an affinely independent family of points, an affine combination lies in the
span of two points given as affine combinations if and only if it is an affine combination
with weights those of one point plus a multiple of the difference between the weights of the
two points. -/
lemma affine_combination_mem_affine_span_pair {p : ι → P} (h : affine_independent k p)
  {w w₁ w₂ : ι → k} {s : finset ι} (hw : ∑ i in s, w i = 1) (hw₁ : ∑ i in s, w₁ i = 1)
  (hw₂ : ∑ i in s, w₂ i = 1) :
  s.affine_combination k p w ∈
    line[k, s.affine_combination k p w₁, s.affine_combination k p w₂] ↔
    ∃ r : k, ∀ i ∈ s, w i = r * (w₂ i - w₁ i) + w₁ i :=
begin
  rw [←vsub_vadd (s.affine_combination k p w) (s.affine_combination k p w₁),
      affine_subspace.vadd_mem_iff_mem_direction _ (left_mem_affine_span_pair _ _ _),
      direction_affine_span, s.affine_combination_vsub, set.pair_comm,
      weighted_vsub_mem_vector_span_pair h _ hw₂ hw₁],
  { simp only [pi.sub_apply, sub_eq_iff_eq_add] },
  { simp_rw [pi.sub_apply, finset.sum_sub_distrib, hw, hw₁, sub_self] }
end

end affine_independent

section division_ring

variables {k : Type*} {V : Type*} {P : Type*} [division_ring k] [add_comm_group V] [module k V]
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

variables (k V)

lemma exists_affine_independent (s : set P) :
  ∃ t ⊆ s, affine_span k t = affine_span k s ∧ affine_independent k (coe : t → P) :=
begin
  rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩,
  { exact ⟨∅, set.empty_subset ∅, rfl, affine_independent_of_subsingleton k _⟩, },
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := exists_linear_independent k ((equiv.vadd_const p).symm '' s),
  have hb₀ : ∀ (v : V), v ∈ b → v ≠ 0, { exact λ v hv, hb₃.ne_zero (⟨v, hv⟩ : b), },
  rw linear_independent_set_iff_affine_independent_vadd_union_singleton k hb₀ p at hb₃,
  refine ⟨{p} ∪ (equiv.vadd_const p) '' b, _, _, hb₃⟩,
  { apply set.union_subset (set.singleton_subset_iff.mpr hp),
    rwa ← (equiv.vadd_const p).subset_image' b s, },
  { rw [equiv.coe_vadd_const_symm, ← vector_span_eq_span_vsub_set_right k hp] at hb₂,
    apply affine_subspace.ext_of_direction_eq,
    { have : submodule.span k b = submodule.span k (insert 0 b), { simp, },
      simp only [direction_affine_span, ← hb₂, equiv.coe_vadd_const, set.singleton_union,
        vector_span_eq_span_vsub_set_right k (set.mem_insert p _), this],
      congr,
      change (equiv.vadd_const p).symm '' insert p ((equiv.vadd_const p) '' b) = _,
      rw [set.image_insert_eq, ← set.image_comp],
      simp, },
    { use p,
      simp only [equiv.coe_vadd_const, set.singleton_union, set.mem_inter_iff, coe_affine_span],
      exact ⟨mem_span_points k _ _ (set.mem_insert p _), mem_span_points k _ _ hp⟩, }, },
end

variables (k) {V P}

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
  have hz : (![p₁, p₂] ↑default -ᵥ ![p₁, p₂] 0 : V) ≠ 0,
  { rw he' default, simpa using h.symm },
  exact linear_independent_unique _ hz
end

variables {k V P}

/-- If all but one point of a family are affinely independent, and that point does not lie in
the affine span of that family, the family is affinely independent. -/
lemma affine_independent.affine_independent_of_not_mem_span {p : ι → P} {i : ι}
  (ha : affine_independent k (λ x : {y // y ≠ i}, p x))
  (hi : p i ∉ affine_span k (p '' {x | x ≠ i})) : affine_independent k p :=
begin
  classical,
  intros s w hw hs,
  let s' : finset {y // y ≠ i} := s.subtype (≠ i),
  let p' : {y // y ≠ i} → P := λ x, p x,
  by_cases his : i ∈ s ∧ w i ≠ 0,
  { refine false.elim (hi _),
    let wm : ι → k := -(w i)⁻¹ • w,
    have hms : s.weighted_vsub p wm = (0 : V), { simp [wm, hs] },
    have hwm : ∑ i in s, wm i = 0, { simp [wm, ←finset.mul_sum, hw] },
    have hwmi : wm i = -1, { simp [wm, his.2] },
    let w' : {y // y ≠ i} → k := λ x, wm x,
    have hw' : ∑ x in s', w' x = 1,
    { simp_rw [w', finset.sum_subtype_eq_sum_filter],
      rw ←s.sum_filter_add_sum_filter_not (≠ i) at hwm,
      simp_rw [not_not, finset.filter_eq', if_pos his.1, finset.sum_singleton, ←wm, hwmi,
               ←sub_eq_add_neg, sub_eq_zero] at hwm,
      exact hwm },
    rw [←s.affine_combination_eq_of_weighted_vsub_eq_zero_of_eq_neg_one hms his.1 hwmi,
        ←(subtype.range_coe : _ = {x | x ≠ i}), ←set.range_comp,
        ←s.affine_combination_subtype_eq_filter],
    exact affine_combination_mem_affine_span hw' p' },
  { rw [not_and_distrib, not_not] at his,
    let w' : {y // y ≠ i} → k := λ x, w x,
    have hw' : ∑ x in s', w' x = 0,
    { simp_rw [finset.sum_subtype_eq_sum_filter],
      rw [finset.sum_filter_of_ne, hw],
      rintro x hxs hwx rfl,
      exact hwx (his.neg_resolve_left hxs) },
    have hs' : s'.weighted_vsub p' w' = (0 : V),
    { simp_rw finset.weighted_vsub_subtype_eq_filter,
      rw [finset.weighted_vsub_filter_of_ne, hs],
      rintro x hxs hwx rfl,
      exact hwx (his.neg_resolve_left hxs) },
    intros j hj,
    by_cases hji : j = i,
    { rw hji at hj,
      exact hji.symm ▸ (his.neg_resolve_left hj) },
    { exact ha s' w' hw' hs' ⟨j, hji⟩ (finset.mem_subtype.2 hj) } }
end

/-- If distinct points `p₁` and `p₂` lie in `s` but `p₃` does not, the three points are affinely
independent. -/
lemma affine_independent_of_ne_of_mem_of_mem_of_not_mem {s : affine_subspace k P} {p₁ p₂ p₃ : P}
  (hp₁p₂ : p₁ ≠ p₂) (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∉ s) :
  affine_independent k ![p₁, p₂, p₃] :=
begin
  have ha : affine_independent k (λ x : {x : fin 3 // x ≠ 2}, ![p₁, p₂, p₃] x),
  { rw ←affine_independent_equiv ((fin_succ_above_equiv (2 : fin 3)).to_equiv),
    convert affine_independent_of_ne k hp₁p₂,
    ext x,
    fin_cases x;
      refl },
  refine ha.affine_independent_of_not_mem_span _,
  intro h,
  refine hp₃ ((affine_subspace.le_def' _ s).1 _ p₃ h),
  simp_rw [affine_span_le, set.image_subset_iff, set.subset_def, set.mem_preimage],
  intro x,
  fin_cases x;
    simp [hp₁, hp₂]
end

/-- If distinct points `p₁` and `p₃` lie in `s` but `p₂` does not, the three points are affinely
independent. -/
lemma affine_independent_of_ne_of_mem_of_not_mem_of_mem {s : affine_subspace k P} {p₁ p₂ p₃ : P}
  (hp₁p₃ : p₁ ≠ p₃) (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∉ s) (hp₃ : p₃ ∈ s) :
  affine_independent k ![p₁, p₂, p₃] :=
begin
  rw ←affine_independent_equiv (equiv.swap (1 : fin 3) 2),
  convert affine_independent_of_ne_of_mem_of_mem_of_not_mem hp₁p₃ hp₁ hp₃ hp₂ using 1,
  ext x,
  fin_cases x;
    refl
end

/-- If distinct points `p₂` and `p₃` lie in `s` but `p₁` does not, the three points are affinely
independent. -/
lemma affine_independent_of_ne_of_not_mem_of_mem_of_mem {s : affine_subspace k P} {p₁ p₂ p₃ : P}
  (hp₂p₃ : p₂ ≠ p₃) (hp₁ : p₁ ∉ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) :
  affine_independent k ![p₁, p₂, p₃] :=
begin
  rw ←affine_independent_equiv (equiv.swap (0 : fin 3) 2),
  convert affine_independent_of_ne_of_mem_of_mem_of_not_mem hp₂p₃.symm hp₃ hp₂ hp₁ using 1,
  ext x,
  fin_cases x;
    refl
end

end division_ring

section ordered

variables {k : Type*} {V : Type*} {P : Type*} [linear_ordered_ring k] [add_comm_group V]
variables [module k V] [affine_space V P] {ι : Type*}
include V

local attribute [instance] linear_ordered_ring.decidable_lt

/-- Given an affinely independent family of points, suppose that an affine combination lies in
the span of two points given as affine combinations, and suppose that, for two indices, the
coefficients in the first point in the span are zero and those in the second point in the span
have the same sign. Then the coefficients in the combination lying in the span have the same
sign. -/
lemma sign_eq_of_affine_combination_mem_affine_span_pair {p : ι → P} (h : affine_independent k p)
  {w w₁ w₂ : ι → k} {s : finset ι} (hw : ∑ i in s, w i = 1) (hw₁ : ∑ i in s, w₁ i = 1)
  (hw₂ : ∑ i in s, w₂ i = 1)
  (hs : s.affine_combination k p w ∈
    line[k, s.affine_combination k p w₁, s.affine_combination k p w₂])
  {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hi0 : w₁ i = 0) (hj0 : w₁ j = 0)
  (hij : sign (w₂ i) = sign (w₂ j)) : sign (w i) = sign (w j) :=
begin
  rw affine_combination_mem_affine_span_pair h hw hw₁ hw₂ at hs,
  rcases hs with ⟨r, hr⟩,
  dsimp only at hr,
  rw [hr i hi, hr j hj, hi0, hj0, add_zero, add_zero, sub_zero, sub_zero, sign_mul, sign_mul, hij]
end

/-- Given an affinely independent family of points, suppose that an affine combination lies in
the span of one point of that family and a combination of another two points of that family given
by `line_map` with coefficient between 0 and 1. Then the coefficients of those two points in the
combination lying in the span have the same sign. -/
lemma sign_eq_of_affine_combination_mem_affine_span_single_line_map {p : ι → P}
  (h : affine_independent k p) {w : ι → k} {s : finset ι} (hw : ∑ i in s, w i = 1)
  {i₁ i₂ i₃ : ι} (h₁ : i₁ ∈ s) (h₂ : i₂ ∈ s) (h₃ : i₃ ∈ s) (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
  (h₂₃ : i₂ ≠ i₃) {c : k} (hc0 : 0 < c) (hc1 : c < 1)
  (hs : s.affine_combination k p w ∈ line[k, p i₁, affine_map.line_map (p i₂) (p i₃) c]) :
  sign (w i₂) = sign (w i₃) :=
begin
  classical,
  rw [←s.affine_combination_affine_combination_single_weights k p h₁,
      ←s.affine_combination_affine_combination_line_map_weights p h₂ h₃ c] at hs,
  refine sign_eq_of_affine_combination_mem_affine_span_pair h hw
    (s.sum_affine_combination_single_weights k h₁)
    (s.sum_affine_combination_line_map_weights h₂ h₃ c) hs h₂ h₃
    (finset.affine_combination_single_weights_apply_of_ne k h₁₂.symm)
    (finset.affine_combination_single_weights_apply_of_ne k h₁₃.symm) _,
  rw [finset.affine_combination_line_map_weights_apply_left h₂₃,
      finset.affine_combination_line_map_weights_apply_right h₂₃],
  simp [hc0, sub_pos.2 hc1]
end

end ordered

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
⟨mk_of_point k default⟩

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
  s.independent.comp_embedding (fs.order_emb_of_fin h).to_embedding⟩

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

/-- Remap a simplex along an `equiv` of index types. -/
@[simps]
def reindex {m n : ℕ} (s : simplex k P m) (e : fin (m + 1) ≃ fin (n + 1)) : simplex k P n :=
⟨s.points ∘ e.symm, (affine_independent_equiv e.symm).2 s.independent⟩

/-- Reindexing by `equiv.refl` yields the original simplex. -/
@[simp] lemma reindex_refl {n : ℕ} (s : simplex k P n) :
  s.reindex (equiv.refl (fin (n + 1))) = s :=
ext $ λ _, rfl

/-- Reindexing by the composition of two equivalences is the same as reindexing twice. -/
@[simp] lemma reindex_trans {n₁ n₂ n₃ : ℕ} (e₁₂ : fin (n₁ + 1) ≃ fin (n₂ + 1))
  (e₂₃ : fin (n₂ + 1) ≃ fin (n₃ + 1)) (s : simplex k P n₁) :
  s.reindex (e₁₂.trans e₂₃) = (s.reindex e₁₂).reindex e₂₃ :=
rfl

/-- Reindexing by an equivalence and its inverse yields the original simplex. -/
@[simp] lemma reindex_reindex_symm {m n : ℕ} (s : simplex k P m) (e : fin (m + 1) ≃ fin (n + 1)) :
  (s.reindex e).reindex e.symm = s :=
by rw [←reindex_trans, equiv.self_trans_symm, reindex_refl]

/-- Reindexing by the inverse of an equivalence and that equivalence yields the original simplex. -/
@[simp] lemma reindex_symm_reindex {m n : ℕ} (s : simplex k P m) (e : fin (n + 1) ≃ fin (m + 1)) :
  (s.reindex e.symm).reindex e = s :=
by rw [←reindex_trans, equiv.symm_trans_self, reindex_refl]

/-- Reindexing a simplex produces one with the same set of points. -/
@[simp] lemma reindex_range_points {m n : ℕ} (s : simplex k P m) (e : fin (m + 1) ≃ fin (n + 1)) :
  set.range (s.reindex e).points = set.range s.points :=
by rw [reindex, set.range_comp, equiv.range_eq_univ, set.image_univ]

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
  refine ⟨λ h, _, congr_arg _⟩,
  rw [finset.centroid_eq_affine_combination_fintype,
      finset.centroid_eq_affine_combination_fintype] at h,
  have ha := (affine_independent_iff_indicator_eq_of_affine_combination_eq k s.points).1
    s.independent _ _ _ _ (fs₁.sum_centroid_weights_indicator_eq_one_of_card_eq_add_one k h₁)
    (fs₂.sum_centroid_weights_indicator_eq_one_of_card_eq_add_one k h₂) h,
  simp_rw [finset.coe_univ, set.indicator_univ, function.funext_iff,
           finset.centroid_weights_indicator_def, finset.centroid_weights, h₁, h₂] at ha,
  ext i,
  specialize ha i,
  have key : ∀ n : ℕ, (n : k) + 1 ≠ 0 := λ n h, by norm_cast at h,
  -- we should be able to golf this to `refine ⟨λ hi, decidable.by_contradiction (λ hni, _), ...⟩`,
  -- but for some unknown reason it doesn't work.
  split; intro hi; by_contra hni,
  { simpa [hni, hi, key] using ha },
  { simpa [hni, hi, key] using ha.symm }
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
    (λ _ _ _ _ he, affine_independent.injective s₁.independent he)
    (λ _ _ _ _ he, affine_independent.injective s₂.independent he) h
end

end simplex
end affine
