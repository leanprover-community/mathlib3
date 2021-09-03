/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.caratheodory
import linear_algebra.affine_space.independent

/-!
# Convex independence

This file defines convexly independent families of points.

## Main declarations

## References

* https://en.wikipedia.org/wiki/Convex_position

## TODO

Once convexity is generalised to affine spaces, `convex_independent` will take as first parameter
the ring of scalars, so that `convex_independent p` becomes `convex_independent k p`, mimicking
`affine_independent k p`. Our current definition would then correspond to `convex_independent ℝ p`.

## Tags

independence, convex position
-/

open_locale affine big_operators classical
open finset

@[simp] lemma set.mem_iff_nonempty_of_subsingleton {α : Type*} [subsingleton α] {s : set α}
  {x : α} :
  x ∈ s ↔ s.nonempty :=
begin
  refine ⟨λ hx, ⟨x, hx⟩, _⟩,
  rintro ⟨y, hy⟩,
  rwa subsingleton.elim x y,
end


variables {V : Type*} [add_comm_group V] [module ℝ V]
          {ι : Type*} {s t : set V}

/-- An indexed family is said to be convexly independent if every point only belongs to convex hulls
of sets containing it. -/
def convex_independent (p : ι → V) : Prop :=
∀ (s : set ι) (x : ι), p x ∈ convex_hull (p '' s) → x ∈ s

/-- A family with at most one point is affinely independent. -/
lemma convex_independent_of_subsingleton [subsingleton ι] (p : ι → V) :
  convex_independent p :=
λ s x hx, begin
  have : (convex_hull (p '' s)).nonempty := ⟨p x, hx⟩,
  rw [convex_hull_nonempty_iff, set.nonempty_image_iff] at this,
  rwa set.mem_iff_nonempty_of_subsingleton,
end

lemma convex_independent_iff_finset (p : ι → V) :
  convex_independent p ↔ ∀ (s : finset ι) (x : ι), p x ∈ convex_hull (s.image p : set V) → x ∈ s :=
begin
  split,
  { refine λ hc s x hx, hc s x _,
    rwa finset.coe_image at hx },
  refine λ h s x hx,  _,
  sorry --use Carathéodory
  --have := convex_hull_subset_union _ hx,
end

/-- A family is convexly independent if and only if any convex combinations (with sum of weights
`1`) that evaluate to the same point have equal `set.indicator`. -/
lemma convex_independent_iff_indicator_eq_of_affine_combination_eq (p : ι → V) :
  convex_independent p ↔ ∀ (s₁ s₂ : finset ι) (w₁ w₂ : ι → ℝ), (∀ i, 0 ≤ w₁ i) → (∀ i, 0 ≤ w₂ i) →
    ∑ i in s₁, w₁ i = 1 → ∑ i in s₂, w₂ i = 1 →
    s₁.affine_combination p w₁ = s₂.affine_combination p w₂ →
    set.indicator ↑s₁ w₁ = set.indicator ↑s₂ w₂ :=
begin
  split,
  { intros ha s₁ s₂ w₁ w₂ hw₁₀ hw₂₀ hw₁ hw₂ heq,
    ext i,
    by_cases hi : i ∈ s₁ ∪ s₂,
    { rw ←sub_eq_zero,
      rw set.sum_indicator_subset _ (finset.subset_union_left s₁ s₂) at hw₁,
      rw set.sum_indicator_subset _ (finset.subset_union_right s₁ s₂) at hw₂,
      have hws : ∑ i in s₁ ∪ s₂, (set.indicator ↑s₁ w₁ - set.indicator ↑s₂ w₂) i = 0,
      { simp [hw₁, hw₂] },
      rw [finset.affine_combination_indicator_subset _ _ (finset.subset_union_left s₁ s₂),
          finset.affine_combination_indicator_subset _ _ (finset.subset_union_right s₁ s₂),
          ←@vsub_eq_zero_iff_eq V, finset.affine_combination_vsub] at heq,
      exact ha (s₁ ∪ s₂) (set.indicator ↑s₁ w₁ - set.indicator ↑s₂ w₂) hws heq i hi },
    { rw [←finset.mem_coe, finset.coe_union] at hi,
      simp [mt (set.mem_union_left ↑s₂) hi, mt (set.mem_union_right ↑s₁) hi] } },
  { intros ha s w hw hs i0 hi0,
    let w₁ : ι → := function.update (function.const ι 0) i0 1,
    have hw₁ : ∑ i in s, w₁ i = 1,
    { rw [finset.sum_update_of_mem hi0, finset.sum_const_zero, add_zero] },
    have hw₁s : s.affine_combination p w₁ = p i0 :=
      s.affine_combination_of_eq_one_of_eq_zero w₁ p hi0 (function.update_same _ _ _)
                                                (λ _ _ hne, function.update_noteq hne _ _),
    let w₂ := w + w₁,
    have hw₂ : ∑ i in s, w₂ i = 1,
    { simp [w₂, finset.sum_add_distrib, hw, hw₁] },
    have hw₂s : s.affine_combination p w₂ = p i0,
    { simp [w₂, ←finset.weighted_vsub_vadd_affine_combination, hs, hw₁s] },
    replace ha := ha s s w₂ w₁ hw₂ hw₁ (hw₁s.symm ▸ hw₂s),
    have hws : w₂ i0 - w₁ i0 = 0,
    { rw ←finset.mem_coe at hi0,
      rw [←set.indicator_of_mem hi0 w₂, ←set.indicator_of_mem hi0 w₁, ha, sub_self] },
    simpa [w₂] using hws }
end

#exit

variables {k}

/-- An affinely independent family is injective, if the underlying
ring is nontrivial. -/
protected lemma convex_independent.injective [nontrivial] {p : ι → V}
  (ha : convex_independent p) :
  function.injective p :=
begin
  intros i j hij,
  rw convex_independent_iff_linear_independent_vsub _ _ j at ha,
  by_contra hij',
  exact ha.ne_zero ⟨i, hij'⟩ (vsub_eq_zero_iff_eq.mpr hij)
end

/-- If a family is affinely independent, so is any subfamily given by
composition of an embedding into index type with the original
family. -/
lemma convex_independent.comp_embedding {ι2 : Type*} (f : ι2 ↪ ι) {p : ι → V}
    (ha : convex_independent p) : convex_independent (p ∘ f) :=
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
protected lemma convex_independent.subtype {p : ι → V}
    (ha : convex_independent p) (s : set ι) : convex_independent (λ i : s, p i) :=
ha.comp_embedding (embedding.subtype _)

/-- If an indexed family of points is affinely independent, so is the
corresponding set of points. -/
protected lemma convex_independent.range {p : ι → V} (ha : convex_independent p) :
  convex_independent (λ x, x : set.range p → P) :=
begin
  let f : set.range p → ι := λ x, x.property.some,
  have hf : ∀ x, p (f x) = x := λ x, x.property.some_spec,
  let fe : set.range p ↪ ι := ⟨f, λ x₁ x₂ he, subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩,
  convert ha.comp_embedding fe,
  ext,
  simp [hf]
end

/-- If a set of points is affinely independent, so is any subset. -/
protected lemma convex_independent.mono {s t : set P}
  (ha : convex_independent (λ x, x : t → P)) (hs : s ⊆ t) :
  convex_independent (λ x, x : s → P) :=
ha.comp_embedding (s.embedding_of_subset t hs)

/-- If the range of an injective indexed family of points is affinely
independent, so is that family. -/
lemma convex_independent.of_set_of_injective {p : ι → V}
  (ha : convex_independent (λ x, x : set.range p → P)) (hi : function.injective p) :
  convex_independent p :=
ha.comp_embedding
  (⟨λ i, ⟨p i, set.mem_range_self _⟩, λ x y h, hi (subtype.mk_eq_mk.1 h)⟩ : ι ↪ set.range p)

/-- If a family is affinely independent, and the spans of points
indexed by two subsets of the index type have a point in common, those
subsets of the index type have an element in common, if the underlying
ring is nontrivial. -/
lemma convex_independent.exists_mem_inter_of_exists_mem_inter_affine_span [nontrivial]
    {p : ι → V} (ha : convex_independent p) {s1 s2 : set ι} {p0 : P}
    (hp0s1 : p0 ∈ affine_span (p '' s1)) (hp0s2 : p0 ∈ affine_span (p '' s2)):
  ∃ (i : ι), i ∈ s1 ∩ s2 :=
begin
  rw set.image_eq_range at hp0s1 hp0s2,
  rw [mem_affine_span_iff_eq_affine_combination,
      ←finset.eq_affine_combination_subset_iff_eq_affine_combination_subtype] at hp0s1 hp0s2,
  rcases hp0s1 with ⟨fs1, hfs1, w1, hw1, hp0s1⟩,
  rcases hp0s2 with ⟨fs2, hfs2, w2, hw2, hp0s2⟩,
  rw convex_independent_iff_indicator_eq_of_affine_combination_eq at ha,
  replace ha := ha fs1 fs2 w1 w2 hw1 hw2 (hp0s1 ▸ hp0s2),
  have hnz : ∑ i in fs1, w1 i ≠ 0 := hw1.symm ▸ one_ne_zero,
  rcases finset.exists_ne_zero_of_sum_ne_zero hnz with ⟨i, hifs1, hinz⟩,
  simp_rw [←set.indicator_of_mem (finset.mem_coe.2 hifs1) w1, ha] at hinz,
  use [i, hfs1 hifs1, hfs2 (set.mem_of_indicator_ne_zero hinz)]
end

/-- If a family is affinely independent, the spans of points indexed
by disjoint subsets of the index type are disjoint, if the underlying
ring is nontrivial. -/
lemma convex_independent.affine_span_disjoint_of_disjoint [nontrivial] {p : ι → V}
    (ha : convex_independent p) {s1 s2 : set ι} (hd : s1 ∩ s2 = ∅) :
  (affine_span (p '' s1) : set P) ∩ affine_span (p '' s2) = ∅ :=
begin
  by_contradiction hne,
  change (affine_span (p '' s1) : set P) ∩ affine_span (p '' s2) ≠ ∅ at hne,
  rw set.ne_empty_iff_nonempty at hne,
  rcases hne with ⟨p0, hp0s1, hp0s2⟩,
  cases ha.exists_mem_inter_of_exists_mem_inter_affine_span hp0s1 hp0s2 with i hi,
  exact set.not_mem_empty i (hd ▸ hi)
end

/-- If a family is affinely independent, a point in the family is in
the span of some of the points given by a subset of the index type if
and only if that point's index is in the subset, if the underlying
ring is nontrivial. -/
@[simp] protected lemma convex_independent.mem_affine_span_iff [nontrivial] {p : ι → V}
    (ha : convex_independent p) (i : ι) (s : set ι) :
  p i ∈ affine_span (p '' s) ↔ i ∈ s :=
begin
  split,
  { intro hs,
    have h := convex_independent.exists_mem_inter_of_exists_mem_inter_affine_span
      ha hs (mem_affine_span (set.mem_image_of_mem _ (set.mem_singleton _))),
    rwa [←set.nonempty_def, set.inter_singleton_nonempty] at h },
  { exact λ h, mem_affine_span (set.mem_image_of_mem p h) }
end

/-- If a family is affinely independent, a point in the family is not
in the affine span of the other points, if the underlying ring is
nontrivial. -/
lemma convex_independent.not_mem_affine_span_diff [nontrivial] {p : ι → V}
    (ha : convex_independent p) (i : ι) (s : set ι) :
  p i ∉ affine_span (p '' (s \ {i})) :=
by simp [ha]

end convex_independent

section field

variables {k : Type*} {V : Type*} {P : Type*} [field] [add_comm_group V] [module V]
variables [affine_space V P] {ι : Type*}
include V

/-- An affinely independent set of points can be extended to such a
set that spans the whole space. -/
lemma exists_subset_convex_independent_affine_span_eq_top {s : set P}
  (h : convex_independent (λ p, p : s → P)) :
  ∃ t : set P, s ⊆ t ∧ convex_independent (λ p, p : t → P) ∧ affine_span t = ⊤ :=
begin
  rcases s.eq_empty_or_nonempty with rfl | ⟨p₁, hp₁⟩,
  { have p₁ : P := add_torsor.nonempty.some,
    let hsv := basis.of_vector_space V,
    have hsvi := hsv.linear_independent,
    have hsvt := hsv.span_eq,
    rw basis.coe_of_vector_space at hsvi hsvt,
    have h0 : ∀ v : V, v ∈ (basis.of_vector_space_index _ _) → v ≠ 0,
    { intros v hv, simpa using hsv.ne_zero ⟨v, hv⟩ },
    rw linear_independent_set_iff_convex_independent_vadd_union_singleton h0 p₁ at hsvi,
    exact ⟨{p₁} ∪ (λ v, v +ᵥ p₁) '' _, set.empty_subset _, hsvi,
         affine_span_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt⟩ },
  { rw convex_independent_set_iff_linear_independent_vsub hp₁ at h,
    let bsv := basis.extend h,
    have hsvi := bsv.linear_independent,
    have hsvt := bsv.span_eq,
    rw basis.coe_extend at hsvi hsvt,
    have hsv := h.subset_extend (set.subset_univ _),
    have h0 : ∀ v : V, v ∈ (h.extend _) → v ≠ 0,
    { intros v hv, simpa using bsv.ne_zero ⟨v, hv⟩ },
    rw linear_independent_set_iff_convex_independent_vadd_union_singleton h0 p₁ at hsvi,
    refine ⟨{p₁} ∪ (λ v, v +ᵥ p₁) '' h.extend (set.subset_univ _), _, _⟩,
    { refine set.subset.trans _ (set.union_subset_union_right _ (set.image_subset _ hsv)),
      simp [set.image_image] },
    { use [hsvi, affine_span_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt] } }
end

variables (k)

/-- Two different points are affinely independent. -/
lemma convex_independent_of_ne {p₁ p₂ : P} (h : p₁ ≠ p₂) : convex_independent ![p₁, p₂] :=
begin
  rw convex_independent_iff_linear_independent_vsub ![p₁, p₂] 0,
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

protected lemma convex_independent.mono (hs : convex_independent (λ p, p : s → V)) (hts : t ⊆ s) :
  convex_independent (λ p, p : t → V) :=
begin
  rintro s x hs,
  sorry
end

lemma convex_independent_set_iff (A : set E) :
  convex_independent (λ p, p : A → V) ↔ ∀ s, s ⊆ A → A ∩ convex_hull s ⊆ s :=
begin
  split,
  { rintro h s hs x ⟨hx₁, hx₂⟩,
    have := h.mono hs,
    /-suffices H : x ∈ convex_hull ((λ (p : A), ↑p) '' {x : A | ↑x ∈ s}),
    {
      have := h {x : A | ↑x ∈ s},
      sorry
    },-/
    sorry

    --simpa using h (s.attach.image (λ x, ⟨x.1, hs x.2⟩)) ⟨_, hx₁⟩ _,
    --convert hx₂,
    --ext y,
    --simpa [←and_assoc] using @hs y
    },
  { intros h s x hs,
    simpa using h (s.image coe) (by simp) ⟨x.2, by simpa using hs⟩ }
end

lemma convex_independent_set_iff' (A : set E) :
  convex_independent (λ p, p : A → V) ↔ ∀ x ∈ A, x ∉ convex_hull (A \ {x}) :=
begin
  rw convex_independent_set_iff,
  split,
  { rintro hA x hxA hx,
    exact (hA _ (set.diff_subset _ _) ⟨hxA, hx⟩).2 (set.mem_singleton _) },
  rintro hA s hs x ⟨hxA, hxs⟩,
  by_contra h,
  exact hA _ hxA (convex_hull_mono (set.subset_diff_singleton hs h) hxs),
end

-- TODO (Bhavik): move these two, and use them to prove the old versions
lemma nontrivial_sum_of_affine_independent' {p : ι → V} {s : finset ι}
  (ha : affine_independent ℝ p) (w : ι → ℝ)
  (hw₀ : ∑ i in s, w i = 0) (hw₁ : ∑ i in s, w i • p i = 0) :
∀ i ∈ s, w i = 0 :=
begin
  refine ha _ _ hw₀ _,
  rw [finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw₀ (0 : V),
    finset.weighted_vsub_of_point_apply],
  simpa only [vsub_eq_sub, sub_zero, sum_finset_coe (λ i, w i • p i)],
end

lemma unique_combination' {p : ι → V} (s : finset ι)
  (ha : affine_independent ℝ p)
  (w₁ w₂ : ι → ℝ) (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1)
  (same : ∑ i in s, w₁ i • p i = ∑ i in s, w₂ i • p i) :
  ∀ i ∈ s, w₁ i = w₂ i :=
begin
  let w := w₁ - w₂,
  suffices : ∀ i ∈ X, w i = 0,
  { intros i hi,
    apply eq_of_sub_eq_zero (this i hi) },
  apply nontrivial_sum_of_affine_independent' hX,
  { change ∑ i in X, (w₁ i - w₂ i) = _,
    rw [finset.sum_sub_distrib, hw₁, hw₂, sub_self] },
  { change ∑ i in X, (w₁ i - w₂ i) • p i = _,
    simp_rw [sub_smul, finset.sum_sub_distrib, same, sub_self] }
end

lemma affine_independent.convex_independent {p : ι → V} (hp : affine_independent ℝ p) :
  convex_independent p :=
begin
  intros s x hx,
  by_contra,
  sorry
  /-
  rw [finset.convex_hull_eq] at hx,
  rcases hx with ⟨w, hw₀, hw₁, x_eq⟩,
  have : set.inj_on p s := λ x hx y hy h, injective_of_affine_independent hp h,
  rw finset.center_mass_eq_of_sum_1 _ _ hw₁ at x_eq,
  rw finset.sum_image ‹set.inj_on p s› at hw₁,
  rw finset.sum_image ‹set.inj_on p s› at x_eq,
  dsimp at hw₁ x_eq,
  simp only [and_imp, finset.mem_image, forall_apply_eq_imp_iff₂, exists_imp_distrib] at hw₀,
  let w₀ : ι → ℝ := λ i, if i ∈ s then w (p i) else 0,
  let w₁ : ι → ℝ := λ i, if x = i then 1 else 0,
  have thing : _ = _ := unique_combination' (insert x s) hp w₀ w₁ _ _ _ _ (mem_insert_self _ _),
  { change ite _ _ _ = ite _ _ _ at thing,
    simpa [h] using thing },
  { rwa [sum_insert_of_eq_zero_if_not_mem, sum_extend_by_zero s],
    simp [h] },
  { simp [sum_ite_eq] },
  { simpa [sum_insert_of_eq_zero_if_not_mem, h, ite_smul, sum_extend_by_zero s] }-/
end
