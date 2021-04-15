import combinatorics.simplicial_complex.exposed

open_locale classical affine big_operators
open set
--TODO: Generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B : set E}

namespace affine

--being proven in another branch, so don't need to unsorry it here
theorem geometric_hahn_banach_compact_closed {A B : set E}
  (hA₁ : convex A) (hA₂ : is_compact A)
  (hB₁ : convex B) (hB₂ : is_closed B)
  (disj : disjoint A B) :
  ∃ (f : E →L[ℝ] ℝ) (s t : ℝ), s < t ∧ (∀ b ∈ B, f b < s) ∧ (∀ a ∈ A, t < f a) :=
sorry

theorem geometric_hahn_banach_point_point {x y : E} (hxy : x ≠ y) :
  ∃ (f : E →L[ℝ] ℝ), f x < f y :=
sorry

/--
The Krein-Milman lemma
-/
lemma has_extreme_point_of_convex_of_compact_of_nonempty (hAnemp : A.nonempty)
  (hAcomp : is_compact A) (hAconv : convex A) :
  A.extreme_points.nonempty :=
begin
  suffices h : ∃ B : set E, B.nonempty ∧ is_extreme_set A B ∧
    ∀ C : set E, C.nonempty → is_extreme_set B C → is_extreme_set C B,
  {
    obtain ⟨B, hBnemp, hAB, hBmin⟩ := h,
    obtain ⟨x, hxB⟩ := hBnemp,
    refine ⟨x, extreme_point_iff_extreme_singleton.2 _⟩,
    suffices h : B = {x},
    { rw ←h,
      exact hAB },
    refine eq_singleton_iff_unique_mem.2 ⟨hxB, λ y hyB, _⟩,
    by_contra hyx,
    obtain ⟨l, hl⟩ := geometric_hahn_banach_point_point hyx,
    obtain ⟨z, hzB, hz⟩ := is_compact.exists_forall_ge (compact_of_extreme hAcomp hAB) ⟨x, hxB⟩
      (continuous.continuous_on l.continuous), --contentious. Is `compact_of_extreme` true?
    exact not_le.2 hl (((hBmin {z ∈ B | ∀ w ∈ B, l w ≤ l z} ⟨z, hzB, hz⟩
      (extreme_of_exposed ⟨l, rfl⟩)).1 hyB).2 x hxB),
  },
  suffices h : ∃ B : set E, ∀ C : set E, (C.nonempty ∧ is_extreme_set A C ∧ is_extreme_set B C) →
  (B.nonempty ∧ is_extreme_set A B ∧ is_extreme_set C B),
  sorry,
  apply zorn.exists_maximal_of_chains_bounded,
  {
    rintro F hF,
    use ⋂ C ∈ F, C,
    rintro B hB,
    split,
    {
      sorry
    },
    have : (⋂ (C : set E) (H : C ∈ F), C) = ⋂ (C : set E) (H : C ∈ F ∧ C ⊆ B), C := sorry,
    rw this,
    refine ⟨bInter_extreme_of_extreme _, bInter_extreme_of_extreme _⟩,
    sorry,
    sorry
    /-rintro C ⟨hC, hCB⟩,
    cases zorn.chain.total_of_refl hF hB hC,
    { exact h},
    rw subset.antisymm hCB h.1,
    exact is_extreme_set.refl _,-/
  },
  {
    sorry
  }
end
/-
  refine zorn.exists_maximal_of_chains_bounded _ is_extreme_set.trans,
  rintro F (hF : zorn.chain is_extreme_set F),
  use ⋂ C ∈ F, C,
  rintro B hB,
  have : (⋂ (C : set E) (H : C ∈ F), C) = ⋂ (C : set E) (H : C ∈ F ∧ C ⊆ B), C := sorry,
  rw this,
  apply bInter_extreme_of_extreme,
  rintro C ⟨hC, hCB⟩,
  cases zorn.chain.total_of_refl hF hB hC,
  { exact h},
  rw subset.antisymm hCB h.1,
  exact is_extreme_set.refl _,-/

/--
The Krein-Milman theorem
-/
lemma eq_closure_convex_hull_extreme_points_of_compact_of_convex (hAcomp : is_compact A)
  (hAconv : convex A) :
  A = closure (convex_hull A.extreme_points) :=
begin
  let B := closure (convex_hull A.extreme_points),
  have hBA : B ⊆ A :=
    closure_minimal (convex_hull_min (λ x hx, hx.1) hAconv) (is_compact.is_closed hAcomp),
  refine subset.antisymm _ hBA,
  by_contra hAB,
  have hABdiff : (A \ B).nonempty := nonempty_diff.2 hAB,
  obtain ⟨x, hxA, hxB⟩ := id hABdiff,
  obtain ⟨l, s, t, hst, hs, ht⟩ := geometric_hahn_banach_compact_closed (convex_singleton x)
    compact_singleton (convex.closure (convex_convex_hull _)) is_closed_closure
    (disjoint_singleton_left.2 hxB),
  let C := {y ∈ A | ∀ z ∈ A, l z ≤ l y},
  have hCexp : is_exposed_set A C := ⟨l, rfl⟩,
  obtain ⟨y, hyC⟩ := has_extreme_point_of_convex_of_compact_of_nonempty
    begin
      obtain ⟨z, hzA, hz⟩ := is_compact.exists_forall_ge hAcomp ⟨x, hxA⟩
        (continuous.continuous_on l.continuous),
      exact ⟨z, hzA, hz⟩,
    end
    (compact_of_exposed hAcomp hCexp) (convex_of_exposed hAconv hCexp),
  have := hs _ (subset_closure (subset_convex_hull _
    (extreme_points_subset_extreme_points_of_extreme (extreme_of_exposed hCexp) hyC))),
  have := ht x (mem_singleton _),
  have := hyC.1.2 x hxA,
  linarith,
end

/--
Carathéodory's theorem, the extreme points way
-/
lemma eq_convex_hull_extreme_points_of_compact_of_convex [finite_dimensional ℝ E]
  (hAcomp : is_compact A) (hAconv : convex A) :
  A = convex_hull A.extreme_points :=
begin
  let B := convex_hull A.extreme_points,
  have hBA : B ⊆ A :=
    convex_hull_min (λ x hx, hx.1) hAconv,
  refine subset.antisymm _ hBA,
  by_contra hAB,
  have hABdiff : (A \ B).nonempty := nonempty_diff.2 hAB,
  obtain ⟨x, hxA, hxB⟩ := id hABdiff,
  sorry
end

end affine
