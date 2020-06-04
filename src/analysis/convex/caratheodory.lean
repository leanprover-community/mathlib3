import analysis.convex.basic
import linear_algebra.finite_dimensional

universes u

open set

lemma set.subset_subset_Union
  {E : Type*} {A : set E} {ι : Sort*} {f : ι → set E} (i : ι) (h : A ⊆ f i) : A ⊆ ⋃ (i : ι), f i :=
begin
  transitivity,
  exact h,
  exact subset_Union f i,
end

open set finite_dimensional


variables {E : Type u} [decidable_eq E] [add_comm_group E] [vector_space ℝ E] [finite_dimensional ℝ E]

namespace caratheodory

lemma step (t : finset E) (h : findim ℝ E + 1 < t.card) :
  convex_hull (↑t : set E) = ⋃ (x : (↑t : set E)), convex_hull ↑(t.erase x) :=
-- This is the actual work!
sorry

lemma shrink' (t : finset E) (k : ℕ) (h : t.card = findim ℝ E + 1 + k) :
  convex_hull (↑t : set E) ⊆
    ⋃ (t' : finset E) (w : t' ⊆ t) (b : t'.card ≤ findim ℝ E + 1), convex_hull ↑t' :=
begin
  induction k with k ih generalizing t,
  { apply subset_subset_Union t,
    apply subset_subset_Union (subset.refl _),
    exact subset_subset_Union (le_of_eq h) (subset.refl _), },
  rw step _ (by { rw h, simp, } : findim ℝ E + 1 < t.card),
  apply Union_subset,
  intro i,
  transitivity,
  { apply ih,
    rw [finset.card_erase_of_mem, h, nat.pred_succ],
    exact i.2, },
  { apply Union_subset_Union,
    intro t',
    apply Union_subset_Union_const,
    exact λ h, subset.trans h (finset.erase_subset _ _), }
end

lemma shrink (t : finset E) :
  convex_hull (↑t : set E) ⊆
    ⋃ (t' : finset E) (w : t' ⊆ t) (b : t'.card ≤ findim ℝ E + 1), convex_hull ↑t' :=
begin
  by_cases h : t.card ≤ findim ℝ E + 1,
  { apply subset_subset_Union t,
    apply subset_subset_Union (subset.refl _),
    exact subset_subset_Union h (subset.refl _), },
  simp at h,
  obtain ⟨k, w⟩ := le_iff_exists_add.mp (le_of_lt h), clear h,
  exact shrink' _ _ w,
end


end caratheodory

lemma caratheodory_le (s : set E) :
  convex_hull s ⊆ ⋃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1), convex_hull ↑t :=
begin
  -- First we replace `convex_hull s` with the union of the convex hulls of finite subsets.
  rw convex_hull_eq_union_convex_hull_finite_subsets,
  -- And prove the inclusion for each of those
  apply Union_subset,
  intro r,
  apply Union_subset,
  intro h,
  -- Second, for each convex hull of a finite subset, we shrink it
  transitivity,
  { apply caratheodory.shrink, },
  { -- After that it's just shuffling everything around.
    apply Union_subset,
    intro r',
    apply Union_subset,
    intro h',
    apply Union_subset,
    intro b',
    apply subset_subset_Union r',
    apply subset_subset_Union,
    exact subset.trans h' h,
    apply subset_Union _ b', },
end

theorem caratheodory (s : set E) :
  convex_hull s = ⋃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1), convex_hull ↑t :=
begin
  apply subset.antisymm,
  apply caratheodory_le,
  convert Union_subset _,
  intro t,
  convert Union_subset _,
  intro ss,
  convert Union_subset _,
  intro b,
  exact convex_hull_mono ss,
end
