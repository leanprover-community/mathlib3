import analysis.convex.basic
import linear_algebra.finite_dimensional

universes u

open set finset
open_locale big_operators

lemma set.subset_subset_Union
  {E : Type*} {A : set E} {ι : Sort*} {f : ι → set E} (i : ι) (h : A ⊆ f i) : A ⊆ ⋃ (i : ι), f i :=
begin
  transitivity,
  exact h,
  exact subset_Union f i,
end

open set finite_dimensional

variables {E : Type u} [decidable_eq E] [add_comm_group E] [vector_space ℝ E] [finite_dimensional ℝ E]

-- a basic fact about convex hulls of finsets.
lemma convex_coefficients (t : finset E) (x : E) :
  x ∈ convex_hull (↑t : set E) ↔
    ∃ f : E → ℝ, (∀ y, 0 ≤ f y) ∧ (∑ e in t, f e = 1) ∧ (∑ e in t, f e • e = x) :=
begin
  fsplit,
  { intro m,
    rw set.finite.convex_hull_eq (finite_to_set t) at m,
    obtain ⟨w, w_nonneg, w_sum_one, w_center⟩ := m,
    let w' : E → ℝ := λ z, if z ∈ t then w z else 0,
    refine ⟨w', _, _, _⟩,
    { intro y, by_cases y ∈ t,
      { convert w_nonneg y h, simp [w', if_pos, h], },
      { simp [w', if_neg, h], }, },
    { sorry, },
    { sorry, }, },
  sorry,
end

-- a basic fact about linear algebra!
lemma exists_nontrivial_relation_of_dim_lt_card {t : finset E} (h : findim ℝ E < t.card) :
  ∃ f : E → ℝ, ∑ e in t, f e • e = 0 ∧ ∃ x ∈ t, f x ≠ 0 :=
begin
  have := mt finset_card_le_findim_of_linear_independent (by { simpa using h }),
  rw linear_dependent_iff at this,
  obtain ⟨s, g, sum, z, zm, nonzero⟩ := this,
  -- Now we have to extend `g` to all of `t`, then to all of `E`.
  let f : E → ℝ := λ x, if h : x ∈ t then if (⟨x, h⟩ : (↑t : set E)) ∈ s then g ⟨x, h⟩ else 0 else 0,
  -- and finally clean up the mess caused by the extension.
  refine ⟨f, _, _⟩,
  { sorry, },
  { sorry, },
end

lemma exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card {t : finset E} (h : findim ℝ E + 1 < t.card) :
  ∃ f : E → ℝ, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x ∈ t, f x ≠ 0 :=
begin
  -- pick an element x₀ ∈ t,
  -- apply the previous lemma to the other xᵢ - x₀,
  -- to obtain a function `f`
  -- and then adjust f x₀ := - others.sum f
  sorry
end

lemma exists_pos_of_sum_zero_of_exists_nonzero {F : Type*} [decidable_eq F] {t : finset F}
  (f : F → ℝ) (h₁ : ∑ e in t, f e = 0) (h₂ : ∃ x ∈ t, f x ≠ 0) :
  ∃ x ∈ t, 0 < f x :=
begin
  contrapose! h₁,
  obtain ⟨x, m, x_nz⟩ : ∃ x ∈ t, f x ≠ 0 := h₂,
  apply ne_of_lt,
  calc ∑ e in t, f e < ∑ e in t, 0 : by { apply sum_lt_sum h₁ ⟨x, m, lt_of_le_of_ne (h₁ x m) x_nz⟩ }
                 ... = 0           : by rw [sum_const, nsmul_zero],
end

lemma exists_relation_sum_zero_pos_coefficient {t : finset E} (h : findim ℝ E + 1 < t.card) :
  ∃ f : E → ℝ, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x ∈ t, 0 < f x :=
begin
  obtain ⟨f, sum, total, nonzero⟩ := exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card h,
  exact ⟨f, sum, total, exists_pos_of_sum_zero_of_exists_nonzero f total nonzero⟩,
end

namespace caratheodory

-- All the sorries here are very doable!
lemma mem_convex_hull_erase {t : finset E} (h : findim ℝ E + 1 < t.card) {x : E} (m : x ∈ convex_hull (↑t : set E)) :
  ∃ (y : (↑t : set E)), x ∈ convex_hull (↑(t.erase y) : set E) :=
begin
   obtain ⟨f, fpos, fsum, rfl⟩ := (convex_coefficients _ _).1 m, clear m,
   obtain ⟨g, gcombo, gsum, gpos⟩ := exists_relation_sum_zero_pos_coefficient h, clear h,
   let s := t.filter (λ z : E, 0 < g z),
   have : s.nonempty := sorry,
   obtain ⟨i₀, mem, w⟩ := s.exists_max_image (λ z, f z / g z) this,
   let k : E → ℝ := λ z, f z - (f i₀ / g i₀) * g z,
   have : k i₀ = 0 := sorry,
   use i₀,
   { simp,
     sorry, },
   { apply (convex_coefficients _ _).2,
     { refine ⟨k, _, _, _⟩,
       { sorry },
       { sorry },
       { sorry }, },
     { assumption, },
     { assumption, }, },
end

lemma step (t : finset E) (h : findim ℝ E + 1 < t.card) :
  convex_hull (↑t : set E) = ⋃ (x : (↑t : set E)), convex_hull ↑(t.erase x) :=
begin
  apply set.subset.antisymm,
  { intros x m',
    obtain ⟨y, m⟩ := mem_convex_hull_erase h m',
    exact mem_Union.2 ⟨y, m⟩, },
  { convert Union_subset _,
    intro x,
    apply convex_hull_mono, simp, }
end

lemma shrink' (t : finset E) (k : ℕ) (h : t.card = findim ℝ E + 1 + k) :
  convex_hull (↑t : set E) ⊆
    ⋃ (t' : finset E) (w : t' ⊆ t) (b : t'.card ≤ findim ℝ E + 1), convex_hull ↑t' :=
begin
  induction k with k ih generalizing t,
  { apply subset_subset_Union t,
    apply subset_subset_Union (set.subset.refl _),
    exact subset_subset_Union (le_of_eq h) (subset.refl _), },
  rw step _ (by { rw h, simp, } : findim ℝ E + 1 < t.card),
  apply Union_subset,
  intro i,
  transitivity,
  { apply ih,
    rw [card_erase_of_mem, h, nat.pred_succ],
    exact i.2, },
  { apply Union_subset_Union,
    intro t',
    apply Union_subset_Union_const,
    exact λ h, set.subset.trans h (erase_subset _ _), }
end

lemma shrink (t : finset E) :
  convex_hull (↑t : set E) ⊆
    ⋃ (t' : finset E) (w : t' ⊆ t) (b : t'.card ≤ findim ℝ E + 1), convex_hull ↑t' :=
begin
  by_cases h : t.card ≤ findim ℝ E + 1,
  { apply subset_subset_Union t,
    apply subset_subset_Union (set.subset.refl _),
    exact subset_subset_Union h (set.subset.refl _), },
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

/--
Carathéodory's convexity theorem.

The convex hull of a set `s` in ℝᵈ is the union of the convex hulls of the (d+1)-tuples in `s`.
-/
theorem caratheodory (s : set E) :
  convex_hull s = ⋃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1), convex_hull ↑t :=
begin
  apply set.subset.antisymm,
  apply caratheodory_le,
  convert Union_subset _,
  intro t,
  convert Union_subset _,
  intro ss,
  convert Union_subset _,
  intro b,
  exact convex_hull_mono ss,
end
