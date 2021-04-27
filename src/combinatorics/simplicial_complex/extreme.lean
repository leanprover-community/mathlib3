import tactic
import data.real.basic
import linear_algebra.affine_space.independent
import linear_algebra.std_basis
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.affine_space.combination
import linear_algebra.finite_dimensional
import algebra.module.linear_map
import analysis.convex.topology
import analysis.normed_space.operator_norm
import combinatorics.simplicial_complex.dump
import combinatorics.simplicial_complex.to_move.topology
import combinatorics.simplicial_complex.convex_independence

open_locale classical affine big_operators
open set
--TODO: Generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B C : set E}
  {X : finset E}

theorem geometric_hahn_banach_closed_point {A : set E} {x : E}
  (hA₁ : convex A) (hA₂ : is_closed A)
  (disj : x ∉ A) :
  ∃ (f : E →L[ℝ] ℝ) (s : ℝ), (∀ a ∈ A, f a < s) ∧ s < f x := sorry

theorem geometric_hahn_banach_open_point {A : set E} {x : E}
  (hA₁ : convex A) (hA₂ : is_open A)
  (disj : x ∉ A) :
  ∃ (f : E →L[ℝ] ℝ), (∀ a ∈ A, f a < f x) := sorry

theorem geometric_hahn_banach_point_open {x : E} {B : set E}
  (hB₁ : convex B) (hB₂ : is_open B)
  (disj : x ∉ B) :
  ∃ (f : E →L[ℝ] ℝ), (∀ b ∈ B, f x < f b) :=
let ⟨f, hf⟩ := geometric_hahn_banach_open_point hB₁ hB₂ disj in ⟨-f, by simpa⟩

lemma eq_left_end_iff_eq_right_end_aux {x₁ x₂ : E} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : a + b = 1) (hx : a • x₁ + b • x₂ = x) :
    x = x₁ ↔ x = x₂ :=
begin
  suffices h : ∀ {a b : ℝ}, a ≠ 0 → b ≠ 0 → ∀ {x₁ x₂ : E}, a + b = 1 → a • x₁ + b • x₂ = x →
    x =x₁ → x = x₂,
  { use h ha hb hab hx,
    rw add_comm at hab hx,
    exact h hb ha hab hx },
  rintro a b ha hb x₁ x₂ hab hx rfl,
  apply smul_injective hb,
  rw [←add_right_inj (a • x), hx, ←add_smul, hab, one_smul],
  sorry,
end
/--
A set B is extreme to a set A if no affine combination of points in A \ B is in B. -/
def is_extreme (A B : set E) :
  Prop :=
B ⊆ A ∧ ∀ x₁ x₂ ∈ A, ∀ x ∈ B, x ∈ segment x₁ x₂ → x ≠ x₁ → x ≠ x₂ → x₁ ∈ B ∧ x₂ ∈ B

lemma extreme_set_iff :
  is_extreme A B ↔ B ⊆ A ∧ ∀ x₁ x₂ ∈ A, ∀ x ∈ B, (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 1 ∧
  a • x₁ + b • x₂ = x) → x₁ ∈ B ∧ x₂ ∈ B :=
begin
  split,
  { rintro hAB,
    use hAB.1,
    rintro x₁ x₂ hx₁A hx₂A x hxB ⟨a, b, ha, hb, hab, hx⟩,
    by_cases hxx₁ : x = x₁,
    { rw [←hxx₁, ←(eq_left_end_iff_eq_right_end_aux (ne_of_gt ha) (ne_of_gt hb) hab hx).1 hxx₁],
      exact ⟨hxB, hxB⟩ },
    exact hAB.2 x₁ x₂ hx₁A hx₂A x hxB ⟨a, b, le_of_lt ha, le_of_lt hb, hab, hx⟩ hxx₁ (λ hxx₂,
      hxx₁ ((eq_left_end_iff_eq_right_end_aux (ne_of_gt ha) (ne_of_gt hb) hab hx).2 hxx₂)) },
  rintro ⟨hBA, hAB⟩,
  use hBA,
  rintro x₁ x₂ hx₁A hx₂A x hxB ⟨a, b, ha, hb, hab, hx⟩ hxx₁ hxx₂,
  refine hAB x₁ x₂ hx₁A hx₂A x hxB ⟨a, b, lt_of_le_of_ne ha _, lt_of_le_of_ne hb _, hab, hx⟩,
  { rintro rfl,
    rw zero_smul at hx,
    rw zero_add at hab hx,
    rw [hab, one_smul] at hx,
    exact hxx₂ hx.symm },
  rintro rfl,
  rw zero_smul at hx,
  rw add_zero at hab hx,
  rw [hab, one_smul] at hx,
  exact hxx₁ hx.symm
end

lemma is_extreme.refl :
  reflexive (is_extreme : set E → set E → Prop) :=
λ A, ⟨subset.refl _, λ x₁ x₂ hx₁A hx₂A x hxA hx hxx₁ hxx₂, ⟨hx₁A, hx₂A⟩⟩

lemma is_extreme.trans :
  transitive (is_extreme : set E → set E → Prop) :=
begin
  rintro A B C ⟨hBA, hAB⟩ ⟨hCB, hBC⟩,
  use subset.trans hCB hBA,
  rintro x₁ x₂ hx₁A hx₂A x hxC hx hxx₁ hxx₂,
  obtain ⟨hx₁B, hx₂B⟩ := hAB x₁ x₂ hx₁A hx₂A x (hCB hxC) hx hxx₁ hxx₂,
  exact hBC x₁ x₂ hx₁B hx₂B x hxC hx hxx₁ hxx₂,
end

lemma is_extreme.antisymm :
  anti_symmetric (is_extreme : set E → set E → Prop) :=
λ A B hAB hBA, subset.antisymm hBA.1 hAB.1

instance : is_partial_order (set E) is_extreme :=
{ refl := is_extreme.refl,
  trans := is_extreme.trans,
  antisymm := is_extreme.antisymm }

lemma is_extreme.convex_diff (hA : convex A) (hAB : is_extreme A B) :
  convex (A \ B) :=
begin
  rw convex_iff_segment_subset,
  rintro x₁ x₂ ⟨hx₁A, hx₁B⟩ ⟨hx₂A, hx₂B⟩ x hx,
  refine ⟨hA.segment_subset hx₁A hx₂A hx, λ hxB, hx₁B (hAB.2 x₁ x₂ hx₁A hx₂A x hxB hx _ _).1⟩,
  { rintro rfl,
    exact hx₁B hxB },
  { rintro rfl,
    exact hx₂B hxB }
end

def set.extreme_points (A : set E) :
  set E :=
{x ∈ A | ∀ (x₁ x₂ ∈ A), x ∈ segment x₁ x₂ → x = x₁ ∨ x = x₂}

lemma extreme_point_iff :
  x ∈ A.extreme_points ↔ x ∈ A ∧ ∀ (x₁ x₂ ∈ A), x ∈ segment x₁ x₂ → x = x₁ ∨ x = x₂ :=
by refl

lemma extreme_point_iff_extreme_singleton :
  x ∈ A.extreme_points ↔ is_extreme A {x} :=
begin
  split,
  { rintro ⟨hxA, hx⟩,
    use singleton_subset_iff.2 hxA,
    rintro x₁ x₂ hx₁A hx₂A y (rfl : y = x) hxs hx₁ hx₂,
    exfalso,
    cases hx x₁ x₂ hx₁A hx₂A hxs,
    exacts [hx₁ h, hx₂ h] },
  { rintro hx,
    use singleton_subset_iff.1 hx.1,
    rintro x₁ x₂ hx₁ hx₂ hxs,
    by_contra,
    push_neg at h,
    exact h.1 (hx.2 x₁ x₂ hx₁ hx₂ x rfl hxs h.1 h.2).1.symm }
end

lemma extreme_points_subset :
  A.extreme_points ⊆ A :=
λ x hx, hx.1

@[simp]
lemma extreme_points_empty :
  (∅ : set E).extreme_points = ∅ :=
subset_empty_iff.1 extreme_points_subset

lemma is_extreme.inter (hAB : is_extreme A B) (hAC : is_extreme A C) :
  is_extreme A (B ∩ C) :=
begin
  use subset.trans (inter_subset_left _ _) hAB.1,
  rintro x₁ x₂ hx₁A hx₂A x ⟨hxB, hxC⟩ hx hxx₁ hxx₂,
  obtain ⟨hx₁B, hx₂B⟩ := hAB.2 x₁ x₂ hx₁A hx₂A x hxB hx hxx₁ hxx₂,
  obtain ⟨hx₁C, hx₂C⟩ := hAC.2 x₁ x₂ hx₁A hx₂A x hxC hx hxx₁ hxx₂,
  exact ⟨⟨hx₁B, hx₁C⟩, hx₂B, hx₂C⟩,
end

lemma is_extreme.bInter {F : set (set E)} (hF : F.nonempty)
  (hAF : ∀ B ∈ F, is_extreme A B) :
  is_extreme A (⋂ B ∈ F, B) :=
begin
  obtain ⟨B, hB⟩ := hF,
  use subset.trans (bInter_subset_of_mem hB) (hAF B hB).1,
  rintro x₁ x₂ hx₁A hx₂A x hxF hx hxx₁ hxx₂,
  rw mem_bInter_iff at ⊢ hxF,
  rw mem_bInter_iff,
  have h := λ B hB, (hAF B hB).2 x₁ x₂ hx₁A hx₂A x (hxF B hB) hx hxx₁ hxx₂,
  exact ⟨λ B hB, (h B hB).1, λ B hB, (h B hB).2⟩,
end

lemma is_extreme.sInter {F : set (set E)} (hF : F.nonempty)
  (hAF : ∀ B ∈ F, is_extreme A B) :
  is_extreme A (⋂₀ F) :=
begin
  obtain ⟨B, hB⟩ := hF,
  use subset.trans (sInter_subset_of_mem hB) (hAF B hB).1,
  rintro x₁ x₂ hx₁A hx₂A x hxF hx hxx₁ hxx₂,
  rw mem_sInter at ⊢ hxF,
  rw mem_sInter,
  have h := λ B hB, (hAF B hB).2 x₁ x₂ hx₁A hx₂A x (hxF B hB) hx hxx₁ hxx₂,
  exact ⟨λ B hB, (h B hB).1, λ B hB, (h B hB).2⟩,
end

lemma is_extreme.Inter {ι : Type*} [nonempty ι] {F : ι → set E}
  (hAF : ∀ i : ι, is_extreme A (F i)) :
  is_extreme A (⋂ i : ι, F i) :=
begin
  obtain i := classical.arbitrary ι,
  use Inter_subset_of_subset i (hAF i).1,
  rintro x₁ x₂ hx₁A hx₂A x hxF hx hxx₁ hxx₂,
  rw mem_Inter at ⊢ hxF,
  rw mem_Inter,
  have h := λ i, (hAF i).2 x₁ x₂ hx₁A hx₂A x (hxF i) hx hxx₁ hxx₂,
  exact ⟨λ i, (h i).1, λ i, (h i).2⟩,
end

lemma inter_extreme_points_subset_extreme_points_of_subset (hBA : B ⊆ A) :
  B ∩ A.extreme_points ⊆ B.extreme_points :=
begin
  rintro x ⟨hxB, hxA⟩,
  use hxB,
  rintro x₁ x₂ hx₁ hx₂ hx,
  exact hxA.2 x₁ x₂ (hBA hx₁) (hBA hx₂) hx,
end

lemma is_extreme.extreme_points_eq (hAB : is_extreme A B) :
  B.extreme_points = B ∩ A.extreme_points :=
subset.antisymm (λ x hx, ⟨hx.1, extreme_point_iff_extreme_singleton.2 (is_extreme.trans hAB
  (extreme_point_iff_extreme_singleton.1 hx))⟩)
  (inter_extreme_points_subset_extreme_points_of_subset hAB.1)

lemma is_extreme.extreme_points_subset_extreme_points (hAB : is_extreme A B) :
  B.extreme_points ⊆ A.extreme_points :=
begin
  rw is_extreme.extreme_points_eq hAB,
  exact inter_subset_right _ _,
end

lemma convex.extreme_point_iff_convex_remove (hA : convex A) :
  x ∈ A.extreme_points ↔ x ∈ A ∧ convex (A \ {x}) :=
begin
  use λ hx, ⟨hx.1, convex_remove_of_extreme hA (extreme_point_iff_extreme_singleton.1 hx)⟩,
  split,
  { rintro ⟨hxA, hAx⟩,
    use hxA,
    rintro x₁ x₂ hx₁A hx₂A hx,
    by_contra,
    push_neg at h,
    rw convex_iff_segment_subset at hAx,
    exact (hAx ⟨hx₁A, λ hx₁, h.1 (mem_singleton_iff.2 hx₁.symm)⟩
      ⟨hx₂A, λ hx₂, h.2 (mem_singleton_iff.2 hx₂.symm)⟩ hx).2 rfl },
  exact λ hx, ⟨hx.1, convex_remove_of_extreme hA (extreme_point_iff_extreme_singleton.1 hx)⟩,
end

--probably relaxable
lemma diff_subset_convex_hull_diff_of_convex (hBA : B ⊆ convex_hull A) (hCB : C ⊆ convex_hull B)
  (hC : convex C) :
  B \ C ⊆ convex_hull (A \ C) :=
begin
  rintro x ⟨hxB, hxC⟩,
  have := hBA hxB,
  sorry
end

--provable from the above by induction on C as a singleton is convex
lemma diff_subset_convex_hull_diff_of_finite (hBA : B ⊆ convex_hull A) (hCB : C ⊆ convex_hull B)
  (hC : finite C) :
  B \ C ⊆ convex_hull (A \ C) :=
begin
  rintro x ⟨hxB, hxC⟩,
  have := hBA hxB,
  sorry
end

lemma extreme_points_convex_hull_subset :
  (convex_hull A : set E).extreme_points ⊆ A :=
begin
  rintro x hx,
  have hxA : x ∈ convex_hull A := hx.1,
  rw (convex_convex_hull _).extreme_point_iff_convex_remove at hx,
  by_contra,
  have : convex_hull A ⊆ convex_hull A \ {x} :=
    convex_hull_min (subset_diff.2 ⟨subset_convex_hull _, disjoint_singleton_right.2 h⟩) hx.2,
  exact (this hxA).2 (mem_singleton _),
end

lemma convex.convex_independent_extreme_points (hA : convex A) :
  convex_independent (λ p, p : A.extreme_points → E) :=
(convex_independent_set_iff' _).2 $ λ x hxA hx, (extreme_points_convex_hull_subset
  (inter_extreme_points_subset_extreme_points_of_subset (convex_hull_min
  (subset.trans (diff_subset _ _) extreme_points_subset) hA) ⟨hx, hxA⟩)).2 (mem_singleton _)

lemma convex.convex_remove_iff_not_mem_convex_hull_remove (hA : convex A) :
  convex (A \ {x}) ↔ x ∉ convex_hull (A \ {x}) :=
begin
  split,
  { rintro hA hx,
    rw hA.convex_hull_eq at hx,
    exact hx.2 (mem_singleton _) },
  rintro hx,
  suffices h : A \ {x} = convex_hull (A \ {x}),
  { rw h,
    exact convex_convex_hull _},
  refine subset.antisymm (subset_convex_hull _) _,
  rintro y hy,
  rw ←hA.convex_hull_eq,
  use convex_hull_mono (diff_subset _ _) hy,
  rintro (hyx : y = x),
  rw hyx at hy,
  exact hx hy,
end

lemma convex.extreme_point_iff_mem_diff_convex_hull_remove (hA : convex A) :
  x ∈ A.extreme_points ↔ x ∈ A \ convex_hull (A \ {x}) :=
begin
  rw hA.extreme_point_iff_convex_remove,
  split,
  { rintro ⟨hxA, hx⟩,
    exact ⟨hxA, hA.convex_remove_iff_not_mem_convex_hull_remove.1 hx⟩ },
  rintro ⟨hxA, hx⟩,
  exact ⟨hxA, hA.convex_remove_iff_not_mem_convex_hull_remove.2 hx⟩,
end

lemma eq_extreme_points_convex_hull_iff_convex_independent :
  A = (convex_hull A).extreme_points ↔ convex_independent (λ p, p : A → E) :=
begin
  split,
  { rintro h,
    rw h,
    exact (convex_convex_hull _).convex_independent_extreme_points },
  rintro hA,
  rw convex_independent_set_iff' at hA,
  refine subset.antisymm _ extreme_points_convex_hull_subset,
  rintro x hxA,
  use subset_convex_hull _ hxA,
  by_contra h,
  push_neg at h,
  obtain ⟨x₁, x₂, hx₁, hx₂, hx⟩ := h,
  apply hA _ hxA,
  suffices h : x₁ ∈ convex_hull (A \ {x}) ∧ x₂ ∈ convex_hull (A \ {x}),
  { exact convex_iff_segment_subset.1 (convex_convex_hull _) h.1 h.2 hx.1 },
  sorry --use diff_subset_convex_hull_diff_of_convex or _of_finite on A = A, B = {x₁, x₂}, C = {x}
end

lemma extreme_to_convex_hull_of_affine_independent {s : finset E} (hx : x ∈ s)
  (hs : affine_independent ℝ (λ p, p : (s : set E) → E)) :
  x ∈ (convex_hull ↑s : set E).extreme_points :=
begin
  refine ⟨subset_convex_hull _ hx, _⟩,
  rintro y y' hy hy' t,
  rw finset.convex_hull_eq at hy hy',
  obtain ⟨w, hw₀, hw₁, hy⟩ := hy,
  obtain ⟨w', hw'₀, hw'₁, hy'⟩ := hy',
  rw segment_eq_image at t,
  obtain ⟨θ, hθ₁, hθ₂ : _ + _ = _⟩ := t,
  rw finset.center_mass_eq_of_sum_1 _ _ hw₁ at hy,
  rw finset.center_mass_eq_of_sum_1 _ _ hw'₁ at hy',
  change s.sum (λ i, w i • i) = y at hy,
  change s.sum (λ i, w' i • i) = y' at hy',
  let w'' : E → ℝ := λ t, (1 - θ) * w t + θ * w' t - if t = x then 1 else 0,
  have hw''₁ : s.sum w'' = 0,
  { rw [finset.sum_sub_distrib, finset.sum_add_distrib, ← finset.mul_sum, ← finset.mul_sum, hw₁,
      hw'₁, finset.sum_ite_eq' s, if_pos hx],
    simp },
  have hw''₂ : s.sum (λ i, w'' i • i) = 0,
  { simp only [sub_smul, add_smul, finset.sum_add_distrib, finset.sum_sub_distrib],
    simp only [mul_smul, ←finset.smul_sum, hy, hy'],
    simp only [ite_smul, zero_smul, one_smul, finset.sum_ite_eq', if_pos hx, hθ₂, sub_self] },
  by_contra t,
  push_neg at t,
  suffices hw''₃ : ∀ q ∈ s, w'' q = 0,
  { have : θ = 0 ∨ θ = 1,
    { by_contra hθ,
      push_neg at hθ,
      have : 0 < θ ∧ 0 < 1 - θ,
      { split,
        { apply lt_of_le_of_ne hθ₁.1 hθ.1.symm },
        { rw sub_pos,
          apply lt_of_le_of_ne hθ₁.2 hθ.2 } },
      have both_zero : ∀ q ∈ s, q ≠ x → w q = 0,
      { intros q hq₁ hq₂,
        specialize hw''₃ q hq₁,
        change _ + _ = _ at hw''₃,
        rw if_neg hq₂ at hw''₃,
        simp only [add_zero, neg_zero] at hw''₃,
        rw add_eq_zero_iff'
            (mul_nonneg (le_of_lt this.2) (hw₀ q hq₁))
            (mul_nonneg (le_of_lt this.1) (hw'₀ q hq₁)) at hw''₃,
        rw mul_eq_zero at hw''₃,
        apply or.resolve_left hw''₃.1 (ne_of_gt this.2) },
      have : (1 - θ) * w x + θ * w' x = 1,
      { specialize hw''₃ _ hx,
        change (1 - θ) * w x + θ * w' x - ite _ _ _ = 0 at hw''₃,
        rwa [if_pos rfl, sub_eq_zero] at hw''₃ },
      rw finset.sum_eq_single x at hw₁,
      { rw finset.sum_eq_single x at hy,
        { rw hw₁ at hy,
          apply t.1,
          rw ←hy,
          simp },
        { rintro q hq₁ hq₂,
          rw both_zero q hq₁ hq₂,
          simp },
        { exact λ t, (t hx).elim } },
      { intros q hq₁ hq₂,
        apply both_zero q hq₁ hq₂ },
      { exact λ t, (t hx).elim } },
    rcases this with (rfl | rfl),
    { simp only [add_zero, one_smul, sub_zero, zero_smul] at hθ₂,
      apply t.1 hθ₂.symm },
    { simp only [one_smul, zero_smul, zero_add, sub_self] at hθ₂,
      apply t.2 hθ₂.symm } },
  rw affine_independent_iff_of_fintype at hs,
  let w''' : (s : set E) → ℝ := λ t, w'' (t : E),
  have hw''' : finset.univ.sum w''' = 0,
  { rw coe_sum,
    apply hw''₁ },
  specialize hs w''' hw''' _,
  { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw''' (0 : E),
    rw finset.weighted_vsub_of_point_apply,
    simp only [vsub_eq_sub, sub_zero],
    rw coe_sum _ (λ i, w'' i • i),
    apply hw''₂ },
  rintro q hq,
  exact hs ⟨q, hq⟩,
end

lemma inter_frontier_self_inter_convex_hull_extreme :
  is_extreme (closure A) (closure A ∩ frontier (convex_hull A)) :=
begin
  refine ⟨inter_subset_left _ _, λ x₁ x₂ hx₁A hx₂A x hxA hx hxx₁ hxx₂, ⟨⟨hx₁A, _⟩, hx₂A, _⟩⟩,
  sorry,
  sorry
end

lemma frontier_extreme_to_closure (hA₁ : convex A) (hA₂ : is_closed A) :
  is_extreme A (frontier A) :=
begin
  convert (inter_frontier_self_inter_convex_hull_extreme : is_extreme (closure A)
    (closure A ∩ frontier (convex_hull A))),
  { exact (is_closed.closure_eq hA₂).symm },
  rw [convex.convex_hull_eq hA₁, inter_eq_self_of_subset_right frontier_subset_closure],
end

lemma filter.tendsto.smul_const {α β M : Type*} [topological_space α] [topological_space M]
  [has_scalar M α] [has_continuous_smul M α] {f : β → M} {l : filter β}
  {c : M} (hf : filter.tendsto f l (nhds c)) (a : α) :
  filter.tendsto (λ x, (f x) • a) l (nhds (c • a)) :=
hf.smul tendsto_const_nhds

lemma closure_eq_closure_interior (hA₁ : convex A) (hA₂ : (interior A).nonempty) :
  closure A = closure (interior A) :=
begin
  refine set.subset.antisymm _ (closure_mono interior_subset),
  rintro x,
  obtain ⟨y, hy⟩ := hA₂,
  simp only [mem_closure_iff_seq_limit],
  rintro ⟨z, hzA, hzx⟩,
  use λ n, (1/n.succ : ℝ) • y + (n/n.succ : ℝ) • z n,
  split,
  {
    rintro n,
    --have := (frontier_extreme_to_closure hA₁).2 y (z n) (interior_subset hy) (hzA n),
    sorry
  },
  rw ←zero_add x,
  apply filter.tendsto.add,
  {
    sorry
  },
  rw ←one_smul _ x,
  refine filter.tendsto.smul _ hzx,
  sorry
end

--can be generalized is_extreme.subset_intrinsic_frontier
lemma is_extreme.subset_frontier (hAB : is_extreme A B) (hBA : ¬ A ⊆ B) :
  B ⊆ frontier A :=
begin
  rintro x hxB,
  obtain ⟨y, hyA, hyB⟩ := nonempty_of_ssubset ⟨hAB.1, hBA⟩,
  rw frontier_eq_closure_inter_closure,
  use subset_closure (hAB.1 hxB),
  rw mem_closure_iff_seq_limit,
  let z : ℕ → E := λ n, (1 + 1/n.succ : ℝ) • x - (1/n.succ : ℝ) • y,
  use z,
  split,
  {
    rintro n hzn,
    --have := hAB.2 y (f n) hyA hfn x hxB,
    refine hyB (hAB.2 y (z n) hyA hzn x hxB ⟨1/(↑n + 1)/(1/(↑n + 1) + 1), 1/(1/(↑n + 1) + 1), _, _, _, _⟩
      _ _).1,
    { exact le_of_lt (div_pos nat.one_div_pos_of_nat (add_pos nat.one_div_pos_of_nat (by linarith))),
    },
    {
      exact le_of_lt (one_div_pos.2 (add_pos nat.one_div_pos_of_nat (by linarith))),
    },
    {
      rw [←add_div, div_self],
      exact (ne_of_gt (add_pos nat.one_div_pos_of_nat (by linarith))),
    },
    {
      sorry,
    },
    {
      rintro rfl,
      exact hyB hxB,
    },
    {
      rintro h,
      apply hyB,
      suffices h : x = y,
      { rw ←h, exact hxB },
      suffices h : (1/n.succ : ℝ) • x = (1/n.succ : ℝ) • y,
      { exact smul_injective (ne_of_gt nat.one_div_pos_of_nat) h },
      calc
        (1/n.succ : ℝ) • x
            = -(1 • x) + ((1 • x + (1/n.succ : ℝ) • x) - (1/n.succ : ℝ) • y) + (1/n.succ : ℝ) • y : sorry
        ... = -(1 • x) + ((1 + 1/n.succ : ℝ) • x - (1/n.succ : ℝ) • y) + (1/n.succ : ℝ) • y : sorry
        ... = -(1 • x) + z n + (1/n.succ : ℝ) • y : by refl
        ... = -(1 • x) + x + (1/n.succ : ℝ) • y : by rw h
        ... = (1/n.succ : ℝ) • y : by simp,
    },
  },
  rw ←sub_zero x,
  apply filter.tendsto.sub,
  {
    nth_rewrite 0 ←one_smul _ x,
    apply filter.tendsto.smul_const,
    nth_rewrite 0 ←add_zero (1 : ℝ), --weirdly skips the first two `1`. Might break in the future
    apply filter.tendsto.const_add,
    sorry
  },
  rw ←zero_smul _ y,
  apply filter.tendsto.smul_const,
  sorry
end



--probably belongs in the mathlib file of convex hulls
lemma subset_of_convex_hull_eq_convex_hull_of_linearly_independent {X Y : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E))
  (h : convex_hull ↑X = convex_hull (Y : set E)) :
  X ⊆ Y :=
begin
  rintro x hx,
  have hxextreme := extreme_to_convex_hull_of_affine_independent hx hX,
  rw h at hxextreme,
  exact_mod_cast extreme_points_convex_hull_subset hxextreme,
end

--Keep two linearly_independent in the name?
lemma eq_of_convex_hull_eq_convex_hull_of_linearly_independent
  {X Y : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E))
  (hY : affine_independent ℝ (λ p, p : (Y : set E) → E))
  (h : convex_hull (X : set E) = convex_hull (Y : set E)) :
  X = Y :=
finset.subset.antisymm
  (subset_of_convex_hull_eq_convex_hull_of_linearly_independent hX h)
  (subset_of_convex_hull_eq_convex_hull_of_linearly_independent hY h.symm)

/-! # DANGER ZONE
Unproved, and maybe wrong, lemmas -/

--lemma dimension_lt_of_extreme (hAB : is_extreme A B) (hBA : B ⊂ A) :
--  B.dimension < A.dimension := sorry

lemma is_extreme.closed (hAB : is_extreme A B) (hA : is_closed A) :
  is_closed B :=
begin
  rw ←is_seq_closed_iff_is_closed at ⊢ hA,
  apply is_seq_closed_of_def,
  rintro x y hx hxy,
  sorry -- true? probably not
end

lemma is_extreme.compact (hAB : is_extreme A B) (hA : is_compact A) :
  is_compact B :=
compact_of_is_closed_subset hA (hAB.closed hA.is_closed) hAB.1
