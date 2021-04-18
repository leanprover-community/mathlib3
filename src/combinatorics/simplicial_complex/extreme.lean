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

/--
A set B is extreme to a set A if no affine combination of points in A \ B is in B. -/
def is_extreme_set (A B : set E) :
  Prop :=
B ⊆ A ∧ ∀ x₁ x₂ ∈ A, ∀ x ∈ B, x ∈ segment x₁ x₂ → x₁ ≠ x → x₂ ≠ x → x₁ ∈ B ∧ x₂ ∈ B

lemma is_extreme_set.refl :
  reflexive (is_extreme_set : set E → set E → Prop) :=
λ A, ⟨subset.refl _, λ x₁ x₂ hx₁A hx₂A x hxA hx hxx₁ hxx₂, ⟨hx₁A, hx₂A⟩⟩

lemma is_extreme_set.trans :
  transitive (is_extreme_set : set E → set E → Prop) :=
begin
  rintro A B C ⟨hBA, hAB⟩ ⟨hCB, hBC⟩,
  use subset.trans hCB hBA,
  rintro x₁ x₂ hx₁A hx₂A x hxC hx hxx₁ hxx₂,
  obtain ⟨hx₁B, hx₂B⟩ := hAB x₁ x₂ hx₁A hx₂A x (hCB hxC) hx hxx₁ hxx₂,
  exact hBC x₁ x₂ hx₁B hx₂B x hxC hx hxx₁ hxx₂,
end

lemma is_extreme_set.antisymm :
  anti_symmetric (is_extreme_set : set E → set E → Prop) :=
λ A B hAB hBA, subset.antisymm hBA.1 hAB.1

instance : is_partial_order (set E) is_extreme_set :=
{ refl := is_extreme_set.refl,
  trans := is_extreme_set.trans,
  antisymm := is_extreme_set.antisymm }

lemma closed_of_extreme (hA : is_closed A) (hAB : is_extreme_set A B) :
  is_closed B :=
begin
  rw ←is_seq_closed_iff_is_closed at ⊢ hA,
  apply is_seq_closed_of_def,
  rintro x y hx hxy,
  sorry -- true?
end

lemma compact_of_extreme (hA : is_compact A) (hAB : is_extreme_set A B) :
  is_compact B :=
compact_of_is_closed_subset hA (closed_of_extreme (is_compact.is_closed hA) hAB) hAB.1

lemma convex_remove_of_extreme (hA : convex A) (hAB : is_extreme_set A B) :
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
{x ∈ A | ∀ (x₁ x₂ ∈ A), x ∈ segment x₁ x₂ → x₁ = x ∨ x₂ = x}

lemma extreme_point_iff :
  x ∈ A.extreme_points ↔ x ∈ A ∧ ∀ (x₁ x₂ ∈ A), x ∈ segment x₁ x₂ → x₁ = x ∨ x₂ = x :=
by refl

lemma extreme_point_iff_extreme_singleton :
  x ∈ A.extreme_points ↔ is_extreme_set A {x} :=
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
    exact h.1 (hx.2 x₁ x₂ hx₁ hx₂ x rfl hxs h.1 h.2).1 }
end

lemma extreme_points_subset :
  A.extreme_points ⊆ A :=
λ x hx, hx.1

@[simp]
lemma extreme_points_empty :
  (∅ : set E).extreme_points = ∅ :=
subset_empty_iff.1 extreme_points_subset

lemma inter_extreme_of_extreme (hAB : is_extreme_set A B) (hAC : is_extreme_set A C) :
  is_extreme_set A (B ∩ C) :=
begin
  use subset.trans (inter_subset_left _ _) hAB.1,
  rintro x₁ x₂ hx₁A hx₂A x ⟨hxB, hxC⟩ hx hxx₁ hxx₂,
  obtain ⟨hx₁B, hx₂B⟩ := hAB.2 x₁ x₂ hx₁A hx₂A x hxB hx hxx₁ hxx₂,
  obtain ⟨hx₁C, hx₂C⟩ := hAC.2 x₁ x₂ hx₁A hx₂A x hxC hx hxx₁ hxx₂,
  exact ⟨⟨hx₁B, hx₁C⟩, hx₂B, hx₂C⟩,
end

lemma bInter_extreme_of_extreme {F : set (set E)} (hF : F.nonempty)
  (hAF : ∀ B ∈ F, is_extreme_set A B) :
  is_extreme_set A (⋂ B ∈ F, B) :=
begin
  obtain ⟨B, hB⟩ := hF,
  use subset.trans (bInter_subset_of_mem hB) (hAF B hB).1,
  rintro x₁ x₂ hx₁A hx₂A x hxF hx hxx₁ hxx₂,
  rw mem_bInter_iff at ⊢ hxF,
  rw mem_bInter_iff,
  have h := λ B hB, (hAF B hB).2 x₁ x₂ hx₁A hx₂A x (hxF B hB) hx hxx₁ hxx₂,
  exact ⟨λ B hB, (h B hB).1, λ B hB, (h B hB).2⟩,
end

lemma sInter_extreme_of_extreme {F : set (set E)} (hF : F.nonempty)
  (hAF : ∀ B ∈ F, is_extreme_set A B) :
  is_extreme_set A (⋂₀ F) :=
begin
  obtain ⟨B, hB⟩ := hF,
  use subset.trans (sInter_subset_of_mem hB) (hAF B hB).1,
  rintro x₁ x₂ hx₁A hx₂A x hxF hx hxx₁ hxx₂,
  rw mem_sInter at ⊢ hxF,
  rw mem_sInter,
  have h := λ B hB, (hAF B hB).2 x₁ x₂ hx₁A hx₂A x (hxF B hB) hx hxx₁ hxx₂,
  exact ⟨λ B hB, (h B hB).1, λ B hB, (h B hB).2⟩,
end

lemma Inter_extreme_of_extreme {ι : Type*} [nonempty ι] {F : ι → set E}
  (hAF : ∀ i : ι, is_extreme_set A (F i)) :
  is_extreme_set A (⋂ i : ι, F i) :=
begin
  obtain i := classical.arbitrary ι,
  use Inter_subset_of_subset i (hAF i).1,
  rintro x₁ x₂ hx₁A hx₂A x hxF hx hxx₁ hxx₂,
  rw mem_Inter at ⊢ hxF,
  rw mem_Inter,
  have h := λ i, (hAF i).2 x₁ x₂ hx₁A hx₂A x (hxF i) hx hxx₁ hxx₂,
  exact ⟨λ i, (h i).1, λ i, (h i).2⟩,
end

lemma extreme_points_eq_inter_extreme_points_of_extreme (hAB : is_extreme_set A B) :
  B.extreme_points = B ∩ A.extreme_points :=
begin
  ext x,
  exact ⟨λ hxB, ⟨hxB.1, extreme_point_iff_extreme_singleton.2 (is_extreme_set.trans hAB
  (extreme_point_iff_extreme_singleton.1 hxB))⟩, λ ⟨hxB, hxA⟩, ⟨hxB, λ x₁ x₂ hx₁B hx₂B hx,
    hxA.2 x₁ x₂ (hAB.1 hx₁B) (hAB.1 hx₂B) hx⟩⟩,
end

lemma extreme_points_subset_extreme_points_of_extreme (hAB : is_extreme_set A B) :
  B.extreme_points ⊆ A.extreme_points :=
begin
  rw extreme_points_eq_inter_extreme_points_of_extreme hAB,
  exact inter_subset_right _ _,
end


--lemma dimension_lt_of_extreme (hAB : is_extreme_set A B) (hBA : B ⊂ A) :
--  B.dimension < A.dimension := sorry

lemma convex_remove_iff_extreme_point (hA : convex A) :
  x ∈ A ∧ convex (A \ {x}) ↔ x ∈ A.extreme_points :=
begin
  split,
  { rintro ⟨hxA, hAx⟩,
    use hxA,
    rintro x₁ x₂ hx₁A hx₂A hx,
    by_contra,
    push_neg at h,
    rw convex_iff_segment_subset at hAx,
    exact (hAx ⟨hx₁A, λ hx₁, h.1 (mem_singleton_iff.2 hx₁)⟩
      ⟨hx₂A, λ hx₂, h.2 (mem_singleton_iff.2 hx₂)⟩ hx).2 rfl },
  exact λ hx, ⟨hx.1, convex_remove_of_extreme hA (extreme_point_iff_extreme_singleton.1 hx)⟩,
end

lemma extreme_points_convex_independent :
  convex_independent (λ p, p : A.extreme_points → E) :=
begin
  rw convex_independent_set_iff,
  rintro X hX x hxA,
  simp,
  have : x ∈ (convex_hull (X : set E)).extreme_points,--true?
  {
    use hxA.2,
    rintro x₁ x₂ hx₁ hx₂ hx,
    refine hxA.1.2 x₁ x₂ _ _ hx,
    sorry,
    sorry,
  },

  sorry
end

lemma eq_extreme_points_convex_hull_iff_convex_independent :
  A = (convex_hull A).extreme_points ↔ convex_independent (λ p, p : A → E) :=
begin
  split,
  { rintro h,
    rw h,
    exact extreme_points_convex_independent },
  rintro hA,
  ext x,
  split,
  {
    rintro hxA,
    use subset_convex_hull _ hxA,
    rintro x₁ x₂ hx₂ hx₂ hx,
    rw convex_independent_set_iff at hA,
    --have := hA {x₁, x₂},
    sorry
  },
  sorry
end

lemma extreme_to_convex_hull_of_affine_independent {s : finset E} (hx : x ∈ s)
  (hs : affine_independent ℝ (λ p, p : (s : set E) → E)) :
  x ∈ (convex_hull ↑s : set E).extreme_points :=
begin
  -- have := convex_independent_of_affine_independent hs _ hx,

  -- rw ←convex_remove_iff_is_extreme (convex_convex_hull s) (subset_convex_hull _ hx),
  refine ⟨subset_convex_hull _ hx, _⟩,
  rintro y y' hy hy' t,
  rw finset.convex_hull_eq at hy hy',
  obtain ⟨w, hw₀, hw₁, hy⟩ := hy,
  obtain ⟨w', hw'₀, hw'₁, hy'⟩ := hy',
  -- rcases hy with ⟨ι, q, w, z, hw₀, hw₁ : q.sum w = 1, hz, _⟩,
  -- rcases hy' with ⟨ι', q', w', z', hw'₀, hw'₁ : q'.sum w' = 1, hz', rfl⟩,
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
      apply t.1 hθ₂ },
    { simp only [one_smul, zero_smul, zero_add, sub_self] at hθ₂,
      apply t.2 hθ₂ } },
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

--Accurate name?
lemma mem_of_extreme_to_convex_hull (hx : x ∈ (convex_hull A : set E).extreme_points) :
  x ∈ A :=
begin
  have hxA : x ∈ convex_hull A := hx.1,
  rw ←convex_remove_iff_extreme_point (convex_convex_hull _) at hx,
  by_contra,
  have : convex_hull A ⊆ convex_hull A \ {x} :=
    convex_hull_min (subset_diff.2 ⟨subset_convex_hull _, disjoint_singleton_right.2 h⟩) hx.2,
  rw [subset_diff, disjoint_singleton_right] at this,
  exact this.2 hxA,
end

lemma inter_frontier_self_inter_convex_hull_extreme :
  is_extreme_set (closure A) (closure A ∩ frontier (convex_hull A)) :=
begin
  refine ⟨inter_subset_left _ _, λ x₁ x₂ hx₁A hx₂A x hxA hx hxx₁ hxx₂, ⟨⟨hx₁A, _⟩, hx₂A, _⟩⟩,
  sorry,
  sorry
end

lemma frontier_extreme_to_closure (hA₁ : convex A) (hA₂ : is_closed A) :
  is_extreme_set A (frontier A) :=
begin
  convert (inter_frontier_self_inter_convex_hull_extreme : is_extreme_set (closure A)
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
    have := (frontier_extreme hA₁).2 y (z n) (interior_subset hy) (hzA n),
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

lemma subset_frontier_of_extreme (hAB : is_extreme_set A B) (hBA : B ⊂ A) :
  B ⊆ frontier A :=
begin
  rintro x hxB,
  obtain ⟨y, hyA, hyB⟩ := nonempty_of_ssubset hBA,
  rw frontier_eq_closure_inter_closure,
  use subset_closure (hBA.1 hxB),
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
    sorry
    --nth_rewrite 0 ←add_zero 1,
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
  exact_mod_cast mem_of_extreme_to_convex_hull hxextreme,
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
