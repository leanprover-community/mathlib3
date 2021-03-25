import tactic
import data.real.basic
import linear_algebra.affine_space.independent
import linear_algebra.std_basis
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.affine_space.combination
import linear_algebra.finite_dimensional
import analysis.convex.topology
import combinatorics.simplicial_complex.dump
-- import data.nat.parity

open_locale classical affine big_operators
open set
variables {m n : ℕ}
local notation `E` := fin m → ℝ

namespace affine

def is_extreme (s : set E) (x : E) : Prop :=
x ∈ s ∧ ∀ (x₁ x₂ ∈ s), x ∈ segment x₁ x₂ → x = x₁ ∨ x = x₂

lemma convex_remove_iff_is_extreme {s : set E} {x : E} (hs : convex s) (hx : x ∈ s) :
  convex (s \ {x}) ↔ is_extreme s x :=
begin
  split,
  { refine λ hsx, ⟨hx, λ y₁ y₂ hy₁ hy₂ hxy, _⟩,
    by_contra,
    push_neg at h,
    rw convex_iff_segment_subset at hsx,
    exact (hsx ⟨hy₁, h.1.symm⟩ ⟨hy₂, h.2.symm⟩ hxy).2 rfl },
  { intro hsx,
    rw convex_iff_segment_subset,
    rintro y₁ y₂ ⟨hy₁, y₁x : _ ≠ _⟩ ⟨hy₂, y₂x : _ ≠ _⟩ z hz,
    refine ⟨hs.segment_subset hy₁ hy₂ hz, λ (t : z = x), _⟩,
    subst t,
    rcases hsx.2 _ _ hy₁ hy₂ hz with (rfl | rfl),
    exacts [y₁x rfl, y₂x rfl] }
end

-- example {a b c d : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 ≤ d) (h : a * b + c * d = 0) :
--   b = 0 ∧ d = 0 :=
-- begin
--   rw add_eq_zero_iff' at h,
--   rw mul_eq_zero at h,
--   rw mul_eq_zero at h,

-- end


lemma is_extreme_convex_hull_of_affine_independent {s : finset E} {x : E} (hx : x ∈ s)
  (hs : affine_independent ℝ (λ p, p : (s : set E) → E)) :
  is_extreme (convex_hull ↑s) x :=
begin
  -- have := convex_independent_of_affine_independent hs _ hx,

  -- rw ←convex_remove_iff_is_extreme (convex_convex_hull s) (subset_convex_hull _ hx),
  refine ⟨subset_convex_hull _ hx, _⟩,
  rintro y y' hy hy' t,
  rw finset.convex_hull_eq at hy hy',
  rcases hy with ⟨w, hw₀, hw₁, hy⟩,
  rcases hy' with ⟨w', hw'₀, hw'₁, hy'⟩,
  -- rcases hy with ⟨ι, q, w, z, hw₀, hw₁ : q.sum w = 1, hz, _⟩,
  -- rcases hy' with ⟨ι', q', w', z', hw'₀, hw'₁ : q'.sum w' = 1, hz', rfl⟩,
  rw segment_eq_image at t,
  rcases t with ⟨θ, hθ₁, hθ₂ : _ + _ = _⟩,
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
          simpa using hy },
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

--Accurate name?
lemma mem_of_is_extreme_to_convex_hull {X : set E} {x : E} (hx : is_extreme (convex_hull X) x) :
  x ∈ X :=
begin
  have : x ∈ convex_hull (X : set E) := hx.1,
  rw ←convex_remove_iff_is_extreme (convex_convex_hull _) this at hx,
  by_contra,
  have : convex_hull X ⊆ convex_hull X \ {x},
  { apply convex_hull_min _ hx,
    rw subset_diff,
    exact ⟨subset_convex_hull _, disjoint_singleton_right.2 h⟩ },
  rw [subset_diff, disjoint_singleton_right] at this,
  apply this.2 ‹x ∈ convex_hull X›,
end

--probably belongs in the mathlib file of convex hulls
lemma subset_of_convex_hull_eq_convex_hull_of_linearly_independent {X Y : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E))
  (h : convex_hull ↑X = convex_hull (Y : set E)) :
  X ⊆ Y :=
begin
  rintro x hx,
  have hxextreme := is_extreme_convex_hull_of_affine_independent hx hX,
  rw h at hxextreme,
  exact mem_of_is_extreme_to_convex_hull hxextreme,
end

--Keep two linearly_independent in the name?
lemma eq_of_convex_hull_eq_convex_hull_of_linearly_independent_of_linearly_independent
  {X Y : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E))
  (hY : affine_independent ℝ (λ p, p : (Y : set E) → E))
  (h : convex_hull (X : set E) = convex_hull (Y : set E)) :
  X = Y :=
finset.subset.antisymm
  (subset_of_convex_hull_eq_convex_hull_of_linearly_independent hX h)
  (subset_of_convex_hull_eq_convex_hull_of_linearly_independent hY h.symm)

end affine
