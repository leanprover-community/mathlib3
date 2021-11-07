import tactic
import geometry.euclidean
import linear_algebra.affine_space.barycentric_coords

variables {V : Type*} {P : Type*} [metric_space P] [inner_product_space ℝ V]
[module ℝ V] [normed_add_torsor V P] [finite_dimensional ℝ V]
include V

open affine finite_dimensional finset

open_locale euclidean_geometry big_operators

theorem lemma1
  (A B C O : P)
  (S : triangle ℝ P)
  (h₀ : finrank ℝ V = 2)
  (h₁ : S.points = ![A, B, C]) :
  ∃ (w₁ w₂ w₃ : ℝ), w₁ + w₂ + w₃ = 1 ∧
    ∀ X : P, X -ᵥ O = w₁ • (X -ᵥ A) + w₂ • (X -ᵥ B) + w₃ • (X -ᵥ C) :=
  begin
    have hspan : affine_span ℝ (set.range S.points) = ⊤,
    rw affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one,
    norm_num, rw h₀,
    exact S.independent,

    let h := barycentric_coord S.independent hspan,
    let w : fin 3 → ℝ := λ i, h i O,

    have hw : ∑ (i : fin 3), w i = 1,
    exact sum_barycentric_coord_apply_eq_one S.independent hspan O,

    refine ⟨w 0, w 1, w 2, _⟩,
    split,
    rw ← hw,
    simp only [fin.sum_univ_succ, finset.sum_empty, zero_add, univ_is_empty],
    norm_num,
    ring,

    intros X,
    have h₄ := weighted_vsub_of_point_vadd_eq_of_sum_eq_one univ w S.points hw,
    specialize h₄ X O,
    rw vadd_eq_vadd_iff_sub_eq_vsub at h₄,
    rw ← h₄,

    have h₅ : (univ.weighted_vsub_of_point S.points O) w = (0 : V),
    suffices : univ.affine_combination S.points w = O,
    rw affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one univ w S.points hw O at this,
    replace this := this.symm,
    rw eq_vadd_iff_vsub_eq at this,
    rw ← this,
    exact vsub_self O,

    convert affine_combination_barycentric_coord_eq_self S.independent hspan O,

    rw h₅,
    simp only [zero_sub, weighted_vsub_of_point_apply, fin.sum_univ_succ, fin.sum_univ_zero, zero_add],
    norm_num,
    rw ← neg_vsub_eq_vsub_rev X (S.points 0),
    rw ← neg_vsub_eq_vsub_rev X (S.points 1),
    rw ← neg_vsub_eq_vsub_rev X (S.points 2),
    simp only [smul_neg, h₁],
    norm_num,
    abel,
  end

-- todo
-- do the lemma for arbitrary point on line AB and try to unify vectors with distances somehow. 
