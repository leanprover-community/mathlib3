import tactic
import geometry.euclidean
import linear_algebra.affine_space.barycentric_coords
import tactic.basic

variables {V : Type*} {P : Type*} [metric_space P] [inner_product_space ℝ V]
 [normed_add_torsor V P] [finite_dimensional ℝ V]
include V

open affine finite_dimensional finset

open_locale euclidean_geometry big_operators

theorem lemma1
  (A B C O : P)
  (S : triangle ℝ P)
  {w : fin 3 → ℝ}
  (h₀ : S.points = ![A, B, C])
  (hspan : affine_span ℝ (set.range S.points) = ⊤)
  (hw : w = λ i, barycentric_coord S.independent hspan i O) :
    ∀ X : P, X -ᵥ O = w 0 • (X -ᵥ A) + w 1 • (X -ᵥ B) + w 2 • (X -ᵥ C) :=
  begin
    have hw : ∑ (i : fin 3), w i = 1,
    rw hw,
    exact sum_barycentric_coord_apply_eq_one S.independent hspan O,

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
    simp only [smul_neg, h₀],
    norm_num,
    abel
  end


lemma lemma2
  (A B C D O : P)
  (S : triangle ℝ P)
  (w : fin 3 → ℝ)
  (h₀ : S.points = ![A, B, C])
  (h₁ : collinear ℝ ({A, B, D} : set P))
  (h₂ : collinear ℝ ({D, O, C} : set P))
  (hspan : affine_span ℝ (set.range S.points) = ⊤)
  (hw : w = λ i, barycentric_coord S.independent hspan i O) :
  w 0 • (D -ᵥ A) + w 1 • (D -ᵥ B) = (0 : V) :=
begin
  have h := lemma1 A B C O S h₀ hspan hw,
  specialize h D,

  have hsub : D -ᵥ O - w 2 • (D -ᵥ C) = w 0 • (D -ᵥ A) + w 1 • (D -ᵥ B),

  apply vadd_right_cancel (w 2 • (D -ᵥ C)),
  simp only [sub_add_cancel, vadd_eq_add],
  exact h,

  have hO : O ∈ ({D, O, C} : set P),
  simp only [set.mem_insert_iff, true_or, eq_self_iff_true, or_true],
  rw (collinear_iff_of_mem ℝ hO) at h₂,
  cases h₂ with v₁ hv₁,

  have hD₁ : D ∈ ({A, B, D} : set P),
  simp only [set.mem_insert_iff, set.mem_singleton, or_true],
  rw (collinear_iff_of_mem ℝ hD₁) at h₁,
  cases h₁ with v₂ hv₂,

  obtain ⟨r₂, hC₁⟩ := hv₁ C _,
  obtain ⟨r₃, hA₁⟩ := hv₂ A _,
  obtain ⟨r₄, hB₁⟩ := hv₂ B _,
  obtain ⟨r₁, hD₁⟩ := hv₁ D _,

  rw [hC₁, hA₁, hB₁, hD₁] at hsub,
  simp only [vadd_vsub_vadd_cancel_right, vadd_vsub, vsub_vadd_eq_vsub_sub] at hsub,
  simp only [zero_sub, smul_neg, sub_self] at hsub,

  rw [hB₁, hA₁, hD₁],
  simp only [vadd_vsub_vadd_cancel_right, vadd_vsub, vsub_vadd_eq_vsub_sub],
  simp only [zero_sub, smul_neg, sub_self],

  have : linear_independent ℝ ![v₁, v₂],
  rw linear_independent_fin2,
  split,
  { simp only [matrix.head_cons, ne.def, matrix.cons_val_one],
    intro hv₂,
    subst hv₂,
    simp only [smul_zero, zero_vadd] at hA₁,
    simp only [smul_zero, zero_vadd] at hB₁,
    rw [hA₁, hB₁] at h₀,
    have hindep := simplex.independent S,
    rw h₀ at hindep,
    rw affine_independent at hindep,
    specialize hindep {0, 1} (![1, -1, 0]),
    simp at hindep,
    apply hindep,
    rw weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ _ D,
    simp,
    simp },
  { intros a ha,
    simp only [matrix.head_cons, matrix.cons_val_one, matrix.cons_val_zero] at ha,
    subst ha,
    subst hD₁,
    have hindep := simplex.independent S,
    rw affine_independent_iff_not_collinear at hindep,
    rw h₀ at hindep,
    simp only [insert_emptyc_eq, matrix.range_cons, set.singleton_union, matrix.range_empty, set.union_singleton] at hindep,
    apply hindep,
    have hA₂ : A ∈ ({A, C, B} : set P),
    simp only [set.mem_insert_iff, true_or, eq_self_iff_true],
    rw (collinear_iff_of_mem ℝ hA₂),
    use v₂,
    intros p hp,
    simp only [set.mem_insert_iff, set.mem_singleton_iff] at hp,
    rcases hp with (⟨hpA, refl⟩ | ⟨hpB, refl⟩ | ⟨hpC, refl⟩),
    { use 0,
      simp, },
    { use (r₂ • a - r₁ • a - r₃),
      subst hC₁,
      subst hA₁,
      simp only [sub_smul, vadd_vadd, ← add_assoc, ← smul_assoc, smul_eq_mul, sub_add_cancel] },
    { use (r₄ - r₃),
      subst hB₁,
      subst hA₁,
      simp only [sub_smul, vadd_vadd, ← add_assoc, ← smul_assoc, smul_eq_mul, sub_add_cancel] }},
  have hv₁ : (r₁ + w 2 • r₂ - w 2 • r₁) • v₁ = r₁ • v₁ - w 2 • (r₁ • v₁ - r₂ • v₁),
  rw ← sub_smul,
  rw ← smul_assoc,
  simp only [smul_eq_mul, mul_sub, sub_smul, add_smul],
  rw sub_sub_assoc_swap,

  have hv₂ : (- w 0 • r₃ - w 1 • r₄) • v₂ = -(w 0 • r₃ • v₂) + -(w 1 • r₄ • v₂),
  simp only [sub_smul, ← smul_assoc, smul_eq_mul, neg_smul, ← sub_eq_add_neg],

  have h₂ : (r₁ + w 2 • r₂ - w 2 • r₁) • v₁ = (- w 0 • r₃ - w 1 • r₄) • v₂,
  rw hv₁,
  rw hv₂,
  exact hsub,

  simp only [smul_eq_mul] at h₂,
  rw [← sub_eq_add_neg, ← neg_smul, ← smul_assoc, ← smul_assoc, ← sub_smul],

  by_cases h₃ : (r₁ + w 2 * r₂ - w 2 * r₁) = 0,
  simp only [h₃, zero_smul] at h₂,
  simp only [smul_eq_mul, ← h₂],

  rw ← eq_inv_smul_iff₀ at h₂,
  rw ← smul_assoc at h₂,

  rw linear_independent_fin2 at this,
  cases this with h₄ h₅,
  specialize h₅ ((r₁ + w 2 * r₂ - w 2 * r₁)⁻¹ • (-w 0 * r₃ - w 1 * r₄)),
  simp only [neg_mul_eq_neg_mul_symm, matrix.head_cons, smul_eq_mul, ne.def, matrix.cons_val_one, matrix.cons_val_zero] at h₅,
  exfalso,
  apply h₅,
  rw h₂,
  rw smul_eq_mul,
  rw neg_mul_eq_neg_mul,

  exact h₃,
  simp,
  simp,
  simp,
  simp
end

theorem Ceva_Theorem
  (A B C D E F O : P)
  (S : triangle ℝ P)
  (h₀ : finrank ℝ V = 2)
  (h₁ : S.points = ![A, B, C])
  (h₂ : collinear ℝ ({A, B, D} : set P))
  (h₃ : collinear ℝ ({B, C, E} : set P))
  (h₄ : collinear ℝ ({C, A, F} : set P))
  (h₅ : collinear ℝ ({D, O, C} : set P))
  (h₆ : collinear ℝ ({E, O, A} : set P))
  (h₇ : collinear ℝ ({F, O, B} : set P))
  (h₈ : O ∉ ({A, B, C} : set P)) :
  dist A D * dist B E * dist C F= dist D B * dist E C * dist F A :=
begin
  have hspan : affine_span ℝ (set.range S.points) = ⊤,
  rw affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one S.independent,
  { rw fintype.card_fin,
    rw h₀ },

  set w : fin 3 → ℝ := λ i, barycentric_coord S.independent hspan i O with hw,
  have hwzero : w 0 ≠ 0 ∧ w 1 ≠ 0 ∧ w 2 ≠ 0,
  contrapose h₈,
  simp only [set.mem_insert_iff, set.mem_singleton_iff, not_not],
  simp only [not_and, not_not, ne.def] at h₈,
  by_cases hw0 : w 0 = 0,
  left,
  rw hw at hw0,
  dsimp at hw0,
  rw barycentric_coord at hw0,
  simp only [basis.coord_apply, fintype.sum_apply, basis.coe_sum_coords_of_fintype, affine_map.coe_mk] at hw0,
  sorry,
  sorry,


  have hADB := lemma2 A B C D O S w h₁ h₂ h₅ hspan hw,
  rw add_eq_zero_iff_eq_neg at hADB,
  rw ← eq_inv_smul_iff₀ at hADB,
  simp only [smul_neg] at hADB,
  rw ← smul_assoc at hADB,
  rw smul_eq_mul at hADB,
  rw inv_eq_one_div at hADB,
  rw mul_comm at hADB,
  rw mul_one_div at hADB,

  have hadb : dist A D = w 1 / w 0 * dist D B,
  rw dist_eq_norm_vsub V,
  swap,
  apply_instance,
  rw dist_eq_norm_vsub V,
  swap,
  apply_instance,
  rw ← norm_smul_of_nonneg,
  rw eq_neg_iff_eq_neg at hADB,
  rw neg_vsub_eq_vsub_rev at hADB,
  rw ← hADB,

  sorry,
  sorry,

  have hbec : dist B E = w 2 / w 1 * dist E C,
  sorry,

  have hcfa : dist C F = w 0 / w 2 * dist F A,
  sorry,

  have hdist : 0 ≠ dist D B ∧ 0 ≠ dist E C ∧ 0 ≠ dist F A,
  sorry,

  rw [hadb, hbec, hcfa],
  field_simp,
  rw div_eq_one_iff_eq,
  ring,
  sorry,
  sorry,
end

lemma test
  (a b : ℝ)
  (A B D : P)
  (h : (a / b) • (D -ᵥ B) = A -ᵥ D) :
  ∥A -ᵥ D∥ = ∥(a / b) • (D -ᵥ B)∥ :=
begin
  rw h,
end
