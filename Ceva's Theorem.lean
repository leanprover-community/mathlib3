import tactic
import geometry.euclidean
import linear_algebra.affine_space.barycentric_coords
import tactic.basic
import analysis.normed_space.add_torsor_bases
import data.equiv.basic
import group_theory.perm.list

-- wait for afinity refactor, for now we'll have to work over the below definitions

variables {V : Type*} [inner_product_space ℝ V] [normed_space ℝ V] [finite_dimensional ℝ V]
include V

open affine finite_dimensional finset equiv

open_locale euclidean_geometry big_operators

theorem lemma1
  (A B C O : V)
  (S : triangle ℝ V)
  {w : fin 3 → ℝ}
  (σ : perm (fin 3))
  (h₀ : S.points = ![A, B, C] ∘ σ)
  (hspan : affine_span ℝ (set.range S.points) = ⊤)
  (hw : w = λ i, barycentric_coord S.independent hspan i O) :
    ∀ X : V, X -ᵥ O = w 0 • (X -ᵥ S.points 0) + w 1 • (X -ᵥ S.points 1) + w 2 • (X -ᵥ S.points 2) :=
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
    simp only [zero_sub, weighted_vsub_of_point_apply,
      fin.sum_univ_succ, fin.sum_univ_zero, zero_add],
    norm_num,
    simp only [smul_sub, h₀],
    norm_num,
    abel
  end

lemma triangle_perm_barycentric_coord (S S₁ : triangle ℝ V) (σ : perm (fin 3)) (O : V)
  (hspan : affine_span ℝ (set.range S.points) = ⊤)
  (hS₁span : affine_span ℝ (set.range S₁.points) = ⊤)
  (h : S₁.points = S.points ∘ σ) (i : fin 3) :
  barycentric_coord S.independent hspan (σ i) O = barycentric_coord S₁.independent hS₁span i O :=
begin
  simp only [barycentric_coord, affine_map.coe_mk, ← subtype.coe_mk i _],
  apply congr_arg (λ (b : ℝ), 1 - b),
  simp_rw [h],
  apply congr_fun,


  sorry -- finish the proof
end

lemma name_later
  ()

-- roadmap to prove the above lemma
--

lemma lemma2
  (A B C D O : V)
  (S : triangle ℝ V)
  (w : fin 3 → ℝ)
  (σ : perm (fin 3))
  (h₀ : S.points = (![A, B, C] ∘ σ))
  (h₁ : collinear ℝ ({S.points 0, S.points 1, D} : set V))
  (h₂ : collinear ℝ ({D, O, S.points 2} : set V))
  (hspan : affine_span ℝ (set.range S.points) = ⊤)
  (hw : w = λ i, barycentric_coord S.independent hspan i O) :
  w 0 • (D -ᵥ S.points 0) + w 1 • (D -ᵥ S.points 1) = (0 : V) :=
begin
  have h := lemma1 A B C O S σ h₀ hspan hw,
  specialize h D,

  have hsub : D -ᵥ O - w 2 • (D -ᵥ S.points 2) = w 0 • (D -ᵥ S.points 0) + w 1 • (D -ᵥ S.points 1),

  apply vadd_right_cancel (w 2 • (D -ᵥ S.points 2)),
  simp only [sub_add_cancel, vadd_eq_add],
  exact h,

  have hO : O ∈ ({D, O, S.points 2} : set V),
  simp only [set.mem_insert_iff, true_or, eq_self_iff_true, or_true],
  rw (collinear_iff_of_mem ℝ hO) at h₂,
  cases h₂ with v₁ hv₁,

  have hD₁ : D ∈ ({S.points 0, S.points 1, D} : set V),
  simp only [set.mem_insert_iff, set.mem_singleton, or_true],
  rw (collinear_iff_of_mem ℝ hD₁) at h₁,
  cases h₁ with v₂ hv₂,

  obtain ⟨r₂, hC₁⟩ := hv₁ (S.points 2) _,
  obtain ⟨r₃, hA₁⟩ := hv₂ (S.points 0) _,
  obtain ⟨r₄, hB₁⟩ := hv₂ (S.points 1) _,
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
    simp only [smul_zero, zero_vadd, h₀, function.comp_app] at hA₁,
    simp only [smul_zero, zero_vadd, h₀, function.comp_app] at hB₁,

    have hindep := simplex.independent S,
    rw h₀ at hindep,
    rw affine_independent at hindep,
    specialize hindep {0, 1} (![1, -1, 0]),
    simp at hindep,
    apply hindep,
    rw weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ _ D,
    simp, -- bad simp, need to fix
    rw [hA₁, hB₁],
    exact sub_self D,
    simp only [nat.one_ne_zero, matrix.head_cons, sum_insert, fin.zero_eq_one_iff,
    add_right_neg, sum_singleton, not_false_iff, bit0_eq_zero, matrix.cons_val_one,
     matrix.cons_val_zero, mem_singleton] },
  { intros a ha,
    simp only [matrix.head_cons, matrix.cons_val_one, matrix.cons_val_zero] at ha,
    subst ha,
    subst hD₁,
    have hindep := simplex.independent S,
    rw affine_independent_iff_not_collinear at hindep,
    apply hindep,
    have hA₂ : S.points 0 ∈ set.range S.points := by use 0,
    rw (collinear_iff_of_mem ℝ hA₂),
    use v₂,
    intros p hp,
    rw set.range_comp at hp,
    simp only [true_and, set.mem_range, set.mem_image, exists_apply_eq_apply] at hp,
    cases hp with n hpn,
    fin_cases n,
    { use 0,
      rw ← hpn,
      simp, },
    { use (r₄ - r₃),
      rw [← hpn, hB₁, hA₁],
      simp only [sub_smul, vadd_vadd, ← add_assoc, ← smul_assoc, smul_eq_mul, sub_add_cancel], },
    { use (r₂ • a - r₁ • a - r₃),
      rw [← hpn, hC₁, hA₁],
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
  simp only [neg_mul_eq_neg_mul_symm, matrix.head_cons, smul_eq_mul, ne.def,
    matrix.cons_val_one, matrix.cons_val_zero] at h₅,
  exfalso,
  apply h₅,
  rw h₂,
  rw smul_eq_mul,
  rw neg_mul_eq_neg_mul,

  exact h₃,
  simp only [set.mem_insert_iff, true_or, eq_self_iff_true],
  simp only [set.mem_insert_iff, true_or, eq_self_iff_true, or_true],
  simp only [set.mem_insert_iff, true_or, eq_self_iff_true],
  simp only [set.mem_insert_iff, set.mem_singleton, or_true],
end

theorem Ceva_Theorem
  (A B C D E F O : V)
  (S : triangle ℝ V)
  (h₀ : finrank ℝ V = 2)
  (h₁ : S.points = ![A, B, C])
  (h₂ : collinear ℝ ({A, B, D} : set V))
  (h₃ : collinear ℝ ({B, C, E} : set V))
  (h₄ : collinear ℝ ({C, A, F} : set V))
  (h₅ : collinear ℝ ({D, O, C} : set V))
  (h₆ : collinear ℝ ({E, O, A} : set V))
  (h₇ : collinear ℝ ({F, O, B} : set V))
  (h₈ : O ∈ interior (convex_hull ℝ (set.range S.points))) :
  dist A D * dist B E * dist C F  = dist D B * dist E C * dist F A :=
begin
  have hspan : affine_span ℝ (set.range S.points) = ⊤,
  rw affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one S.independent,
  { rw fintype.card_fin,
    rw h₀ },

  set σ₁ : perm (fin 3) := equiv.refl (fin 3) with hσ₁,
  set σ₂ : perm (fin 3) := list.form_perm [0, 1, 2] with hσ₂,
  set σ₃ : perm (fin 3) := equiv.trans σ₂ σ₂ with hσ₃,

  have hs := S.independent,

  let S₁ : triangle ℝ V := ⟨![A, B, C] ∘ σ₁, by simpa [affine_independent_equiv, ← h₁]⟩,
  have hS₁ : S₁.points = ![A, B, C] ∘ σ₁ := by refl,
  have hS₁span : affine_span ℝ (set.range S₁.points) = ⊤,
  rw affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one S₁.independent,
  { rw fintype.card_fin,
    rw h₀ },
  replace h₂ : collinear ℝ ({S₁.points 0, S₁.points 1, D} : set V) := by convert h₂,
  replace h₅ : collinear ℝ ({D, O, S₁.points 2} : set V) := by convert h₅,

  let S₂ : triangle ℝ V := ⟨![A, B, C] ∘ σ₂, by simpa [affine_independent_equiv, ← h₁]⟩,
  have hS₂ : S₂.points = ![A, B, C] ∘ σ₂ := by refl,
  have hS₂span : affine_span ℝ (set.range S₂.points) = ⊤,
  rw affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one S₂.independent,
  { rw fintype.card_fin,
    rw h₀ },
  replace h₃ : collinear ℝ ({S₂.points 0, S₂.points 1, E} : set V) := by convert h₃,
  replace h₆ : collinear ℝ ({E, O, S₂.points 2} : set V) := by convert h₆,

  let S₃ : triangle ℝ V := ⟨![A, B, C] ∘ σ₃, by simp only [affine_independent_equiv, ← h₁,
    S.independent]⟩,
  have hS₃ : S₃.points = ![A, B, C] ∘ σ₃ := by refl,
  have hS₃span : affine_span ℝ (set.range S₃.points) = ⊤,
  rw affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one S₃.independent,
  { rw fintype.card_fin,
    rw h₀ },
  replace h₄ : collinear ℝ ({S₃.points 0, S₃.points 1, F} : set V) := by convert h₄,
  replace h₇ : collinear ℝ ({F, O, S₃.points 2} : set V) := by convert h₇,

  set w : fin 3 → ℝ := λ i, barycentric_coord S.independent hspan i O with hw,

  have hwpos : 0 < w 0 ∧ 0 < w 1 ∧ 0 < w 2,
  rw interior_convex_hull_aff_basis S.independent hspan at h₈,
  rw set.mem_set_of_eq at h₈,
  refine ⟨h₈ 0, h₈ 1, h₈ 2⟩,

  have hwnezero : w 0 * w 1 * w 2 ≠ 0,
  apply ne_of_gt,
  apply mul_pos (mul_pos hwpos.1 hwpos.2.1) hwpos.2.2,

  set w₁ : fin 3 → ℝ := λ i, barycentric_coord S₁.independent hS₁span i O with hw₁,
  set w₂ : fin 3 → ℝ := λ i, barycentric_coord S₂.independent hS₂span i O with hw₂,
  set w₃ : fin 3 → ℝ := λ i, barycentric_coord S₃.independent hS₃span i O with hw₃,

  -- apply lemmas above with appropriate permutations and shifts

  have hADB := lemma2 A B C D O S₁ w₁ σ₁ hS₁ h₂ h₅ hS₁span hw₁,
  rw add_eq_zero_iff_eq_neg at hADB,
  rw eq_neg_iff_eq_neg at hADB,

  have hadb : w₁ 0 * dist (S₁.points 0) D = w₁ 1 * dist D (S₁.points 1),
  { rw dist_eq_norm_vsub V,
    rw dist_eq_norm_vsub V,
    rw ← norm_smul_of_nonneg,
    rw ← norm_smul_of_nonneg,
    rw hADB,
    rw ← smul_neg,
    rw neg_vsub_eq_vsub_rev,
    sorry,
    sorry, },

  have hBEC := lemma2 A B C E O S₂ w₂ σ₂ hS₂ h₃ h₆ hS₂span hw₂,
  rw add_eq_zero_iff_eq_neg at hBEC,
  rw eq_neg_iff_eq_neg at hBEC,

  have hbec : w₂ 0 * dist (S₂.points 0) E = w₂ 1 * dist E (S₂.points 1),
  { rw dist_eq_norm_vsub V,
    rw dist_eq_norm_vsub V,
    rw ← norm_smul_of_nonneg,
    rw ← norm_smul_of_nonneg,
    rw hBEC,
    rw ← smul_neg,
    rw neg_vsub_eq_vsub_rev,
    sorry,
    sorry },

  have hCFA := lemma2 A B C F O S₃ w₃ σ₃ hS₃ h₄ h₇ hS₃span hw₃,
  rw add_eq_zero_iff_eq_neg at hCFA,
  rw eq_neg_iff_eq_neg at hCFA,

  have hcfa : w₃ 0 * dist (S₃.points 0) F = w₃ 1 * dist F (S₃.points 1),
  { rw dist_eq_norm_vsub V,
    rw dist_eq_norm_vsub V,
    rw ← norm_smul_of_nonneg,
    rw ← norm_smul_of_nonneg,
    rw hCFA,
    rw ← smul_neg,
    rw neg_vsub_eq_vsub_rev,
    sorry,
    sorry },

  have : w₁ 0 = w 0,
  { simp only [hw₁, hw, barycentric_coord],
    simp_rw h₁,
    sorry },
  have : w₁ 1 = w 1,
  { simp only [hw₁, hw, barycentric_coord],
    simp_rw h₁,
    sorry },
  have : w₂ 0 = w 1,
  { simp only [hw₂, hw, barycentric_coord],
    simp_rw h₁,
    sorry },
  have : w₂ 1 = w 2,
  { simp only [hw₂, hw, barycentric_coord],
    simp_rw h₁,
    sorry },
  have : w₃ 0 = w 2,
  { simp only [hw₃, hw, barycentric_coord],
    simp_rw h₁,
    sorry },
  sorry,
  -- have : w₃ 1 = w 0,
  -- { simp only [hw₃, hw, barycentric_coord],
    -- simp_rw h₁,
    -- sorry },

  /- have h := congr_arg2 (λ a b, a * b) (congr_arg2 (λ a b, a * b) hadb hbec) hcfa,
  dsimp at h,
  replace h : (w 0 * w 1 * w 2) * (dist A D * dist B E * dist C F) =
    (w 0 * w 1 * w 2) * (dist D B * dist E C * dist F A) := by linarith,
  rw ← mul_right_inj' hwnezero,
  exact h, -/
end
