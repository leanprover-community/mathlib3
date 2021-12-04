import tactic
import geometry.euclidean
import linear_algebra.affine_space.basis
import tactic.basic
import analysis.normed_space.add_torsor_bases
import data.equiv.basic
import group_theory.perm.list

-- wait for afinity refactor, for now we'll have to work over the below definitions

variables {V : Type*} [inner_product_space ℝ V] [normed_space ℝ V] [finite_dimensional ℝ V]
include V

open affine finite_dimensional finset equiv affine_basis fintype basis

open_locale euclidean_geometry big_operators

theorem lemma1
  (O : V) (n : ℕ) (S : affine_basis (fin n) ℝ V) :
    ∀ X : V, X -ᵥ O = ∑ (i : fin n), S.coord i O • (X -ᵥ S.points i) :=
  begin
    set w : fin n → ℝ := λ i, S.coord i O with hw,
    have hs := sum_coord_apply_eq_one S O,
    intro X,
    have h₄ := weighted_vsub_of_point_vadd_eq_of_sum_eq_one univ w S.points hs,
    specialize h₄ X O,
    rw vadd_eq_vadd_iff_sub_eq_vsub at h₄,
    rw ← h₄,

    have h₅ : (univ.weighted_vsub_of_point S.points O) w = (0 : V),
    suffices : univ.affine_combination S.points w = O,
    rw affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one univ w S.points hs O at this,
    replace this := this.symm,
    rw eq_vadd_iff_vsub_eq at this,
    rw ← this,
    exact vsub_self O,

    convert affine_combination_coord_eq_self S O,

    rw h₅,
    simp only [vsub_eq_sub, zero_sub, weighted_vsub_of_point_apply, neg_eq_iff_add_eq_zero],
    simp only [← sum_add_distrib, smul_sub, smul_sub],
    norm_num,
  end

lemma equiv.sum_coords_congr {ι ι' : Type*} [fintype ι] [fintype ι'] (e : ι ≃ ι') (b : basis ι ℝ V)
  (c : basis ι' ℝ V) (h : c = b.reindex e) : b.sum_coords = c.sum_coords :=
begin
  ext x,
  simp only [coe_sum_coords_of_fintype, h, reindex_repr, reindex, basis.coord_apply,
  linear_equiv.trans_apply, finsupp.dom_congr_apply, fintype.sum_apply,
  finsupp.equiv_map_domain_apply, finsupp.dom_lcongr_apply],
  rw sum_equiv e,
  intro i,
  rw symm_apply_apply,
end

lemma triangle_perm_barycentric_coord {ι : Type*} [fintype ι] (S T : affine_basis ι ℝ V) (O : V)
  (σ : perm ι) (h : T.points = S.points ∘ σ) (i : ι) : S.coord (σ i) O = T.coord i O :=
begin
  simp only [affine_basis.coord, affine_map.coe_mk, ← subtype.coe_mk i _],
  apply congr_arg (λ (b : ℝ), 1 - b),
  simp_rw [h],
  apply congr_fun,
  set f : {j // j ≠ σ i} → {j // j ≠ i} :=
    begin
      intro j,
      cases j with j hj,
      use σ.symm j,
      rw ne.def,
      rw (symm_apply_eq σ),
      exact hj,
    end with hf,
  set g : {j // j ≠ i} → {j // j ≠ σ i} :=
    begin
      intro j,
      cases j with j hj,
      use σ j,
      rw ne.def at hj,
      by_contra,
      apply hj,
      apply (equiv.injective σ) h,
    end with hg,
  have e : {j // j ≠ σ i} ≃ {j // j ≠ i},
  {
    use f,
    use g,
    { intro j,
      rw [hf, hg],
      tidy },
    { intro j,
      rw [hg, hf],
      tidy }},
  have : fintype {j // j ≠ i} := by subtype.fintype _,
  rw equiv.sum_coords_congr e (S.basis_of (σ i)) (T.basis_of i) _,
  ext v,
  sorry -- finish the prove
end

-- lemma to_prove {ι : Type*} (S T : ι → V) (σ : perm ι) (S_ind : affine_independent ℝ S)
  -- (S_tot : affine_span ℝ (set.range S) = ⊤) (T_ind : affine_independent ℝ T)
  -- (T_tot : affine_span ℝ (set.range T) = ⊤) (h : S = T ∘ σ) (i : ι) :
  -- ((basis_of_aff_ind_span_eq_top S_ind S_tot i).sum_coords) =
  -- ((basis_of_aff_ind_span_eq_top T_ind T_tot (σ i)).sum_coords) := sorry

lemma lemma2 {O D v₁ v₂ : V} (S : affine_basis (fin 3) ℝ V) {r₁ r₂ r₃ r₄ : ℝ}
  (hA₁ : S.points 0 = r₃ • v₂ +ᵥ D) (hB₁ : S.points 1 = r₄ • v₂ +ᵥ D)
  (hC₁ : S.points 2 = r₂ • v₁ +ᵥ O) (hD₁ : D = r₁ • v₁ +ᵥ O) : linear_independent ℝ ![v₁, v₂] :=
begin
  rw linear_independent_fin2,
  split,
  { simp only [matrix.head_cons, ne.def, matrix.cons_val_one],
    intro hv₂,
    subst hv₂,
    simp only [smul_zero, zero_vadd, function.comp_app] at hA₁,
    simp only [smul_zero, zero_vadd, function.comp_app] at hB₁,
    have hindep := S.ind,
    rw affine_independent at hindep,
    specialize hindep {0, 1} (![1, -1, 0]),
    simp at hindep,
    apply hindep,
    rw weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ _ D,
    simp,
    rw [hA₁, hB₁],
    exact sub_self D,
    simp only [nat.one_ne_zero, matrix.head_cons, sum_insert, fin.zero_eq_one_iff,
    add_right_neg, sum_singleton, not_false_iff, bit0_eq_zero, matrix.cons_val_one,
     matrix.cons_val_zero, mem_singleton] },
  { intros a ha,
    simp only [matrix.head_cons, matrix.cons_val_one, matrix.cons_val_zero] at ha,
    subst ha,
    subst hD₁,
    have hindep := S.ind,
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
      simp only [sub_smul, vadd_vadd, ← add_assoc, ← smul_assoc, smul_eq_mul, sub_add_cancel] },
    { use (r₂ • a - r₁ • a - r₃),
      rw [← hpn, hC₁, hA₁],
      simp only [sub_smul, vadd_vadd, ← add_assoc, ← smul_assoc, smul_eq_mul, sub_add_cancel] }}
end


lemma lemma3
  (O D: V)
  (S : affine_basis (fin 3) ℝ V)
  (h₁ : collinear ℝ ({S.points 0, S.points 1, D} : set V))
  (h₂ : collinear ℝ ({D, O, S.points 2} : set V)) :
  S.coord 0 O • (D -ᵥ S.points 0) + S.coord 1 O • (D -ᵥ S.points 1) = (0 : V) :=
begin
  have h := lemma1 O 3 S,
  specialize h D,

  have hsub : D -ᵥ O - S.coord 2 O • (D -ᵥ S.points 2) = S.coord 0 O • (D -ᵥ S.points 0) +
  S.coord 1 O • (D -ᵥ S.points 1),
  { apply vadd_right_cancel (S.coord 2 O • (D -ᵥ S.points 2)),
    simp only [vsub_eq_sub, sub_add_cancel, vadd_eq_add],
    simp only [fin.sum_univ_succ, fin.sum_univ_zero, add_zero] at h,
    convert h using 1,
    norm_num,
    abel },

  have hO : O ∈ ({D, O, S.points 2} : set V),
  { simp only [set.mem_insert_iff, true_or, eq_self_iff_true, or_true] },

  rw (collinear_iff_of_mem ℝ hO) at h₂,
  cases h₂ with v₁ hv₁,

  have hD₁ : D ∈ ({S.points 0, S.points 1, D} : set V),
  { simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
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

  have hlinind := lemma2 S hA₁ hB₁ hC₁ hD₁,
  have hv₁ : (r₁ + S.coord 2 O • r₂ - S.coord 2 O • r₁) • v₁ = r₁ • v₁ -
    S.coord 2 O • (r₁ • v₁ - r₂ • v₁),
  rw ← sub_smul,
  rw ← smul_assoc,
  simp only [smul_eq_mul, mul_sub, sub_smul, add_smul],
  rw sub_sub_assoc_swap,

  have hv₂ : (- S.coord 0 O • r₃ - S.coord 1 O • r₄) • v₂ = -(S.coord 0 O • r₃ • v₂) +
    -(S.coord 1 O • r₄ • v₂),
  simp only [sub_smul, ← smul_assoc, smul_eq_mul, neg_smul, ← sub_eq_add_neg],

  have h₂ : (r₁ + S.coord 2 O • r₂ - S.coord 2 O • r₁) • v₁ = (- S.coord 0 O • r₃ -
    S.coord 1 O • r₄) • v₂,
  rw hv₁,
  rw hv₂,
  exact hsub,

  simp only [smul_eq_mul] at h₂,
  rw [← sub_eq_add_neg, ← neg_smul, ← smul_assoc, ← smul_assoc, ← sub_smul],

  by_cases h₃ : (r₁ + S.coord 2 O * r₂ - S.coord 2 O * r₁) = 0,
  simp only [h₃, zero_smul] at h₂,
  simp only [smul_eq_mul, ← h₂],

  rw ← eq_inv_smul_iff₀ at h₂,
  rw ← smul_assoc at h₂,

  rw linear_independent_fin2 at hlinind,
  cases hlinind with h₄ h₅,
  specialize h₅
    ((r₁ + S.coord 2 O * r₂ - S.coord 2 O * r₁)⁻¹ • (-S.coord 0 O * r₃ - S.coord 1 O * r₄)),
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

  set T : affine_basis (fin 3) ℝ V := ⟨S.points, S.independent, hspan⟩ with hT,

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
  set T₁ : affine_basis (fin 3) ℝ V := ⟨S₁.points, S₁.independent, hS₁span⟩ with hT₁,
  replace h₂ : collinear ℝ ({S₁.points 0, S₁.points 1, D} : set V) := by convert h₂,
  replace h₅ : collinear ℝ ({D, O, S₁.points 2} : set V) := by convert h₅,

  let S₂ : triangle ℝ V := ⟨![A, B, C] ∘ σ₂, by simpa [affine_independent_equiv, ← h₁]⟩,
  have hS₂ : S₂.points = ![A, B, C] ∘ σ₂ := by refl,
  have hS₂span : affine_span ℝ (set.range S₂.points) = ⊤,
  rw affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one S₂.independent,
  { rw fintype.card_fin,
    rw h₀ },
  set T₂ : affine_basis (fin 3) ℝ V := ⟨S₂.points, S₂.independent, hS₂span⟩ with hT₂,
  replace h₃ : collinear ℝ ({S₂.points 0, S₂.points 1, E} : set V) := by convert h₃,
  replace h₆ : collinear ℝ ({E, O, S₂.points 2} : set V) := by convert h₆,

  let S₃ : triangle ℝ V := ⟨![A, B, C] ∘ σ₃, by simp only [affine_independent_equiv, ← h₁,
    S.independent]⟩,
  have hS₃ : S₃.points = ![A, B, C] ∘ σ₃ := by refl,
  have hS₃span : affine_span ℝ (set.range S₃.points) = ⊤,
  rw affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one S₃.independent,
  { rw fintype.card_fin,
    rw h₀ },
  set T₃ : affine_basis (fin 3) ℝ V := ⟨S₃.points, S₃.independent, hS₃span⟩ with hT₃,
  replace h₄ : collinear ℝ ({S₃.points 0, S₃.points 1, F} : set V) := by convert h₄,
  replace h₇ : collinear ℝ ({F, O, S₃.points 2} : set V) := by convert h₇,

  have hwpos : 0 < T.coord 0 O ∧ 0 < T.coord 1 O ∧ 0 < T.coord 2 O,
  rw interior_convex_hull_aff_basis T at h₈,
  rw set.mem_set_of_eq at h₈,
  refine ⟨h₈ 0, h₈ 1, h₈ 2⟩,

  have hwnezero : T.coord 0 O * T.coord 1 O * T.coord 2 O ≠ 0,
  apply ne_of_gt,
  apply mul_pos (mul_pos hwpos.1 hwpos.2.1) hwpos.2.2,

  -- apply lemmas above with appropriate permutations and shifts

  have hADB := lemma3 O D T₁ h₂ h₅,
  rw add_eq_zero_iff_eq_neg at hADB,
  rw eq_neg_iff_eq_neg at hADB,

  have hadb : T₁.coord 0 O * dist (S₁.points 0) D = T₁.coord 1 O * dist D (S₁.points 1),
  { rw dist_eq_norm_vsub V,
    rw dist_eq_norm_vsub V,
    rw ← norm_smul_of_nonneg,
    rw ← norm_smul_of_nonneg,
    rw hADB,
    rw ← smul_neg,
    rw neg_vsub_eq_vsub_rev,
    sorry,
    sorry, },

  have hBEC := lemma3 O E T₂ h₃ h₆,
  rw add_eq_zero_iff_eq_neg at hBEC,
  rw eq_neg_iff_eq_neg at hBEC,

  have hbec : T₂.coord 0  O * dist (S₂.points 0) E = T₂.coord 1 O * dist E (S₂.points 1),
  { rw dist_eq_norm_vsub V,
    rw dist_eq_norm_vsub V,
    rw ← norm_smul_of_nonneg,
    rw ← norm_smul_of_nonneg,
    rw hBEC,
    rw ← smul_neg,
    rw neg_vsub_eq_vsub_rev,
    sorry,
    sorry },

  have hCFA := lemma3 O F T₃ h₄ h₇,
  rw add_eq_zero_iff_eq_neg at hCFA,
  rw eq_neg_iff_eq_neg at hCFA,

  have hcfa : T₃.coord 0 O * dist (S₃.points 0) F = T₃.coord 1 O * dist F (S₃.points 1),
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
