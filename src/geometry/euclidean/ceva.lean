/-
Copyright (c) 2021 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import tactic.linarith
import tactic.fin_cases
import tactic.norm_num
import geometry.euclidean
import linear_algebra.affine_space.basis
import tactic.basic
import analysis.normed_space.add_torsor_bases
import data.equiv.basic
import group_theory.perm.list

/-!
# Ceva's Theorem

This file (although could be merged to another file later) proves Ceva's Theorem in Euclidean
Geometry following the barycentric coordinate proof. For a reference,
see https://en.wikipedia.org/wiki/Ceva%27s_theorem.

Because of the currently generality that `interior_convex_hull_aff_basis` is stated in, we prove
Ceva's theorem in it's current form. This will need to be upgraded to the usual setting of
Euclidean Geometry results after the affinity refactor.

**This is also a Problem 61 on Freek's list**
-/

variables {V : Type*} [inner_product_space ℝ V] [normed_space ℝ V]
include V

open affine finite_dimensional finset equiv affine_basis fintype basis

open_locale euclidean_geometry big_operators

lemma affine_basis.vsub_eq_coord_smul_sum (O : V) {ι : Type*} [fintype ι]
  (S : affine_basis ι ℝ V) : ∀ X : V, X -ᵥ O = ∑ (i : ι), S.coord i O • (X -ᵥ S.points i) :=
begin
  set w : ι → ℝ := λ i, S.coord i O with hw,
  have hs := sum_coord_apply_eq_one S O,
  intro X,
  have h₄ := weighted_vsub_of_point_vadd_eq_of_sum_eq_one univ w S.points hs X O,
  rw vadd_eq_vadd_iff_sub_eq_vsub at h₄,
  rw ← h₄,
  have h₅ : (univ.weighted_vsub_of_point S.points O) w = (0 : V),
  { suffices h : univ.affine_combination S.points w = O,
    { rw affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one _ w S.points hs O at h,
      symmetry' at h,
      rw eq_vadd_iff_vsub_eq at h,
      rw ← h,
      exact vsub_self O},
    convert affine_combination_coord_eq_self S O },
  rw h₅,
  simp only [vsub_eq_sub, zero_sub, weighted_vsub_of_point_apply, neg_eq_iff_add_eq_zero,
      ← sum_add_distrib, smul_sub, smul_sub],
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
  rw symm_apply_apply
end

lemma affine_basis.coord_perm {ι : Type*} [fintype ι] (σ : perm ι) {i : ι}
  (S T : affine_basis ι ℝ V) (O : V) (h : T.points = S.points ∘ σ) :
  S.coord (σ i) O = T.coord i O :=
begin
  classical,
  simp only [affine_basis.coord, affine_map.coe_mk, ← subtype.coe_mk i _, h],
  set f : {j // j ≠ σ i} → {j // j ≠ i} :=
    begin
      rintros ⟨j, hj⟩,
      use σ.symm j,
      rw [ne.def, (symm_apply_eq σ)],
      exact hj,
    end with hf,
  set g : {j // j ≠ i} → {j // j ≠ σ i} :=
    begin
      rintros ⟨j, hj⟩,
      use σ j,
      by_contra,
      apply hj,
      apply (equiv.injective σ) h,
    end with hg,
  set e : {j // j ≠ σ i} ≃ {j // j ≠ i} :=
  begin
    refine ⟨f,g, _, _⟩,
    { intro j,
      rw [hf, hg],
      tidy },
    { intro j,
      rw [hg, hf],
      tidy }
  end with he,
  rw equiv.sum_coords_congr e (S.basis_of (σ i)) (T.basis_of i) _,
  ext v,
  simp only [coe_reindex, function.comp_app, basis_of_apply, h, e, equiv.symm, equiv.coe_fn_mk, hg],
  congr,
  tidy
end

lemma affine_basis.pair_lin_indep {O D v₁ v₂ : V} (S : affine_basis (fin 3) ℝ V) {r₁ r₂ r₃ r₄ : ℝ}
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
    replace hindep : (({0, 1} : finset (fin 3)).weighted_vsub S.points) ![(1 : ℝ), -1, 0] = 0 →
      false := by simpa using hindep,
    apply hindep,
    rw weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ _ D,
    suffices : S.points 0 - S.points 1 = 0, { simpa},
    rw [hA₁, hB₁],
    exact sub_self D,
    simp },
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


lemma affine_basis_fin3_coord_vsub_smul_sum_eq_zero (O D : V) (S : affine_basis (fin 3) ℝ V)
  (h₁ : collinear ℝ ({S.points 0, S.points 1, D} : set V))
  (h₂ : collinear ℝ ({D, O, S.points 2} : set V)) :
  S.coord 0 O • (D -ᵥ S.points 0) + S.coord 1 O • (D -ᵥ S.points 1) = (0 : V) :=
begin
  have h := affine_basis.vsub_eq_coord_smul_sum O S D,
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
  obtain ⟨r₂, hC₁⟩ := hv₁ (S.points 2)
    (by simp only [set.mem_insert_iff, set.mem_singleton, or_true]),
  obtain ⟨r₃, hA₁⟩ := hv₂ (S.points 0)
    (by simp only [set.mem_insert_iff, true_or, eq_self_iff_true]),
  obtain ⟨r₄, hB₁⟩ := hv₂ (S.points 1)
    (by simp only [set.mem_insert_iff, true_or, eq_self_iff_true, or_true]),
  obtain ⟨r₁, hD₁⟩ := hv₁ D
    (by simp only [set.mem_insert_iff, true_or, eq_self_iff_true]),
  simp only [hC₁, hA₁, hB₁, hD₁, vadd_vsub_vadd_cancel_right, vadd_vsub, vsub_vadd_eq_vsub_sub,
    zero_sub, smul_neg, sub_self] at hsub,
  rw [hB₁, hA₁, hD₁],
  simp only [vadd_vsub_vadd_cancel_right, vadd_vsub, vsub_vadd_eq_vsub_sub, zero_sub, smul_neg,
   sub_self],
  have hlinind := affine_basis.pair_lin_indep S hA₁ hB₁ hC₁ hD₁,
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
  rw [← eq_inv_smul_iff₀, ← smul_assoc] at h₂,
  rw linear_independent_fin2 at hlinind,
  cases hlinind with h₄ h₅,
  specialize h₅
    ((r₁ + S.coord 2 O * r₂ - S.coord 2 O * r₁)⁻¹ • (-S.coord 0 O * r₃ - S.coord 1 O * r₄)),
  simp only [neg_mul_eq_neg_mul_symm, matrix.head_cons, smul_eq_mul, ne.def,
    matrix.cons_val_one, matrix.cons_val_zero] at h₅,
  exfalso,
  apply h₅,
  rw [h₂, smul_eq_mul, neg_mul_eq_neg_mul],
  exact h₃
end

lemma affine_basis.interior_coord_pos
  {ι : Type*} [fintype ι] {O : V} {T : affine_basis ι ℝ V}
  (h : O ∈ interior (convex_hull ℝ (set.range T.points))) {i : ι} : 0 < T.coord i O :=
begin
  rw interior_convex_hull_aff_basis T at h,
  rw set.mem_set_of_eq at h,
  exact h i,
end

lemma affine_basis.fin3_interior_coord_mul_dist_eq {ι : Type*} [fintype ι]
  (σ : perm ι) {O D : V} (S T : affine_basis ι ℝ V) {i j : ι} (hperm : T.points = S.points ∘ σ)
  (h : (T.coord i) O • (D -ᵥ T.points i) + (T.coord j) O • (D -ᵥ T.points j) = (0 : V))
  (hinterior : O ∈ interior (convex_hull ℝ (set.range S.points)))  :
  T.coord i O * dist (T.points i) D = T.coord j O * dist D (T.points j) :=
begin
  rw [add_eq_zero_iff_eq_neg, eq_neg_iff_eq_neg] at h,
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← norm_smul_of_nonneg _, ← norm_smul_of_nonneg _, h,
    ← smul_neg, neg_vsub_eq_vsub_rev],
  rw ← affine_basis.coord_perm σ S T O hperm,
  { apply le_of_lt,
    apply affine_basis.interior_coord_pos hinterior },
  rw ← affine_basis.coord_perm σ S T O hperm,
  { apply le_of_lt,
    apply affine_basis.interior_coord_pos hinterior }
end

lemma affine_span.simplex_eq_top [finite_dimensional ℝ V] {n : ℕ} (T : simplex ℝ V n)
  (hrank : finrank ℝ V = n): affine_span ℝ (set.range T.points) = ⊤ :=
begin
  rw [affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one T.independent,
    fintype.card_fin, hrank],
end

/--**Ceva's Theorem for a triangle with cevians that intersect at an interior point**-/
theorem ceva_theorem [finite_dimensional ℝ V] (A B C D E F O : V) (S : triangle ℝ V)
  (h₀ : finrank ℝ V = 2) (h₁ : S.points = ![A, B, C])
  (h₂ : collinear ℝ ({A, B, D} : set V)) (h₃ : collinear ℝ ({B, C, E} : set V))
  (h₄ : collinear ℝ ({C, A, F} : set V)) (h₅ : collinear ℝ ({D, O, C} : set V))
  (h₆ : collinear ℝ ({E, O, A} : set V)) (h₇ : collinear ℝ ({F, O, B} : set V))
  (h₈ : O ∈ interior (convex_hull ℝ (set.range S.points))) :
  dist A D * dist B E * dist C F  = dist D B * dist E C * dist F A :=
begin
  have hfind : finite_dimensional ℝ V := finite_dimensional_of_finrank_eq_succ h₀,
  have hspan : affine_span ℝ (set.range S.points) = ⊤,
  { rw affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one S.independent,
    { rw fintype.card_fin,
      rw h₀ }},
  have hs := S.independent,
  set T : affine_basis (fin 3) ℝ V := ⟨S.points, S.independent, hspan⟩ with hT,
  replace h₈ : O ∈ interior (convex_hull ℝ (set.range T.points)) := by exact h₈,
  set σ₁ : perm (fin 3) := equiv.refl (fin 3) with hσ₁,
  set σ₂ : perm (fin 3) := list.form_perm [0, 1, 2] with hσ₂,
  set σ₃ : perm (fin 3) := equiv.trans σ₂ σ₂ with hσ₃,
  set S₁ : triangle ℝ V := ⟨![A, B, C] ∘ σ₁, by simpa [affine_independent_equiv, ← h₁]⟩ with hS₁,
  have hS₁span := affine_span.simplex_eq_top S₁ h₀,
  set T₁ : affine_basis (fin 3) ℝ V := ⟨S₁.points, S₁.independent, hS₁span⟩ with hT₁,
  have hTσ₁ : T₁.points = T.points ∘ σ₁ := by simp [h₁],
  replace h₂ : collinear ℝ ({S₁.points 0, S₁.points 1, D} : set V) := by convert h₂,
  replace h₅ : collinear ℝ ({D, O, S₁.points 2} : set V) := by convert h₅,
  set S₂ : triangle ℝ V := ⟨![A, B, C] ∘ σ₂, by simpa [affine_independent_equiv, ← h₁]⟩ with hS₂,
  have hS₂span := affine_span.simplex_eq_top S₂ h₀,
  set T₂ : affine_basis (fin 3) ℝ V := ⟨S₂.points, S₂.independent, hS₂span⟩ with hT₂,
  have hTσ₂ : T₂.points = T.points ∘ σ₂ := by simp [h₁],
  replace h₃ : collinear ℝ ({S₂.points 0, S₂.points 1, E} : set V) := by convert h₃,
  replace h₆ : collinear ℝ ({E, O, S₂.points 2} : set V) := by convert h₆,
  set S₃ : triangle ℝ V := ⟨![A, B, C] ∘ σ₃, by simp only [affine_independent_equiv, ← h₁,
    S.independent]⟩ with hS₃,
  have hS₃span := affine_span.simplex_eq_top S₃ h₀,
  set T₃ : affine_basis (fin 3) ℝ V := ⟨S₃.points, S₃.independent, hS₃span⟩ with hT₃,
  have hTσ₃ : T₃.points = T.points ∘ σ₃ := by simp [h₁],
  replace h₄ : collinear ℝ ({S₃.points 0, S₃.points 1, F} : set V) := by convert h₄,
  replace h₇ : collinear ℝ ({F, O, S₃.points 2} : set V) := by convert h₇,
  have hwnezero : T.coord 0 O * T.coord 1 O * T.coord 2 O ≠ 0,
  { apply ne_of_gt,
    simp only [mul_pos, affine_basis.interior_coord_pos h₈] },
  have hADB := affine_basis.fin3_interior_coord_mul_dist_eq σ₁ T T₁ hTσ₁
    ( affine_basis_fin3_coord_vsub_smul_sum_eq_zero O D T₁ h₂ h₅) h₈,
  have hBEC := affine_basis.fin3_interior_coord_mul_dist_eq σ₂ T T₂ hTσ₂
    (affine_basis_fin3_coord_vsub_smul_sum_eq_zero O E T₂ h₃ h₆) h₈,
  have hCFA := affine_basis.fin3_interior_coord_mul_dist_eq σ₃ T T₃ hTσ₃
    (affine_basis_fin3_coord_vsub_smul_sum_eq_zero O F T₃ h₄ h₇) h₈,
  clear h₂ h₃ h₄ h₅ h₆ h₇ h₈,
  have hs₁ : σ₂ 0 = 1 := by refl,
  have hs₂ : σ₂ 1 = 2 := by refl,
  have hs₃ : σ₂ 2 = 3 := by refl,
  have hb : ![A, B, C] 1 = B := by refl,
  have hc : ![A, B, C] 2 = C := by refl,
  have ha : ![A, B, C] 3 = A := by refl,
  have h := congr_arg2 (λ a b, a * b) (congr_arg2 (λ a b, a * b) hADB hBEC) hCFA,
  simp only [← affine_basis.coord_perm σ₁ T T₁ O hTσ₁, ← affine_basis.coord_perm σ₂ T T₂ O hTσ₂,
    ← affine_basis.coord_perm σ₃ T T₃ O hTσ₃] at h,
  clear hADB hBEC hCFA hTσ₁ hTσ₂ hTσ₃ hT₁ hT₂ hT₃ T₁ T₂ T₃ hS₁span hS₂span hS₃span,
  dsimp at h, -- non-terminal dsimp, do not know how to fix it
  simp only [hs₁, hs₂, hs₃, hb, hc, ha] at h,
  replace h : (T.coord 0 O * T.coord 1 O * T.coord 2 O) * (dist A D * dist B E * dist C F) =
    (T.coord 3 O * T.coord 1 O * T.coord 2 O) * (dist D B * dist E C * dist F A) := by linarith,
  rw ← mul_right_inj' hwnezero,
  exact h
end
