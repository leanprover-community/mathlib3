/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import analysis.normed_space.add_torsor_bases
import group_theory.perm.list

/-!
# Ceva's Theorem

This file proves Ceva's theorem in euclidean geometry following the barycentric coordinate proof.

## Implementation notes

Because of the currently generality of `interior_convex_hull_aff_basis` is stated in, we prove
Ceva's theorem in it's current form. This will need to be upgraded to the usual setting of
Euclidean Geometry results after the affinity refactor.

## References

* https://en.wikipedia.org/wiki/Ceva%27s_theorem
* This is problem 61 on [Freek's list](https://www.cs.ru.nl/~freek/100/).
-/

open affine affine_basis basis finite_dimensional finset fintype equiv
open_locale big_operators

variables {𝕜 V E ι ι' : Type*}

section add_comm_group
variables [add_comm_group V]

section ring
variables [ring 𝕜] [module 𝕜 V] [add_torsor V E]
include V

lemma affine_basis.vsub_eq_coord_smul_sum [fintype ι] (o : E) (S : affine_basis ι 𝕜 E) (x : E) :
  x -ᵥ o = ∑ i, S.coord i o • (x -ᵥ S.points i) :=
begin
  convert (finset.univ.sum_smul_const_vsub_eq_vsub_affine_combination (λ i, S.coord i o)
    S.points x (S.sum_coord_apply_eq_one o)).symm,
  exact (S.affine_combination_coord_eq_self _).symm,
end

lemma equiv.sum_coords_congr [fintype ι] [fintype ι'] (e : ι ≃ ι') (b : basis ι 𝕜 V)
  (c : basis ι' 𝕜 V) (h : c = b.reindex e) :
  b.sum_coords = c.sum_coords :=
begin
  ext x,
  simp only [coe_sum_coords_of_fintype, h, reindex_repr, reindex, basis.coord_apply,
    linear_equiv.trans_apply, finsupp.dom_congr_apply, fintype.sum_apply,
    finsupp.equiv_map_domain_apply, finsupp.dom_lcongr_apply],
  rw sum_equiv e,
  intro i,
  rw symm_apply_apply
end

lemma affine_basis.coord_perm [fintype ι] (σ : perm ι) {i : ι}
  (S T : affine_basis ι 𝕜 E) (o : E) (h : T.points = S.points ∘ σ) :
  S.coord (σ i) o = T.coord i o :=
begin
  classical,
  simp only [affine_basis.coord, affine_map.coe_mk, ← subtype.coe_mk i _, h],
  set f : {j // j ≠ σ i} → {j // j ≠ i} :=
    begin
      rintro ⟨j, hj⟩,
      use σ.symm j,
      rw [ne.def, (symm_apply_eq σ)],
      exact hj,
    end with hf,
  set g : {j // j ≠ i} → {j // j ≠ σ i} :=
    begin
      rintro ⟨j, hj⟩,
      use σ j,
      by_contra,
      exact hj (equiv.injective σ h),
    end with hg,
  set e : {j // j ≠ σ i} ≃ {j // j ≠ i} :=
  begin
    refine ⟨f, g, λ j, _, λ j, _⟩,
    { rw [hf, hg],
      cases j,
      simp },
    { rw [hg, hf],
      cases j,
      simp }
  end with he,
  rw equiv.sum_coords_congr e (S.basis_of (σ i)) (T.basis_of i) _,
  ext v,
  simp only [coe_reindex, function.comp_app, basis_of_apply, h, e, equiv.symm, equiv.coe_fn_mk, hg],
  congr,
  cases v,
  refl,
end

end ring

section field
variables [field 𝕜] [add_comm_group E] [module 𝕜 E]

lemma affine_basis.pair_lin_indep {o d v₁ v₂ : E} (S : affine_basis (fin 3) 𝕜 E) {r₁ r₂ r₃ r₄ : 𝕜}
  (hA₁ : S.points 0 = r₃ • v₂ +ᵥ d) (hB₁ : S.points 1 = r₄ • v₂ +ᵥ d)
  (hC₁ : S.points 2 = r₂ • v₁ +ᵥ o) (hD₁ : d = r₁ • v₁ +ᵥ o) :
  linear_independent 𝕜 ![v₁, v₂] :=
begin
  rw linear_independent_fin2,
  split,
  { simp only [matrix.head_cons, ne.def, matrix.cons_val_one],
    intro hv₂,
    subst hv₂,
    simp only [smul_zero, zero_vadd, function.comp_app] at hA₁ hB₁,
    have hindep := S.ind,
    rw affine_independent at hindep,
    specialize hindep {0, 1} (![1, -1, 0]),
    replace hindep : (({0, 1} : finset (fin 3)).weighted_vsub S.points) ![(1 : 𝕜), -1, 0] = 0 →
      false := by simpa using hindep,
    apply hindep,
    rw weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ _ d,
    suffices : S.points 0 - S.points 1 = 0, { simpa},
    rw [hA₁, hB₁],
    exact sub_self d,
    simp },
  { intros a ha,
    simp only [matrix.head_cons, matrix.cons_val_one, matrix.cons_val_zero] at ha,
    subst ha,
    subst hD₁,
    have hindep := S.ind,
    rw affine_independent_iff_not_collinear at hindep,
    apply hindep,
    have hA₂ : S.points 0 ∈ set.range S.points := by use 0,
    rw (collinear_iff_of_mem 𝕜 hA₂),
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

lemma affine_basis_fin3_coord_vsub_smul_sum_eq_zero (o d : E) (S : affine_basis (fin 3) 𝕜 E)
  (h₁ : collinear 𝕜 ({S.points 0, S.points 1, d} : set E))
  (h₂ : collinear 𝕜 ({d, o, S.points 2} : set E)) :
  S.coord 0 o • (d -ᵥ S.points 0) + S.coord 1 o • (d -ᵥ S.points 1) = (0 : E) :=
begin
  have h := affine_basis.vsub_eq_coord_smul_sum o S d,
  have hsub : d -ᵥ o - S.coord 2 o • (d -ᵥ S.points 2) = S.coord 0 o • (d -ᵥ S.points 0) +
  S.coord 1 o • (d -ᵥ S.points 1),
  { apply vadd_right_cancel (S.coord 2 o • (d -ᵥ S.points 2)),
    simp only [vsub_eq_sub, sub_add_cancel, vadd_eq_add],
    simp only [fin.sum_univ_succ, fin.sum_univ_zero, add_zero] at h,
    convert h using 1,
    norm_num,
    abel },
  have hO : o ∈ ({d, o, S.points 2} : set E),
  { simp only [set.mem_insert_iff, true_or, eq_self_iff_true, or_true] },
  rw (collinear_iff_of_mem 𝕜 hO) at h₂,
  cases h₂ with v₁ hv₁,
  have hD₁ : d ∈ ({S.points 0, S.points 1, d} : set E),
  { simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
  rw (collinear_iff_of_mem 𝕜 hD₁) at h₁,
  cases h₁ with v₂ hv₂,
  obtain ⟨r₂, hC₁⟩ := hv₁ (S.points 2)
    (by simp only [set.mem_insert_iff, set.mem_singleton, or_true]),
  obtain ⟨r₃, hA₁⟩ := hv₂ (S.points 0)
    (by simp only [set.mem_insert_iff, true_or, eq_self_iff_true]),
  obtain ⟨r₄, hB₁⟩ := hv₂ (S.points 1)
    (by simp only [set.mem_insert_iff, true_or, eq_self_iff_true, or_true]),
  obtain ⟨r₁, hD₁⟩ := hv₁ d
    (by simp only [set.mem_insert_iff, true_or, eq_self_iff_true]),
  simp only [hC₁, hA₁, hB₁, hD₁, vadd_vsub_vadd_cancel_right, vadd_vsub, vsub_vadd_eq_vsub_sub,
    zero_sub, smul_neg, sub_self] at hsub,
  rw [hB₁, hA₁, hD₁],
  simp only [vadd_vsub_vadd_cancel_right, vadd_vsub, vsub_vadd_eq_vsub_sub, zero_sub, smul_neg,
   sub_self],
  have hlinind := affine_basis.pair_lin_indep S hA₁ hB₁ hC₁ hD₁,
  have hv₁ : (r₁ + S.coord 2 o • r₂ - S.coord 2 o • r₁) • v₁ = r₁ • v₁ -
    S.coord 2 o • (r₁ • v₁ - r₂ • v₁),
  { rw [←sub_smul, ←smul_assoc],
    simp only [smul_eq_mul, mul_sub, sub_smul, add_smul],
    rw sub_sub_assoc_swap },
  have hv₂ : (- S.coord 0 o • r₃ - S.coord 1 o • r₄) • v₂ = -(S.coord 0 o • r₃ • v₂) +
    -(S.coord 1 o • r₄ • v₂),
  { simp only [sub_smul, ← smul_assoc, smul_eq_mul, neg_smul, ← sub_eq_add_neg] },
  have h₂ : (r₁ + S.coord 2 o • r₂ - S.coord 2 o • r₁) • v₁ = (- S.coord 0 o • r₃ -
    S.coord 1 o • r₄) • v₂,
  { rw [hv₁, hv₂],
    exact hsub },
  simp only [smul_eq_mul] at h₂,
  rw [← sub_eq_add_neg, ← neg_smul, ← smul_assoc, ← smul_assoc, ← sub_smul],
  by_cases h₃ : (r₁ + S.coord 2 o * r₂ - S.coord 2 o * r₁) = 0,
  simp only [h₃, zero_smul] at h₂,
  simp only [smul_eq_mul, ← h₂],
  rw [← eq_inv_smul_iff₀, ← smul_assoc] at h₂,
  rw linear_independent_fin2 at hlinind,
  cases hlinind with h₄ h₅,
  specialize h₅
    ((r₁ + S.coord 2 o * r₂ - S.coord 2 o * r₁)⁻¹ • (-S.coord 0 o * r₃ - S.coord 1 o * r₄)),
  simp only [neg_mul_eq_neg_mul_symm, matrix.head_cons, smul_eq_mul, ne.def,
    matrix.cons_val_one, matrix.cons_val_zero] at h₅,
  refine (h₅ _).elim,
  rw [h₂, smul_eq_mul, neg_mul_eq_neg_mul],
  exact h₃,
end

lemma affine.simplex.span_eq_top [finite_dimensional 𝕜 E] {n : ℕ} (T : simplex 𝕜 E n)
  (hrank : finrank 𝕜 E = n) :
  affine_span 𝕜 (set.range T.points) = ⊤ :=
by rw [affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one T.independent,
    fintype.card_fin, hrank]

end field
end add_comm_group

variables [normed_group E] [normed_space ℝ E]

lemma affine_basis.interior_coord_pos [fintype ι] {o : E} {T : affine_basis ι ℝ E}
  (h : o ∈ interior (convex_hull ℝ (set.range T.points))) {i : ι} :
  0 < T.coord i o :=
begin
  rw interior_convex_hull_aff_basis T at h,
  exact h i,
end

lemma affine_basis.fin3_interior_coord_mul_dist_eq [fintype ι]
  (σ : perm ι) {o d : E} (S T : affine_basis ι ℝ E) {i j : ι} (hperm : T.points = S.points ∘ σ)
  (h : (T.coord i) o • (d -ᵥ T.points i) + (T.coord j) o • (d -ᵥ T.points j) = (0 : E))
  (hinterior : o ∈ interior (convex_hull ℝ (set.range S.points)))  :
  T.coord i o * dist (T.points i) d = T.coord j o * dist d (T.points j) :=
begin
  rw [add_eq_zero_iff_eq_neg, eq_neg_iff_eq_neg] at h,
  rw [dist_eq_norm_vsub E, dist_eq_norm_vsub E, ← norm_smul_of_nonneg _, ← norm_smul_of_nonneg _, h,
    ← smul_neg, neg_vsub_eq_vsub_rev],
  rw ← affine_basis.coord_perm σ S T o hperm,
  { apply le_of_lt,
    apply affine_basis.interior_coord_pos hinterior },
  rw ← affine_basis.coord_perm σ S T o hperm,
  { apply le_of_lt,
    apply affine_basis.interior_coord_pos hinterior }
end

/-- **Ceva's Theorem** for a triangle with cevians that intersect at an interior point. -/
theorem ceva_theorem [finite_dimensional ℝ E] (a b c d e f o : E) (S : triangle ℝ E)
  (h₀ : finrank ℝ E = 2) (h₁ : S.points = ![a, b, c])
  (h₂ : collinear ℝ ({a, b, d} : set E)) (h₃ : collinear ℝ ({b, c, e} : set E))
  (h₄ : collinear ℝ ({c, a, f} : set E)) (h₅ : collinear ℝ ({d, o, c} : set E))
  (h₆ : collinear ℝ ({e, o, a} : set E)) (h₇ : collinear ℝ ({f, o, b} : set E))
  (h₈ : o ∈ interior (convex_hull ℝ (set.range S.points))) :
  dist a d * dist b e * dist c f  = dist d b * dist e c * dist f a :=
begin
  have hfind : finite_dimensional ℝ E := finite_dimensional_of_finrank_eq_succ h₀,
  have hspan : affine_span ℝ (set.range S.points) = ⊤,
  { rw affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one S.independent,
    { rw fintype.card_fin,
      rw h₀ }},
  have hs := S.independent,
  set T : affine_basis (fin 3) ℝ E := ⟨S.points, S.independent, hspan⟩ with hT,
  replace h₈ : o ∈ interior (convex_hull ℝ (set.range T.points)) := by exact h₈,
  set σ₁ : perm (fin 3) := equiv.refl (fin 3) with hσ₁,
  set σ₂ : perm (fin 3) := list.form_perm [0, 1, 2] with hσ₂,
  set σ₃ : perm (fin 3) := equiv.trans σ₂ σ₂ with hσ₃,
  set S₁ : triangle ℝ E := ⟨![a, b, c] ∘ σ₁, by simpa [affine_independent_equiv, ← h₁]⟩ with hS₁,
  have hS₁span := S₁.span_eq_top h₀,
  set T₁ : affine_basis (fin 3) ℝ E := ⟨S₁.points, S₁.independent, hS₁span⟩ with hT₁,
  have hTσ₁ : T₁.points = T.points ∘ σ₁ := by simp [h₁],
  replace h₂ : collinear ℝ ({S₁.points 0, S₁.points 1, d} : set E) := by convert h₂,
  replace h₅ : collinear ℝ ({d, o, S₁.points 2} : set E) := by convert h₅,
  set S₂ : triangle ℝ E := ⟨![a, b, c] ∘ σ₂, by simpa [affine_independent_equiv, ← h₁]⟩ with hS₂,
  have hS₂span := S₂.span_eq_top h₀,
  set T₂ : affine_basis (fin 3) ℝ E := ⟨S₂.points, S₂.independent, hS₂span⟩ with hT₂,
  have hTσ₂ : T₂.points = T.points ∘ σ₂ := by simp [h₁],
  replace h₃ : collinear ℝ ({S₂.points 0, S₂.points 1, e} : set E) := by convert h₃,
  replace h₆ : collinear ℝ ({e, o, S₂.points 2} : set E) := by convert h₆,
  set S₃ : triangle ℝ E := ⟨![a, b, c] ∘ σ₃, by simp only [affine_independent_equiv, ← h₁,
    S.independent]⟩ with hS₃,
  have hS₃span := S₃.span_eq_top h₀,
  set T₃ : affine_basis (fin 3) ℝ E := ⟨S₃.points, S₃.independent, hS₃span⟩ with hT₃,
  have hTσ₃ : T₃.points = T.points ∘ σ₃ := by simp [h₁],
  replace h₄ : collinear ℝ ({S₃.points 0, S₃.points 1, f} : set E) := by convert h₄,
  replace h₇ : collinear ℝ ({f, o, S₃.points 2} : set E) := by convert h₇,
  have hwnezero : T.coord 0 o * T.coord 1 o * T.coord 2 o ≠ 0,
  { apply ne_of_gt,
    simp only [mul_pos, affine_basis.interior_coord_pos h₈] },
  have hADB := affine_basis.fin3_interior_coord_mul_dist_eq σ₁ T T₁ hTσ₁
    ( affine_basis_fin3_coord_vsub_smul_sum_eq_zero o d T₁ h₂ h₅) h₈,
  have hBEC := affine_basis.fin3_interior_coord_mul_dist_eq σ₂ T T₂ hTσ₂
    (affine_basis_fin3_coord_vsub_smul_sum_eq_zero o e T₂ h₃ h₆) h₈,
  have hCFA := affine_basis.fin3_interior_coord_mul_dist_eq σ₃ T T₃ hTσ₃
    (affine_basis_fin3_coord_vsub_smul_sum_eq_zero o f T₃ h₄ h₇) h₈,
  clear h₂ h₃ h₄ h₅ h₆ h₇ h₈,
  have hs₁ : σ₂ 0 = 1 := by refl,
  have hs₂ : σ₂ 1 = 2 := by refl,
  have hs₃ : σ₂ 2 = 3 := by refl,
  have hb : ![a, b, c] 1 = b := by refl,
  have hc : ![a, b, c] 2 = c := by refl,
  have ha : ![a, b, c] 3 = a := by refl,
  have h := congr_arg2 (λ a b, a * b) (congr_arg2 (λ a b, a * b) hADB hBEC) hCFA,
  simp only [← affine_basis.coord_perm σ₁ T T₁ o hTσ₁, ← affine_basis.coord_perm σ₂ T T₂ o hTσ₂,
    ← affine_basis.coord_perm σ₃ T T₃ o hTσ₃] at h,
  clear hADB hBEC hCFA hTσ₁ hTσ₂ hTσ₃ hT₁ hT₂ hT₃ T₁ T₂ T₃ hS₁span hS₂span hS₃span,
  dsimp at h,
  simp only [hs₁, hs₂, hs₃, hb, hc, ha] at h,
  replace h : (T.coord 0 o * T.coord 1 o * T.coord 2 o) * (dist a d * dist b e * dist c f) =
    (T.coord 3 o * T.coord 1 o * T.coord 2 o) * (dist d b * dist e c * dist f a) := by linarith,
  rw ← mul_right_inj' hwnezero,
  exact h,
end
