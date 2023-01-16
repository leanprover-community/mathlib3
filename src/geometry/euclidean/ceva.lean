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

## Main declarations

* `geometry.ceva_of_mem_interior`: Ceva's theorem for an interior point

## TODO

Generalize to exterior points as well, using signed distances.

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
  x -ᵥ o = ∑ i, S.coord i o • (x -ᵥ S i) :=
begin
  convert (finset.univ.sum_smul_const_vsub_eq_vsub_affine_combination (λ i, S.coord i o) S
    x $ S.sum_coord_apply_eq_one o).symm,
  exact (S.affine_combination_coord_eq_self _).symm,
end

end ring

section field
variables [field 𝕜] [add_comm_group E] [module 𝕜 E]

lemma affine_basis.pair_lin_indep {o d v₁ v₂ : E} (S : affine_basis (fin 3) 𝕜 E) {r₁ r₂ r₃ r₄ : 𝕜}
  (hA₁ : S 0 = r₃ • v₂ +ᵥ d) (hB₁ : S 1 = r₄ • v₂ +ᵥ d) (hC₁ : S 2 = r₂ • v₁ +ᵥ o)
  (hD₁ : d = r₁ • v₁ +ᵥ o) :
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
    replace hindep : (({0, 1} : finset (fin 3)).weighted_vsub S) ![(1 : 𝕜), -1, 0] = 0 →
      false := by simpa using hindep,
    apply hindep,
    rw weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ _ d,
    suffices : S 0 - S 1 = 0, { simpa},
    rw [hA₁, hB₁],
    exact sub_self d,
    simp },
  intros a ha,
  simp only [matrix.head_cons, matrix.cons_val_one, matrix.cons_val_zero] at ha,
  subst ha,
  subst hD₁,
  have hindep := S.ind,
  rw affine_independent_iff_not_collinear at hindep,
  apply hindep,
  have hA₂ : S 0 ∈ set.range S := by use 0,
  rw collinear_iff_of_mem hA₂,
  refine ⟨v₂, λ p hp, _⟩,
  rw set.range_comp at hp,
  simp only [true_and, set.mem_range, set.mem_image, exists_apply_eq_apply] at hp,
  cases hp with n hpn,
  fin_cases n,
  { use 0,
    rw ← hpn,
    simp, },
  { use r₄ - r₃,
    rw [← hpn, hB₁, hA₁],
    simp only [sub_smul, vadd_vadd, ← add_assoc, ← smul_assoc, smul_eq_mul, sub_add_cancel] },
  { use r₂ • a - r₁ • a - r₃,
    rw [← hpn, hC₁, hA₁],
    simp only [sub_smul, vadd_vadd, ← add_assoc, ← smul_assoc, smul_eq_mul, sub_add_cancel] }
end

lemma affine_basis_fin3_coord_vsub_smul_sum_eq_zero (o d : E) (S : affine_basis (fin 3) 𝕜 E)
  (h₁ : collinear 𝕜 ({S 0, S 1, d} : set E))
  (habd : collinear 𝕜 ({d, o, S 2} : set E)) :
  S.coord 0 o • (d -ᵥ S 0) + S.coord 1 o • (d -ᵥ S 1) = (0 : E) :=
begin
  have h := affine_basis.vsub_eq_coord_smul_sum o S d,
  have hsub : d -ᵥ o - S.coord 2 o • (d -ᵥ S 2) = S.coord 0 o • (d -ᵥ S 0) +
  S.coord 1 o • (d -ᵥ S 1),
  { apply vadd_right_cancel (S.coord 2 o • (d -ᵥ S 2)),
    simp only [vsub_eq_sub, sub_add_cancel, vadd_eq_add],
    simp only [fin.sum_univ_succ, fin.sum_univ_zero, add_zero] at h,
    convert h using 1,
    norm_num,
    abel },
  have hO : o ∈ ({d, o, S 2} : set E),
  { simp only [set.mem_insert_iff, true_or, eq_self_iff_true, or_true] },
  rw (collinear_iff_of_mem 𝕜 hO) at habd,
  cases habd with v₁ hv₁,
  have hD₁ : d ∈ ({S 0, S 1, d} : set E),
  { simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
  rw (collinear_iff_of_mem 𝕜 hD₁) at h₁,
  cases h₁ with v₂ hv₂,
  obtain ⟨r₂, hC₁⟩ := hv₁ (S 2) (by simp only [set.mem_insert_iff, set.mem_singleton, or_true]),
  obtain ⟨r₃, hA₁⟩ := hv₂ (S 0) (by simp only [set.mem_insert_iff, true_or, eq_self_iff_true]),
  obtain ⟨r₄, hB₁⟩ := hv₂ (S 1)
    (by simp only [set.mem_insert_iff, true_or, eq_self_iff_true, or_true]),
  obtain ⟨r₁, hD₁⟩ := hv₁ d (by simp only [set.mem_insert_iff, true_or, eq_self_iff_true]),
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
  have habd : (r₁ + S.coord 2 o • r₂ - S.coord 2 o • r₁) • v₁ = (- S.coord 0 o • r₃ -
    S.coord 1 o • r₄) • v₂,
  { rw [hv₁, hv₂],
    exact hsub },
  simp only [smul_eq_mul] at habd,
  rw [← sub_eq_add_neg, ← neg_smul, ← smul_assoc, ← smul_assoc, ← sub_smul],
  by_cases hbce : (r₁ + S.coord 2 o * r₂ - S.coord 2 o * r₁) = 0,
  simp only [hbce, zero_smul] at habd,
  simp only [smul_eq_mul, ← habd],
  rw [← eq_inv_smul_iff₀, ← smul_assoc] at habd,
  rw linear_independent_fin2 at hlinind,
  cases hlinind with hcaf hdoc,
  specialize hdoc
    ((r₁ + S.coord 2 o * r₂ - S.coord 2 o * r₁)⁻¹ • (-S.coord 0 o * r₃ - S.coord 1 o * r₄)),
  simp only [neg_mul_eq_neg_mul_symm, matrix.head_cons, smul_eq_mul, ne.def,
    matrix.cons_val_one, matrix.cons_val_zero] at hdoc,
  refine (hdoc _).elim,
  rw [habd, smul_eq_mul, neg_mul_eq_neg_mul],
  exact hbce,
end

end field
end add_comm_group

variables [normed_add_comm_group E] [normed_space ℝ E]

lemma affine_basis.fin3_interior_coord_mul_dist_eq [fintype ι]
  (σ : perm ι) {o d : E} (S T : affine_basis ι ℝ E) {i j : ι} (hperm : T = S ∘ σ)
  (h : T.coord i o • (d -ᵥ T i : E) + T.coord j o • (d -ᵥ T j) = 0)
  (hinterior : ∀ i, 0 ≤ S.coord i o) :
  T.coord i o * dist (T i) d = T.coord j o * dist d (T j) :=
begin
  rw [add_eq_zero_iff_eq_neg, eq_neg_iff_eq_neg] at h,
  rw [dist_eq_norm_vsub E, dist_eq_norm_vsub E, ← norm_smul_of_nonneg _, ← norm_smul_of_nonneg _, h,
    ← smul_neg, neg_vsub_eq_vsub_rev],
  rw ← affine_basis.coord_perm σ S T o hperm,
  { exact hinterior _ },
  rw ← affine_basis.coord_perm σ S T o hperm,
  { exact hinterior _ }
end

namespace geometry

/-- **Ceva's Theorem** for a triangle with cevians that intersect at an interior point. -/
theorem ceva_of_mem_interior [finite_dimensional ℝ E] (a b c d e f o : E) (S : triangle ℝ E)
  (hE : finrank ℝ E = 2) (h₁ : S = ![a, b, c])
  (habd : collinear ℝ ({a, b, d} : set E)) (hbce : collinear ℝ ({b, c, e} : set E))
  (hcaf : collinear ℝ ({c, a, f} : set E)) (hdoc : collinear ℝ ({d, o, c} : set E))
  (heoa : collinear ℝ ({e, o, a} : set E)) (hfob : collinear ℝ ({f, o, b} : set E))
  (ho : o ∈ interior (convex_hull ℝ (set.range S))) :
  dist a d * dist b e * dist c f  = dist d b * dist e c * dist f a :=
begin
  have hfind : finite_dimensional ℝ E := finite_dimensional_of_finrank_eq_succ hE,
  have hspan : affine_span ℝ (set.range S) = ⊤,
  { rw [S.independent.affine_span_eq_top_iff_card_eq_finrank_add_one, fintype.card_fin, hE] },
  have hs := S.independent,
  set T : affine_basis (fin 3) ℝ E := ⟨S, S.independent, hspan⟩ with hT,
  change o ∈ interior (convex_hull ℝ (set.range T)) at ho,
  rw affine_basis.interior_convex_hull at ho,
  set σ₁ : perm (fin 3) := equiv.refl (fin 3) with hσ₁,
  set σ₂ : perm (fin 3) := list.form_perm [0, 1, 2] with hσ₂,
  set σ₃ : perm (fin 3) := equiv.trans σ₂ σ₂ with hσ₃,
  set S₁ : triangle ℝ E := ⟨![a, b, c] ∘ σ₁, by simpa [affine_independent_equiv, ← h₁]⟩ with hS₁,
  have hS₁span := S₁.span_eq_top hE,
  set T₁ : affine_basis (fin 3) ℝ E := ⟨S₁, S₁.independent, hS₁span⟩ with hT₁,
  have hTσ₁ : T₁ = T ∘ σ₁ := by simp [h₁],
  replace habd : collinear ℝ ({S₁ 0, S₁ 1, d} : set E) := by convert habd,
  replace hdoc : collinear ℝ ({d, o, S₁ 2} : set E) := by convert hdoc,
  set S₂ : triangle ℝ E := ⟨![a, b, c] ∘ σ₂, by simpa [affine_independent_equiv, ← h₁]⟩ with hS₂,
  have hS₂span := S₂.span_eq_top hE,
  set T₂ : affine_basis (fin 3) ℝ E := ⟨S₂, S₂.independent, hS₂span⟩ with hT₂,
  have hTσ₂ : T₂ = T ∘ σ₂ := by simp [h₁],
  replace hbce : collinear ℝ ({S₂ 0, S₂ 1, e} : set E) := by convert hbce,
  replace heoa : collinear ℝ ({e, o, S₂ 2} : set E) := by convert heoa,
  set S₃ : triangle ℝ E := ⟨![a, b, c] ∘ σ₃, by simp only [affine_independent_equiv, ← h₁,
    S.independent]⟩ with hS₃,
  have hS₃span := S₃.span_eq_top hE,
  set T₃ : affine_basis (fin 3) ℝ E := ⟨S₃, S₃.independent, hS₃span⟩ with hT₃,
  have hTσ₃ : T₃ = T ∘ σ₃ := by simp [h₁],
  replace hcaf : collinear ℝ ({S₃ 0, S₃ 1, f} : set E) := by convert hcaf,
  replace hfob : collinear ℝ ({f, o, S₃ 2} : set E) := by convert hfob,
  have hwnezero : T.coord 0 o * T.coord 1 o * T.coord 2 o ≠ 0 :=
    mul_ne_zero (mul_pos (ho _) $ ho _).ne' (ho _).ne',
  have hADB := affine_basis.fin3_interior_coord_mul_dist_eq σ₁ T T₁ hTσ₁
    (affine_basis_fin3_coord_vsub_smul_sum_eq_zero o d T₁ habd hdoc) (λ _, (ho _).le),
  have hBEC := affine_basis.fin3_interior_coord_mul_dist_eq σ₂ T T₂ hTσ₂
    (affine_basis_fin3_coord_vsub_smul_sum_eq_zero o e T₂ hbce heoa) (λ _, (ho _).le),
  have hCFA := affine_basis.fin3_interior_coord_mul_dist_eq σ₃ T T₃ hTσ₃
    (affine_basis_fin3_coord_vsub_smul_sum_eq_zero o f T₃ hcaf hfob) (λ _, (ho _).le),
  clear habd hbce hcaf hdoc heoa hfob ho,
  have hb : ![a, b, c] 1 = b := by refl,
  have hc : ![a, b, c] 2 = c := by refl,
  have ha : ![a, b, c] 3 = a := by refl,
  have h := congr_arg2 (λ a b, a * b) (congr_arg2 (λ a b, a * b) hADB hBEC) hCFA,
  simp only [← affine_basis.coord_perm σ₁ T T₁ o hTσ₁, ← affine_basis.coord_perm σ₂ T T₂ o hTσ₂,
    ← affine_basis.coord_perm σ₃ T T₃ o hTσ₃] at h,
  clear hADB hBEC hCFA hTσ₁ hTσ₂ hTσ₃ hT₁ hT₂ hT₃ T₁ T₂ T₃ hS₁span hS₂span hS₃span,
  dsimp at h,
  simp only [hσ₂, hb, hc, ha] at h,
  replace h : (T.coord 0 o * T.coord 1 o * T.coord 2 o) * (dist a d * dist b e * dist c f) =
    (T.coord 3 o * T.coord 1 o * T.coord 2 o) * (dist d b * dist e c * dist f a) := by linarith,
  rwa ←mul_right_inj' hwnezero,
end

end geometry
