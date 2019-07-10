/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

The mean value inequality: a bound on the derivative of a function implies that this function
is Lipschitz continuous for the same bound.
-/


import analysis.calculus.deriv

set_option class.instance_max_depth 90

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F]

open metric set lattice asymptotics continuous_linear_map


/-- The mean value theorem along a segment: a bound on the derivative of a function along a segment
implies a bound on the distance of the endpoints images -/
theorem norm_image_sub_le_of_norm_deriv_le_segment {f : ℝ → F} {C : ℝ}
  (hf : differentiable_on ℝ f (Icc 0 1))
  (bound : ∀t ∈ Icc (0:ℝ) 1, ∥fderiv_within ℝ f (Icc 0 1) t∥ ≤ C) :
  ∥f 1 - f 0∥ ≤ C :=
begin
  /- Let D > C. We will show that, for all t ∈ [0,1], one has ∥f t - f 0∥ ≤ D * t. This is true
  for t=0. Let k be maximal in [0,1] for which this holds. By continuity of all functions, the
  maximum is realized. If k were <1, then a point x slightly to its right would satisfy
  ∥f x - f k∥ ≤ D * (k-x), since the differential of f at k has norm at most C < D. Therefore,
  the point x also satisfies ∥f x - f 0∥ ≤ D * x, contradicting the maximality of k. Hence, k = 1. -/
  refine le_of_forall_le_of_dense (λD hD, _),
  let K := {t ∈ Icc (0 : ℝ) 1 | ∥f t - f 0∥ ≤ D * t},
  let k := Sup K,
  have k_mem_K : k ∈ K,
  { refine cSup_mem_of_is_closed _ _ _,
    show K ≠ ∅,
    { have : (0 : ℝ) ∈ K, by simp [K, le_refl, zero_le_one],
      apply ne_empty_of_mem this },
    show bdd_above K, from ⟨1, λy hy, hy.1.2⟩,
    have A : continuous_on (λt:ℝ, (∥f t - f 0∥, D * t)) (Icc 0 1),
    { apply continuous_on.prod,
      { refine continuous_norm.comp_continuous_on _,
        apply continuous_on.sub hf.continuous_on continuous_on_const },
      { exact (continuous_mul continuous_const continuous_id).continuous_on } },
    show is_closed K, from
      A.preimage_closed_of_closed is_closed_Icc (ordered_topology.is_closed_le' _) },
  have : k = 1,
  { by_contradiction k_ne_1,
    have k_lt_1 : k < 1 := lt_of_le_of_ne k_mem_K.1.2 k_ne_1,
    have : 0 ≤ k := k_mem_K.1.1,
    let g := fderiv_within ℝ f (Icc 0 1) k,
    let h := λx, f x - f k - g (x-k),
    have : is_o (λ x, h x) (λ x, x - k) (nhds_within k (Icc 0 1)) :=
      (hf k k_mem_K.1).has_fderiv_within_at,
    have : {x | ∥h x∥ ≤ (D-C) * ∥x-k∥} ∈ nhds_within k (Icc 0 1) :=
      this (D-C) (sub_pos_of_lt hD),
    rcases (mem_nhds_within _ _ _).1 this with ⟨s, s_open, ks, hs⟩,
    rcases is_open_iff.1 s_open k ks with ⟨ε, εpos, hε⟩,
    change 0 < ε at εpos,
    let δ := min ε (1-k),
    have δpos : 0 < δ, by simp [δ, εpos, k_lt_1],
    let x := k + δ/2,
    have k_lt_x : k < x, by { simp only [x], linarith },
    have x_lt_1 : x < 1 := calc
      x < k + δ : add_lt_add_left (half_lt_self δpos) _
      ... ≤ k + (1-k) : add_le_add_left (min_le_right _ _) _
      ... = 1 : by ring,
    have xε : x ∈ ball k ε,
    { simp [dist, x, abs_of_nonneg (le_of_lt (half_pos δpos))],
      exact lt_of_lt_of_le (half_lt_self δpos) (min_le_left _ _) },
    have xI : x ∈ Icc (0:ℝ) 1 :=
      ⟨le_of_lt (lt_of_le_of_lt (k_mem_K.1.1) k_lt_x), le_of_lt x_lt_1⟩,
    have Ih : ∥h x∥ ≤ (D - C) * ∥x - k∥ :=
      hs ⟨hε xε, xI⟩,
    have I : ∥f x - f k∥ ≤ D * (x-k) := calc
      ∥f x - f k∥ = ∥g (x-k) + h x∥ : by { congr' 1, simp only [h], abel }
      ... ≤ ∥g (x-k)∥ + ∥h x∥ : norm_triangle _ _
      ... ≤ ∥g∥ * ∥x-k∥ + (D-C) * ∥x-k∥ : add_le_add (g.le_op_norm _) Ih
      ... ≤ C * ∥x-k∥ + (D-C) * ∥x-k∥ :
        add_le_add_right (mul_le_mul_of_nonneg_right (bound k k_mem_K.1) (norm_nonneg _)) _
      ... = D * ∥x-k∥ : by ring
      ... = D * (x-k) : by simp [norm, abs_of_nonneg (le_of_lt (half_pos δpos))],
    have : ∥f x - f 0∥ ≤ D * x := calc
      ∥f x - f 0∥ = ∥(f x - f k) + (f k - f 0)∥ : by { congr' 1, abel }
      ... ≤ ∥f x - f k∥ + ∥f k - f 0∥ : norm_triangle _ _
      ... ≤ D * (x - k) + D * k : add_le_add I (k_mem_K.2)
      ... = D * x : by ring,
    have xK : x ∈ K := ⟨xI, this⟩,
    have : x ≤ k := le_cSup ⟨1, λy hy, hy.1.2⟩ xK,
    exact (not_le_of_lt k_lt_x) this },
  rw this at k_mem_K,
  simpa [this] using k_mem_K.2
end

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by C, then
the function is C-Lipschitz -/
theorem norm_image_sub_le_of_norm_deriv_le_convex {f : E → F} {C : ℝ} {s : set E} {x y : E}
  (hf : differentiable_on ℝ f s) (bound : ∀x∈s, ∥fderiv_within ℝ f s x∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
begin
  /- By composition with t ↦ x + t • (y-x), we reduce to a statement for functions defined
  on [0,1], for which it is proved in norm_image_sub_le_of_norm_deriv_le_segment.
  We just have to check the differentiability of the composition and bounds on its derivative,
  which is straightforward but tedious for lack of automation. -/
  have C0 : 0 ≤ C := le_trans (norm_nonneg _) (bound x xs),
  let g := λ(t:ℝ), f (x + t • (y-x)),
  have D1 : differentiable ℝ (λt:ℝ, x + t • (y-x)) :=
    differentiable.add (differentiable_const _)
      (differentiable.smul' differentiable_id (differentiable_const _)),
  have segm : (λ (t : ℝ), x + t • (y - x)) '' Icc 0 1 ⊆ s,
    by { rw image_Icc_zero_one_eq_segment, apply (convex_segment_iff _).1 hs x y xs ys },
  have : f x = g 0, by { simp only [g], rw [zero_smul, add_zero] },
  rw this,
  have : f y = g 1, by { simp only [g], rw one_smul, congr' 1, abel },
  rw this,
  apply norm_image_sub_le_of_norm_deriv_le_segment (hf.comp D1.differentiable_on segm) (λt ht, _),
  /- It remains to check that the derivative of g is bounded by C ∥y-x∥ at any t ∈ [0,1] -/
  have t_s : x + t • (y-x) ∈ s := segm (mem_image_of_mem _ ht),
  simp only [g],
  /- Expand the derivative of the composition, and bound its norm by the product of the norms -/
  rw fderiv_within.comp t (hf _ t_s) ((D1 t).differentiable_within_at) segm
    (unique_diff_on_Icc_zero_one t ht),
  refine le_trans (op_norm_comp_le _ _) (mul_le_mul (bound _ t_s) _ (norm_nonneg _) C0),
  have : fderiv_within ℝ (λ (t : ℝ), x + t • (y - x)) (Icc 0 1) t =
      (id : ℝ →L[ℝ] ℝ).scalar_prod_space_iso (y - x) := calc
    fderiv_within ℝ (λ (t : ℝ), x + t • (y - x)) (Icc 0 1) t
    = fderiv ℝ (λ (t : ℝ), x + t • (y - x)) t :
      differentiable.fderiv_within (D1 t) (unique_diff_on_Icc_zero_one t ht)
    ... = fderiv ℝ (λ (t : ℝ), x) t + fderiv ℝ (λ (t : ℝ), t • (y-x)) t :
      fderiv_add (differentiable_at_const _) ((differentiable.smul' differentiable_id (differentiable_const _)) t)
    ... = fderiv ℝ (λ (t : ℝ), t • (y-x)) t :
      by rw [fderiv_const, zero_add]
    ... = t • fderiv ℝ (λ (t : ℝ), (y-x)) t + (fderiv ℝ id t).scalar_prod_space_iso (y - x) :
      fderiv_smul' differentiable_at_id (differentiable_at_const _)
    ... = (id : ℝ →L[ℝ] ℝ).scalar_prod_space_iso (y - x) :
      by rw [fderiv_const, smul_zero, zero_add, fderiv_id],
  rw [this, scalar_prod_space_iso_norm],
  calc ∥(id : ℝ →L[ℝ] ℝ)∥ * ∥y - x∥ ≤ 1 * ∥y-x∥ :
    mul_le_mul_of_nonneg_right norm_id (norm_nonneg _)
  ... = ∥y - x∥ : one_mul _
end
