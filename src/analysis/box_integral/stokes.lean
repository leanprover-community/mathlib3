/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.basic
import analysis.box_integral.partition.additive
import analysis.calculus.fderiv

/-!
# Divergence integral for Henstock-Kurzweil integral

In this file we prove the Divergence Theorem for a Henstock-Kurzweil style integral. The theorem
says that the following. Let `f : ℝⁿ → Eⁿ` be a function differentiable on a closed rectangular box
`I` with derivative `f' x : ℝⁿ →L[ℝ] Eⁿ` at `x ∈ I`. Then the divergence `λ x, ∑ k, f' x eₖ k`,
where `eₖ = pi.single k 1` is the `k`-th basis vector, is integrable on `I`, and its integral is
equal to the sum of integrals of `f` over the faces of `I` taken with appropriate signs.

To make the proof work, we had to ban tagged partitions with “long and thin” boxes. More precisely,
we use the following generalization of one-dimensional Henstock-Kurzweil integral to functions
defined on a box in `ℝⁿ` (it corresponds to the value `⊥` of `box_integral.integration_filter` in
the definition of `box_integral.has_integral`).

We say that `f : ℝⁿ → E` has integral `y : E` over a box `I ⊆ ℝⁿ` if for an arbitrarily small
positive `ε` and an arbitrarily large `c`, there exists a function `r : ℝⁿ → (0, ∞)` such that for
any tagged partition `π` of `I` such that

* `π` is a Henstock partition, i.e., each tag belongs to its box;
* `π` is subordinate to `r`;
* for every box of `π`, the maximum of the ratios of its sides is less than or equal to `c`,

the integral sum of `f` over `π` is `ε`-close to `y`. In case of dimension one, the last condition
trivially holds for any `c ≥ 1`, so this definition is equivalent to the standard definition of
Henstock-Kurzweil integral.

## Tags

Henstock-Kurzweil integral, integral, Stokes theorem, divergence theorem
-/

open_locale classical big_operators nnreal ennreal topological_space
open continuous_linear_map (lsmul) filter set finset metric
noncomputable theory

universes u
variables {E : Type u} [normed_group E] [normed_space ℝ E] {n : ℕ}

namespace box_integral

local notation `ℝⁿ` := fin n → ℝ
local notation `ℝⁿ⁺¹` := fin (n + 1) → ℝ
local notation `Eⁿ⁺¹` := fin (n + 1) → E

variables [complete_space E] (I : box (fin (n + 1))) {i : fin (n + 1)}

open measure_theory

/-- Auxiliary lemma for the divergence theorem. -/
lemma norm_volume_sub_integral_face_upper_sub_lower_smul_le
  {f : ℝⁿ⁺¹ → E} {f' : ℝⁿ⁺¹ →L[ℝ] E} (hfc : continuous_on f I.Icc)
  {x : ℝⁿ⁺¹} (hxI : x ∈ I.Icc) {a : E} {ε : ℝ} (h0 : 0 < ε)
  (hε : ∀ y ∈ I.Icc, ∥f y - a - f' (y - x)∥ ≤ ε * ∥y - x∥) {c : ℝ≥0} (hc : I.distortion ≤ c) :
  ∥(∏ j, (I.upper j - I.lower j)) • f' (pi.single i 1) -
    (integral (I.face i) ⊥ (f ∘ i.insert_nth (I.upper i)) box_additive_map.volume -
      integral (I.face i) ⊥ (f ∘ i.insert_nth (I.lower i)) box_additive_map.volume)∥ ≤
    2 * ε * c * ∏ j, (I.upper j - I.lower j) :=
begin
  have Hl : I.lower i ∈ Icc (I.lower i) (I.upper i), from left_mem_Icc.2 (I.lower_le_upper i),
  have Hu : I.upper i ∈ Icc (I.lower i) (I.upper i), from right_mem_Icc.2 (I.lower_le_upper i),
  have Hi : ∀ x ∈ Icc (I.lower i) (I.upper i),
    integrable.{0 u u} (I.face i) ⊥ (f ∘ i.insert_nth x) box_additive_map.volume,
    from λ x hx, integrable_of_continuous_on _ (box.continuous_on_face_Icc hfc hx) volume,
  rw [← integral_sub (Hi _ Hu) (Hi _ Hl), ← box.volume_face_mul i, mul_smul, ← box.volume_apply,
    ← box_additive_map.to_smul_apply, ← integral_const, ← box_additive_map.volume,
    ← integral_sub (integrable_const _) ((Hi _ Hu).sub (Hi _ Hl))],
  simp only [(∘), pi.sub_def, ← f'.map_smul, ← pi.single_smul', smul_eq_mul, mul_one],
  have : ∀ y ∈ (I.face i).Icc, ∥f' (pi.single i (I.upper i - I.lower i)) -
    (f (i.insert_nth (I.upper i) y) - f (i.insert_nth (I.lower i) y))∥ ≤ 2 * ε * diam I.Icc,
  { intros y hy,
    set g := λ y, f y - a - f' (y - x) with hg,
    change ∀ y ∈ I.Icc, ∥g y∥ ≤ ε * ∥y - x∥ at hε,
    clear_value g, obtain rfl : f = λ y, a + f' (y - x) + g y, by simp [hg],
    convert_to ∥g (i.insert_nth (I.lower i) y) - g (i.insert_nth (I.upper i) y)∥ ≤ _,
    { congr' 1,
      have := fin.insert_nth_sub_same i (I.upper i) (I.lower i) y,
      simp only [← this, f'.map_sub], abel },
    { have : ∀ z ∈ Icc (I.lower i) (I.upper i), i.insert_nth z y ∈ I.Icc,
        from λ z hz, I.maps_to_insert_nth_face_Icc hz hy,
      replace hε : ∀ y ∈ I.Icc, ∥g y∥ ≤ ε * diam I.Icc,
      { intros y hy,
        refine (hε y hy).trans (mul_le_mul_of_nonneg_left _ h0.le),
        rw ← dist_eq_norm,
        exact dist_le_diam_of_mem (is_compact_pi_Icc I.lower I.upper).bounded hy hxI },
      rw [two_mul, add_mul],
      exact norm_sub_le_of_le (hε _ (this _ Hl)) (hε _ (this _ Hu)) } },
  refine (norm_integral_le_of_le_const this volume).trans _,
  rw [mul_left_comm (volume _).to_real, mul_assoc (2 * ε), mul_left_comm (c : ℝ)],
  refine mul_le_mul_of_nonneg_left _ (mul_nonneg zero_le_two h0.le),
  refine mul_le_mul_of_nonneg_left _ ennreal.to_real_nonneg,
  exact (I.diam_Icc_le_distortion_mul i).trans
    (mul_le_mul_of_nonneg_right hc $ sub_nonneg.2 $ I.lower_le_upper i)
end

lemma has_integral_bot_pderiv (f : ℝⁿ⁺¹ → E) (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] E) (s : set ℝⁿ⁺¹)
  (hs : countable s) (Hs : ∀ x ∈ s, continuous_within_at f I.Icc x)
  (Hd : ∀ x ∈ I.Icc \ s, has_fderiv_within_at f (f' x) I.Icc x) (i : fin (n + 1)) :
  has_integral.{0 u u} I ⊥ (λ x, f' x (pi.single i 1)) box_additive_map.volume
    (integral.{0 u u} (I.face i) ⊥ (λ x, f (i.insert_nth (I.upper i) x)) box_additive_map.volume -
      integral.{0 u u} (I.face i) ⊥ (λ x, f (i.insert_nth (I.lower i) x))
        box_additive_map.volume) :=
begin
  have Hc : continuous_on f I.Icc,
  { intros x hx,
    by_cases hxs : x ∈ s,
    exacts [Hs x hxs, (Hd x ⟨hx, hxs⟩).continuous_within_at] },
  set fI : ℝ → box (fin n) → E := λ y J,
    integral.{0 u u} J ⊥ (λ x, f (i.insert_nth y x)) box_additive_map.volume,
  set fb : Icc (I.lower i) (I.upper i) → fin n →ᵇᵃ[↑(I.face i)] E :=
    λ x, (integrable_of_continuous_on ⊥ (box.continuous_on_face_Icc Hc x.2) volume).to_box_additive,
  set F : fin (n + 1) →ᵇᵃ[I] E := box_additive_map.upper_sub_lower I i fI fb (λ x hx J, rfl),
  change has_integral I ⊥ (λ x, f' x (pi.single i 1)) _ (F I),
  refine has_integral_of_le_Henstock_of_forall_is_o bot_le _ _ _ s hs _ _,
  { exact (volume : measure ℝⁿ⁺¹).to_box_additive.restrict _ le_top },
  { exact λ J, ennreal.to_real_nonneg },
  { intros c x hx ε ε0,
    have : ∀ᶠ δ in 𝓝[Ioi 0] (0 : ℝ), δ ∈ Ioc (0 : ℝ) (1 / 2) ∧
      (∀ y₁ y₂ ∈ closed_ball x δ ∩ I.Icc, ∥f y₁ - f y₂∥ ≤ ε / 2) ∧
      ((2 * δ) ^ (n + 1) * ∥f' x (pi.single i 1)∥ ≤ ε / 2),
    { refine eventually.and _ (eventually.and _ _),
      { exact Ioc_mem_nhds_within_Ioi ⟨le_rfl, one_half_pos⟩ },
      { rcases ((nhds_within_has_basis nhds_basis_closed_ball _).tendsto_iff
          nhds_basis_closed_ball).1 (Hs x hx.2) _ (half_pos $ half_pos ε0) with ⟨δ₁, δ₁0, hδ₁⟩,
        filter_upwards [Ioc_mem_nhds_within_Ioi ⟨le_rfl, δ₁0⟩],
        rintro δ hδ y₁ y₂ hy₁ hy₂,
        have : closed_ball x δ ∩ I.Icc ⊆ closed_ball x δ₁ ∩ I.Icc,
          from inter_subset_inter_left _ (closed_ball_subset_closed_ball hδ.2),
        rw ← dist_eq_norm,
        calc dist (f y₁) (f y₂) ≤ dist (f y₁) (f x) + dist (f y₂) (f x) : dist_triangle_right _ _ _
        ... ≤ ε / 2 / 2 + ε / 2 / 2 : add_le_add (hδ₁ _ $ this hy₁) (hδ₁ _ $ this hy₂)
        ... = ε / 2 : add_halves _ },
      { have : continuous_within_at (λ δ, (2 * δ) ^ (n + 1) * ∥f' x (pi.single i 1)∥)
          (Ioi (0 : ℝ)) 0 := ((continuous_within_at_id.const_mul _).pow _).mul_const _,
        refine this.eventually (ge_mem_nhds _),
        simpa using half_pos ε0 } },
    rcases this.exists with ⟨δ, ⟨hδ0, hδ12⟩, hdfδ, hδ⟩,
    refine ⟨δ, hδ0, λ J hJI hJδ hxJ hJc, add_halves ε ▸ _⟩,
    have Hl : J.lower i ∈ Icc (J.lower i) (J.upper i), from left_mem_Icc.2 (J.lower_le_upper i),
    have Hu : J.upper i ∈ Icc (J.lower i) (J.upper i), from right_mem_Icc.2 (J.lower_le_upper i),
    have Hi : ∀ x ∈ Icc (J.lower i) (J.upper i),
      integrable.{0 u u} (J.face i) ⊥ (λ y, f (i.insert_nth x y)) box_additive_map.volume,
      from λ x hx, integrable_of_continuous_on _
        (box.continuous_on_face_Icc (Hc.mono $ box.le_iff_Icc.1 hJI) hx) volume,
    have hJδ' : J.Icc ⊆ closed_ball x δ ∩ I.Icc,
      from subset_inter hJδ (box.le_iff_Icc.1 hJI),
    have Hmaps : ∀ z ∈ Icc (J.lower i) (J.upper i),
      maps_to (i.insert_nth z) (J.face i).Icc (closed_ball x δ ∩ I.Icc),
      from λ z hz, (J.maps_to_insert_nth_face_Icc hz).mono subset.rfl hJδ',
    simp only [dist_eq_norm, F, fI], dsimp,
    rw [← integral_sub (Hi _ Hu) (Hi _ Hl)],
    refine (norm_sub_le _ _).trans (add_le_add _ _),
    { simp_rw [box_additive_map.volume_apply, norm_smul, real.norm_eq_abs, abs_prod],
      refine (mul_le_mul_of_nonneg_right _ $ norm_nonneg _).trans hδ,
      have : ∀ j, |J.upper j - J.lower j| ≤ 2 * δ,
      { intro j,
        calc dist (J.upper j) (J.lower j) ≤ dist J.upper J.lower : dist_le_pi_dist _ _ _
        ... ≤ dist J.upper x + dist J.lower x : dist_triangle_right _ _ _
        ... ≤ δ + δ : add_le_add (hJδ J.upper_mem_Icc) (hJδ J.lower_mem_Icc)
        ... = 2 * δ : (two_mul δ).symm },
      calc (∏ j, |J.upper j - J.lower j|) ≤ ∏ j : fin (n + 1), (2 * δ) :
        prod_le_prod (λ _ _ , abs_nonneg _) (λ j hj, this j)
      ... = (2 * δ) ^ (n + 1) : by simp },
    { refine (norm_integral_le_of_le_const (λ y hy,
        hdfδ _ _ (Hmaps _ Hu hy) (Hmaps _ Hl hy)) _).trans _,
      refine (mul_le_mul_of_nonneg_right _ (half_pos ε0).le).trans_eq (one_mul _),
      rw [box.coe_eq_pi, real.volume_pi_Ioc_to_real (box.lower_le_upper _)],
      refine prod_le_one (λ _ _, sub_nonneg.2 $ box.lower_le_upper _ _) (λ j hj, _),
      calc J.upper (i.succ_above j) - J.lower (i.succ_above j)
          ≤ dist (J.upper (i.succ_above j)) (J.lower (i.succ_above j)) : le_abs_self _
      ... ≤ dist J.upper J.lower : dist_le_pi_dist J.upper J.lower (i.succ_above j)
      ... ≤ dist J.upper x + dist J.lower x : dist_triangle_right _ _ _
      ... ≤ δ + δ : add_le_add (hJδ J.upper_mem_Icc) (hJδ J.lower_mem_Icc)
      ... ≤ 1 / 2 + 1 / 2 : add_le_add hδ12 hδ12
      ... = 1 : add_halves 1 } },
  { intros c x hx ε ε0,
    rcases exists_pos_mul_lt ε0 (2 * c) with ⟨ε', ε'0, hlt⟩,
    rcases (nhds_within_has_basis nhds_basis_closed_ball _).mem_iff.1 ((Hd x hx).def ε'0)
      with ⟨δ, δ0, Hδ⟩,
    refine ⟨δ, δ0, λ J hle hJδ hxJ hJc, _⟩,
    simp only [box_additive_map.volume_apply, box.volume_apply, dist_eq_norm],
    refine (norm_volume_sub_integral_face_upper_sub_lower_smul_le _
      (Hc.mono $ box.le_iff_Icc.1 hle) hxJ ε'0 (λ y hy, Hδ _) (hJc rfl)).trans _,
    { exact ⟨hJδ hy, box.le_iff_Icc.1 hle hy⟩ },
    { rw [mul_right_comm (2 : ℝ), ← box.volume_apply],
      exact mul_le_mul_of_nonneg_right hlt.le ennreal.to_real_nonneg } }
end

/-- Divergence theorem for a Henstock-Kurzweil style integral.

If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is differentiable on a closed rectangular box `I` with derivative `f'`, then
the divergence `∑ i, f' x (pi.single i 1) i` is Henstock-Kurzweil integrable with integral equal to
the sum of integrals of `f` over the faces of `I` taken with appropriate signs.

More precisely, we use a non-standard generalization of the Henstock-Kurzweil integral and
we allow `f` to be non-differentiable (but still continuous) at a countable set of points. -/
lemma has_integral_bot_divergence_of_forall_has_deriv_within_at
  (f : ℝⁿ⁺¹ → Eⁿ⁺¹) (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (s : set ℝⁿ⁺¹) (hs : countable s)
  (Hs : ∀ x ∈ s, continuous_within_at f I.Icc x)
  (Hd : ∀ x ∈ I.Icc \ s, has_fderiv_within_at f (f' x) I.Icc x) :
  has_integral.{0 u u} I ⊥ (λ x, ∑ i, f' x (pi.single i 1) i)
    box_additive_map.volume
    (∑ i, (integral.{0 u u} (I.face i) ⊥ (λ x, f (i.insert_nth (I.upper i) x) i)
      box_additive_map.volume -
      integral.{0 u u} (I.face i) ⊥ (λ x, f (i.insert_nth (I.lower i) x) i)
        box_additive_map.volume)) :=
begin
  refine has_integral_sum (λ i hi, _), clear hi,
  simp only [has_fderiv_within_at_pi', continuous_within_at_pi] at Hd Hs,
  convert has_integral_bot_pderiv I _ _ s hs (λ x hx, Hs x hx i) (λ x hx, Hd x hx i) i
end

end box_integral
