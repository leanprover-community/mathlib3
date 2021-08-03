/-
Copyright (c) 2021 François Sunatori. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François Sunatori
-/
import analysis.complex.circle
import analysis.normed_space.conformal_linear_map

/-!
# Isometries of the Complex Plane

The lemma `linear_isometry_complex` states the classification of isometries in the complex plane.
Specifically, isometries with rotations but without translation.
The proof involves:
1. creating a linear isometry `g` with two fixed points, `g(0) = 0`, `g(1) = 1`
2. applying `linear_isometry_complex_aux` to `g`
The proof of `linear_isometry_complex_aux` is separated in the following parts:
1. show that the real parts match up: `linear_isometry.re_apply_eq_re`
2. show that I maps to either I or -I
3. every z is a linear combination of a + b * I

## References

* [Isometries of the Complex Plane](http://helmut.knaust.info/mediawiki/images/b/b5/Iso.pdf)
-/
noncomputable theory

open complex

local notation `|` x `|` := complex.abs x

/-- An element of the unit circle defines a `linear_isometry_equiv` from `ℂ` to itself, by
rotation. This is an auxiliary construction; use `rotation`, which has more structure, by
preference. -/
def rotation_aux (a : circle) : ℂ ≃ₗᵢ[ℝ] ℂ :=
{ to_fun := λ z, a * z,
  map_add' := mul_add ↑a,
  map_smul' := λ t z, by { simp only [smul_coe], ring },
  inv_fun := λ z, a⁻¹ * z,
  left_inv := λ z, by { field_simp [nonzero_of_mem_circle], ring },
  right_inv := λ z, by { field_simp [nonzero_of_mem_circle], ring },
  norm_map' := by simp }

/-- An element of the unit circle defines a `linear_isometry_equiv` from `ℂ` to itself, by
rotation. -/
def rotation : circle →* (ℂ ≃ₗᵢ[ℝ] ℂ) :=
{ to_fun := rotation_aux,
  map_one' := by { ext1, simp [rotation_aux] },
  map_mul' := λ a b, by { ext1, simp [rotation_aux] } }

@[simp] lemma rotation_apply (a : circle) (z : ℂ) : rotation a z = a * z := rfl

lemma linear_isometry.re_apply_eq_re_of_add_conj_eq (f : ℂ →ₗᵢ[ℝ] ℂ)
  (h₃ : ∀ z, z + conj z = f z + conj (f z)) (z : ℂ) : (f z).re = z.re :=
by simpa [ext_iff, add_re, add_im, conj_re, conj_im, ←two_mul,
         (show (2 : ℝ) ≠ 0, by simp [two_ne_zero'])] using (h₃ z).symm

lemma linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ}
  (h₂ : ∀ z, (f z).re = z.re) (z : ℂ) :
  (f z).im = z.im ∨ (f z).im = -z.im :=
begin
  have h₁ := f.norm_map z,
  simp only [complex.abs, norm_eq_abs] at h₁,
  rwa [real.sqrt_inj (norm_sq_nonneg _) (norm_sq_nonneg _), norm_sq_apply (f z), norm_sq_apply z,
    h₂, add_left_cancel_iff, mul_self_eq_mul_self_iff] at h₁,
end

lemma linear_isometry.im_apply_eq_im {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) :
  z + conj z = f z + conj (f z) :=
begin
  have : ∥f z - 1∥ = ∥z - 1∥ := by rw [← f.norm_map (z - 1), f.map_sub, h],
  apply_fun λ x, x ^ 2 at this,
  simp only [norm_eq_abs, ←norm_sq_eq_abs] at this,
  rw [←of_real_inj, ←mul_conj, ←mul_conj] at this,
  rw [conj.map_sub, conj.map_sub] at this,
  simp only [sub_mul, mul_sub, one_mul, mul_one] at this,
  rw [mul_conj, norm_sq_eq_abs, ←norm_eq_abs, linear_isometry.norm_map] at this,
  rw [mul_conj, norm_sq_eq_abs, ←norm_eq_abs] at this,
  simp only [sub_sub, sub_right_inj, mul_one, of_real_pow, ring_hom.map_one, norm_eq_abs] at this,
  simp only [add_sub, sub_left_inj] at this,
  rw [add_comm, ←this, add_comm],
end

lemma linear_isometry.re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) : (f z).re = z.re :=
begin
  apply linear_isometry.re_apply_eq_re_of_add_conj_eq,
  intro z,
  apply linear_isometry.im_apply_eq_im h,
end

lemma linear_isometry_complex_aux {f : ℂ ≃ₗᵢ[ℝ] ℂ} (h : f 1 = 1) :
  f = linear_isometry_equiv.refl ℝ ℂ ∨ f = conj_lie :=
begin
  have h0 : f I = I ∨ f I = -I,
  { have : |f I| = 1 := by simpa using f.norm_map complex.I,
    simp only [ext_iff, ←and_or_distrib_left, neg_re, I_re, neg_im, neg_zero],
    split,
    { rw ←I_re,
      exact @linear_isometry.re_apply_eq_re f.to_linear_isometry h I, },
    { apply @linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re f.to_linear_isometry,
      intro z, rw @linear_isometry.re_apply_eq_re f.to_linear_isometry h } },
  refine h0.imp (λ h' : f I = I, _) (λ h' : f I = -I, _);
  { apply linear_isometry_equiv.to_linear_equiv_injective,
    apply complex.basis_one_I.ext',
    intros i,
    fin_cases i; simp [h, h'] }
end

lemma linear_isometry_complex (f : ℂ ≃ₗᵢ[ℝ] ℂ) :
  ∃ a : circle, f = rotation a ∨ f = conj_lie.trans (rotation a) :=
begin
  let a : circle := ⟨f 1, by simpa using f.norm_map 1⟩,
  use a,
  have : (f.trans (rotation a).symm) 1 = 1,
  { simpa using rotation_apply a⁻¹ (f 1) },
  refine (linear_isometry_complex_aux this).imp (λ h₁, _) (λ h₂, _),
  { simpa using eq_mul_of_inv_mul_eq h₁ },
  { exact eq_mul_of_inv_mul_eq h₂ }
end

section conformal_into_complex_normed

variables {E : Type*} [normed_group E] [normed_space ℝ E] [normed_space ℂ E]
  [is_scalar_tower ℝ ℂ E] {z : ℂ} {g : ℂ →L[ℝ] E} {f : ℂ → E}

lemma is_conformal_map_complex_linear
  {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) : is_conformal_map (map.restrict_scalars ℝ) :=
begin
  have minor₀ : ∀ (x : ℂ), x = x • 1 := λ x, by rw [smul_eq_mul, mul_one],
  have minor₁ : ∥map 1∥ ≠ 0,
  { contrapose! nonzero with w,
    ext1,
    rw [continuous_linear_map.zero_apply],
    exact norm_eq_zero.mp w, },
  refine ⟨∥map 1∥, minor₁, _⟩,
  let li' := ∥map 1∥⁻¹ • map,
  have key : ∀ (x : ℂ), ∥li' x∥ = ∥x∥,
  { intros x,
    simp only [li', continuous_linear_map.smul_apply],
    nth_rewrite 0 [minor₀ x],
    simp only [map.map_smul, norm_smul, normed_field.norm_inv, norm_norm],
    field_simp [minor₁], },
  let li : ℂ →ₗᵢ[ℝ] E := ⟨li', key⟩,
  have minor₂ : (li : ℂ → E) = li' := rfl,
  refine ⟨li, _⟩,
  ext1,
  simp only [minor₂, li', pi.smul_apply, continuous_linear_map.smul_apply, smul_smul],
  field_simp [minor₁],
end

lemma is_conformal_map_conj : is_conformal_map conj_cle.to_continuous_linear_map :=
⟨1, one_ne_zero, conj_lie.to_linear_isometry, by rw one_smul; refl⟩

lemma is_conformal_map_complex_linear_conj
  {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) :
  is_conformal_map ((map.restrict_scalars ℝ).comp conj_cle.to_continuous_linear_map) :=
is_conformal_map_conj.comp (is_conformal_map_complex_linear nonzero)

end conformal_into_complex_normed

section conformal_into_complex_plane

variables {f : ℂ → ℂ} {z : ℂ} {g : ℂ →L[ℝ] ℂ}

lemma is_complex_or_conj_complex_linear (h : is_conformal_map g) :
  (∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g) ∨
  (∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g.comp conj_cle.to_continuous_linear_map) :=
begin
  rcases h with ⟨c, hc, li, hg⟩,
  rcases linear_isometry_complex (li.to_linear_isometry_equiv rfl) with ⟨a, ha⟩,
  let rot := c • (a : ℂ) • continuous_linear_map.id ℂ ℂ,
  cases ha,
  { refine or.intro_left _ ⟨rot, _⟩,
    ext1,
    simp only [coe_restrict_scalars', hg, ← li.coe_to_linear_isometry_equiv, ha,
               pi.smul_apply, continuous_linear_map.smul_apply, rotation_apply,
               continuous_linear_map.id_apply, smul_eq_mul], },
  { refine or.intro_right _ ⟨rot, _⟩,
    ext1,
    rw [continuous_linear_map.coe_comp', hg, ← li.coe_to_linear_isometry_equiv, ha],
    simp only [coe_restrict_scalars', function.comp_app, pi.smul_apply,
               linear_isometry_equiv.coe_trans, conj_lie_apply,
               rotation_apply, continuous_linear_equiv.coe_def_rev,
               continuous_linear_equiv.coe_apply, conj_cle_apply],
    simp only [continuous_linear_map.smul_apply, continuous_linear_map.id_apply,
               smul_eq_mul, conj_conj], },
end

/-- A real continuous linear map on the complex plane is conformal if and only if the map or its
    conjugate is complex linear, and the map is nonvanishing. -/
lemma is_complex_or_conj_complex_linear_iff_is_conformal_map :
  ((∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g) ∨
   (∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g.comp conj_cle.to_continuous_linear_map))
  ∧ g ≠ 0 ↔ is_conformal_map g :=
begin
  split,
  { rintros ⟨h₁, h₂⟩,
    cases h₁,
    { rcases h₁ with ⟨map, hmap⟩,
      rw ← hmap,
      refine is_conformal_map_complex_linear _,
      contrapose! h₂ with w,
      ext1,
      simp only [← hmap, coe_restrict_scalars', w, continuous_linear_map.zero_apply], },
    { rcases h₁ with ⟨map, hmap⟩,
      have minor₁ : g = (map.restrict_scalars ℝ).comp conj_cle.to_continuous_linear_map,
      { ext1,
        rw hmap,
        simp only [coe_comp', function.comp_app, conj_cle.coe_def_rev, conj_cle.coe_coe,
                  conj_cle_apply, conj_conj], },
      rw minor₁,
      refine is_conformal_map_complex_linear_conj _,
      contrapose! h₂ with w,
      ext1,
      simp only [minor₁, coe_comp', coe_restrict_scalars', w,
                 function.comp_app, continuous_linear_map.zero_apply], }, },
  { exact λ h, ⟨is_complex_or_conj_complex_linear h, h.ne_zero⟩, },
end

end conformal_into_complex_plane
