/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import topology.algebra.continuous_affine_map
import analysis.normed_space.affine_isometry
import analysis.normed_space.operator_norm

/-!
# Continuous affine maps between normed spaces.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file develops the theory of continuous affine maps between affine spaces modelled on normed
spaces.

In the particular case that the affine spaces are just normed vector spaces `V`, `W`, we define a
norm on the space of continuous affine maps by defining the norm of `f : V →A[𝕜] W` to be
`‖f‖ = max ‖f 0‖ ‖f.cont_linear‖`. This is chosen so that we have a linear isometry:
`(V →A[𝕜] W) ≃ₗᵢ[𝕜] W × (V →L[𝕜] W)`.

The abstract picture is that for an affine space `P` modelled on a vector space `V`, together with
a vector space `W`, there is an exact sequence of `𝕜`-modules: `0 → C → A → L → 0` where `C`, `A`
are the spaces of constant and affine maps `P → W` and `L` is the space of linear maps `V → W`.

Any choice of a base point in `P` corresponds to a splitting of this sequence so in particular if we
take `P = V`, using `0 : V` as the base point provides a splitting, and we prove this is an
isometric decomposition.

On the other hand, choosing a base point breaks the affine invariance so the norm fails to be
submultiplicative: for a composition of maps, we have only `‖f.comp g‖ ≤ ‖f‖ * ‖g‖ + ‖f 0‖`.

## Main definitions:

 * `continuous_affine_map.cont_linear`
 * `continuous_affine_map.has_norm`
 * `continuous_affine_map.norm_comp_le`
 * `continuous_affine_map.to_const_prod_continuous_linear_map`

-/

namespace continuous_affine_map

variables {𝕜 R V W W₂ P Q Q₂ : Type*}
variables [normed_add_comm_group V] [metric_space P] [normed_add_torsor V P]
variables [normed_add_comm_group W] [metric_space Q] [normed_add_torsor W Q]
variables [normed_add_comm_group W₂] [metric_space Q₂] [normed_add_torsor W₂ Q₂]
variables [normed_field R] [normed_space R V] [normed_space R W] [normed_space R W₂]
variables [nontrivially_normed_field 𝕜] [normed_space 𝕜 V] [normed_space 𝕜 W] [normed_space 𝕜 W₂]

include V W

/-- The linear map underlying a continuous affine map is continuous. -/
def cont_linear (f : P →A[R] Q) : V →L[R] W :=
{ to_fun := f.linear,
  cont   := by { rw affine_map.continuous_linear_iff, exact f.cont, },
  .. f.linear, }

@[simp] lemma coe_cont_linear (f : P →A[R] Q) :
  (f.cont_linear : V → W) = f.linear :=
rfl

@[simp] lemma coe_cont_linear_eq_linear (f : P →A[R] Q) :
  (f.cont_linear : V →ₗ[R] W) = (f : P →ᵃ[R] Q).linear :=
by { ext, refl, }

@[simp] lemma coe_mk_const_linear_eq_linear (f : P →ᵃ[R] Q) (h) :
  ((⟨f, h⟩ : P →A[R] Q).cont_linear : V → W) = f.linear :=
rfl

lemma coe_linear_eq_coe_cont_linear (f : P →A[R] Q) :
  ((f : P →ᵃ[R] Q).linear : V → W) = (⇑f.cont_linear : V → W) :=
rfl

include W₂

@[simp] lemma comp_cont_linear (f : P →A[R] Q) (g : Q →A[R] Q₂) :
  (g.comp f).cont_linear = g.cont_linear.comp f.cont_linear :=
rfl

omit W₂

@[simp] lemma map_vadd (f : P →A[R] Q) (p : P) (v : V) :
  f (v +ᵥ p) = f.cont_linear v +ᵥ f p :=
f.map_vadd' p v

@[simp] lemma cont_linear_map_vsub (f : P →A[R] Q) (p₁ p₂ : P) :
  f.cont_linear (p₁ -ᵥ p₂) = f p₁ -ᵥ f p₂ :=
f.to_affine_map.linear_map_vsub p₁ p₂

@[simp] lemma const_cont_linear (q : Q) : (const R P q).cont_linear = 0 := rfl

lemma cont_linear_eq_zero_iff_exists_const (f : P →A[R] Q) :
  f.cont_linear = 0 ↔ ∃ q, f = const R P q :=
begin
  have h₁ : f.cont_linear = 0 ↔ (f : P →ᵃ[R] Q).linear = 0,
  { refine ⟨λ h, _, λ h, _⟩;
    ext,
    { rw [← coe_cont_linear_eq_linear, h], refl, },
    { rw [← coe_linear_eq_coe_cont_linear, h], refl, }, },
  have h₂ : ∀ (q : Q), f = const R P q ↔ (f : P →ᵃ[R] Q) = affine_map.const R P q,
  { intros q,
    refine ⟨λ h, _, λ h, _⟩;
    ext,
    { rw h, refl, },
    { rw [← coe_to_affine_map, h], refl, }, },
  simp_rw [h₁, h₂],
  exact (f : P →ᵃ[R] Q).linear_eq_zero_iff_exists_const,
end

@[simp] lemma to_affine_map_cont_linear (f : V →L[R] W) :
  f.to_continuous_affine_map.cont_linear = f :=
by { ext, refl, }

@[simp] lemma zero_cont_linear :
  (0 : P →A[R] W).cont_linear = 0 :=
rfl

@[simp] lemma add_cont_linear (f g : P →A[R] W) :
  (f + g).cont_linear = f.cont_linear + g.cont_linear :=
rfl

@[simp] lemma sub_cont_linear (f g : P →A[R] W) :
  (f - g).cont_linear = f.cont_linear - g.cont_linear :=
rfl

@[simp] lemma neg_cont_linear (f : P →A[R] W) :
  (-f).cont_linear = -f.cont_linear :=
rfl

@[simp] lemma smul_cont_linear (t : R) (f : P →A[R] W) :
  (t • f).cont_linear = t • f.cont_linear :=
rfl

lemma decomp (f : V →A[R] W) :
  (f : V → W) = f.cont_linear + function.const V (f 0) :=
begin
  rcases f with ⟨f, h⟩,
  rw [coe_mk_const_linear_eq_linear, coe_mk, f.decomp, pi.add_apply, linear_map.map_zero, zero_add],
end

section normed_space_structure

variables (f : V →A[𝕜] W)

/-- Note that unlike the operator norm for linear maps, this norm is _not_ submultiplicative:
we do _not_ necessarily have `‖f.comp g‖ ≤ ‖f‖ * ‖g‖`. See `norm_comp_le` for what we can say. -/
noncomputable instance has_norm : has_norm (V →A[𝕜] W) := ⟨λ f, max ‖f 0‖ ‖f.cont_linear‖⟩

lemma norm_def : ‖f‖ = (max ‖f 0‖ ‖f.cont_linear‖) := rfl

lemma norm_cont_linear_le : ‖f.cont_linear‖ ≤ ‖f‖ := le_max_right _ _

lemma norm_image_zero_le : ‖f 0‖ ≤ ‖f‖ := le_max_left _ _

@[simp] lemma norm_eq (h : f 0 = 0) : ‖f‖ = ‖f.cont_linear‖ :=
calc ‖f‖ = (max ‖f 0‖ ‖f.cont_linear‖) : by rw norm_def
    ... = (max 0 ‖f.cont_linear‖) : by rw [h, norm_zero]
    ... = ‖f.cont_linear‖ : max_eq_right (norm_nonneg _)

noncomputable instance : normed_add_comm_group (V →A[𝕜] W) :=
add_group_norm.to_normed_add_comm_group
{ to_fun := λ f, max ‖f 0‖ ‖f.cont_linear‖,
  map_zero' := by simp,
  neg' := λ f, by simp,
  add_le' := λ f g, begin
      simp only [pi.add_apply, add_cont_linear, coe_add, max_le_iff],
      exact ⟨(norm_add_le _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _)),
             (norm_add_le _ _).trans (add_le_add (le_max_right _ _) (le_max_right _ _))⟩,
    end,
  eq_zero_of_map_eq_zero' := λ f h₀, begin
      rcases max_eq_iff.mp h₀ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩;
      rw h₁ at h₂,
      { rw [norm_le_zero_iff, cont_linear_eq_zero_iff_exists_const] at h₂,
        obtain ⟨q, rfl⟩ := h₂,
        simp only [function.const_apply, coe_const, norm_eq_zero] at h₁,
        rw h₁,
        refl, },
      { rw [norm_eq_zero', cont_linear_eq_zero_iff_exists_const] at h₁,
        obtain ⟨q, rfl⟩ := h₁,
        simp only [function.const_apply, coe_const, norm_le_zero_iff] at h₂,
        rw h₂,
        refl, },
    end }

instance : normed_space 𝕜 (V →A[𝕜] W) :=
{ norm_smul_le := λ t f, by simp only [norm_def, smul_cont_linear, coe_smul, pi.smul_apply,
    norm_smul, ← mul_max_of_nonneg _ _ (norm_nonneg t)], }

lemma norm_comp_le (g : W₂ →A[𝕜] V) :
  ‖f.comp g‖ ≤ ‖f‖ * ‖g‖ + ‖f 0‖ :=
begin
  rw [norm_def, max_le_iff],
  split,
  { calc ‖f.comp g 0‖ = ‖f (g 0)‖ : by simp
                 ... = ‖f.cont_linear (g 0) + f 0‖ : by { rw f.decomp, simp, }
                 ... ≤ ‖f.cont_linear‖ * ‖g 0‖ + ‖f 0‖ :
                          (norm_add_le _ _).trans (add_le_add_right (f.cont_linear.le_op_norm _) _)
                 ... ≤ ‖f‖ * ‖g‖ + ‖f 0‖ :
                          add_le_add_right (mul_le_mul f.norm_cont_linear_le g.norm_image_zero_le
                          (norm_nonneg _) (norm_nonneg _)) _, },
  { calc ‖(f.comp g).cont_linear‖ ≤ ‖f.cont_linear‖ * ‖g.cont_linear‖ :
                                      (g.comp_cont_linear f).symm ▸ f.cont_linear.op_norm_comp_le _
                             ... ≤ ‖f‖ * ‖g‖ :
                                      mul_le_mul f.norm_cont_linear_le g.norm_cont_linear_le
                                      (norm_nonneg _) (norm_nonneg _)
                             ... ≤ ‖f‖ * ‖g‖ + ‖f 0‖ :
                                      by { rw le_add_iff_nonneg_right, apply norm_nonneg, }, },
end

variables (𝕜 V W)

/-- The space of affine maps between two normed spaces is linearly isometric to the product of the
codomain with the space of linear maps, by taking the value of the affine map at `(0 : V)` and the
linear part. -/
def to_const_prod_continuous_linear_map : (V →A[𝕜] W) ≃ₗᵢ[𝕜] W × (V →L[𝕜] W) :=
{ to_fun    := λ f, ⟨f 0, f.cont_linear⟩,
  inv_fun   := λ p, p.2.to_continuous_affine_map + const 𝕜 V p.1,
  left_inv  := λ f, by { ext, rw f.decomp, simp, },
  right_inv := by { rintros ⟨v, f⟩, ext; simp, },
  map_add'  := λ _ _, rfl,
  map_smul' := λ _ _, rfl,
  norm_map' := λ f, rfl }

@[simp] lemma to_const_prod_continuous_linear_map_fst (f : V →A[𝕜] W) :
  (to_const_prod_continuous_linear_map 𝕜 V W f).fst = f 0 :=
rfl

@[simp] lemma to_const_prod_continuous_linear_map_snd (f : V →A[𝕜] W) :
  (to_const_prod_continuous_linear_map 𝕜 V W f).snd = f.cont_linear :=
rfl

end normed_space_structure

end continuous_affine_map
