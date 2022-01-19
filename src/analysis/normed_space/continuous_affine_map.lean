/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import topology.algebra.continuous_affine_map
import analysis.normed_space.add_torsor
import analysis.normed_space.affine_isometry

/-!
# Continuous affine maps between normed spaces.

This file develops the theory of continuous affine maps between affine spaces modelled on normed
spaces.

-/

namespace continuous_affine_map

variables {R V W P Q : Type*}
variables [normed_field R]
variables [normed_group V] [normed_space R V] [metric_space P] [normed_add_torsor V P]
variables [normed_group W] [normed_space R W] [metric_space Q] [normed_add_torsor W Q]

include V W

/-- The linear map underlying a continuous affine map is continuous. -/
def cont_linear (f : P →A[R] Q) : V →L[R] W :=
{ to_fun := f.linear,
  cont   := by { rw affine_map.continuous_linear_iff, exact f.cont, },
  .. f.linear, }

@[simp] lemma coe_cont_linear_eq_linear (f : P →A[R] Q) :
  (f.cont_linear : V →ₗ[R] W) = (f : P →ᵃ[R] Q).linear :=
by { ext, refl, }

@[simp] lemma coe_mk_const_linear_eq_linear (f : P →ᵃ[R] Q) (h) :
  ((⟨f, h⟩ : P →A[R] Q).cont_linear : V → W) = f.linear :=
rfl

@[simp] lemma coe_linear_eq_coe_cont_linear (f : P →A[R] Q) :
  ((f : P →ᵃ[R] Q).linear : V → W) = (⇑f.cont_linear : V → W) :=
rfl

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

end continuous_affine_map
