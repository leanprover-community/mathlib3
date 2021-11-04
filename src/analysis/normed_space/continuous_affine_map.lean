/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import analysis.normed_space.affine_isometry
import topology.continuous_function.basic

/-!
# Continuous affine maps.

This file defines a type of bundled continuous affine maps.

## Main definitions:

 * `continuous_affine_map`

## Notation:

We introduce the notation `P →A[R] Q` for `continuous_affine_map R P Q`. Note that this is parallel
to the notation `E →L[R] F` for `continuous_linear_map R E F`.
-/

open_locale topological_space

/-- A continuous map of affine spaces. -/
structure continuous_affine_map (R : Type*) {V W : Type*} (P Q : Type*) [ring R]
  [add_comm_group V] [module R V] [metric_space P] [add_torsor V P]
  [add_comm_group W] [module R W] [metric_space Q] [add_torsor W Q]
  extends P →ᵃ[R] Q :=
(cont : continuous to_fun)

notation P ` →A[`:25 R `] ` Q := continuous_affine_map R P Q

namespace continuous_affine_map

variables {R V W P Q : Type*}
variables [normed_field R]
variables [normed_group V] [normed_space R V] [metric_space P] [normed_add_torsor V P]
variables [normed_group W] [normed_space R W] [metric_space Q] [normed_add_torsor W Q]

include V W

/-- see Note [function coercion] -/
instance : has_coe_to_fun (P →A[R] Q) (λ _, P → Q) := ⟨λ f, f.to_affine_map.to_fun⟩

lemma to_fun_eq_coe (f : P →A[R] Q) : f.to_fun = ⇑f := rfl

lemma coe_injective :
  @function.injective (P →A[R] Q) (P → Q) coe_fn :=
begin
  rintros ⟨⟨f, ⟨f', hf₁, hf₂⟩, hf₀⟩, hf₁⟩ ⟨⟨g, ⟨g', hg₁, hg₂⟩, hg₀⟩, hg₁⟩ h,
  have : f = g ∧ f' = g', { simpa only using affine_map.coe_fn_injective h, },
  congr,
  exacts [this.1, this.2],
end

@[ext] lemma ext {f g : P →A[R] Q} (h : ∀ x, f x = g x) : f = g :=
coe_injective $ funext h

lemma ext_iff {f g : P →A[R] Q} : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl, }, ext⟩

lemma congr_fun {f g : P →A[R] Q} (h : f = g) (x : P) : f x = g x := h ▸ rfl

instance : has_coe (P →A[R] Q) (P →ᵃ[R] Q) :=
⟨to_affine_map⟩

/-- Forgetting its algebraic properties, a continuous affine map is a continuous map. -/
def to_continuous_map (f : P →A[R] Q) : C(P, Q) :=
⟨f, f.cont⟩

instance : has_coe (P →A[R] Q) (C(P, Q)) :=
⟨to_continuous_map⟩

@[simp] lemma to_affine_map_eq_coe (f : P →A[R] Q) :
  f.to_affine_map = ↑f :=
rfl

@[simp] lemma to_continuous_map_coe (f : P →A[R] Q) : f.to_continuous_map = ↑f :=
rfl

@[simp, norm_cast] lemma coe_to_affine_map (f : P →A[R] Q) :
  ((f : P →ᵃ[R] Q) : P → Q) = f :=
rfl

@[simp, norm_cast] lemma coe_to_continuous_map (f : P →A[R] Q) :
  ((f : C(P, Q)) : P → Q) = f :=
rfl

lemma to_affine_map_injective {f g : P →A[R] Q}
  (h : (f : P →ᵃ[R] Q) = (g : P →ᵃ[R] Q)) : f = g :=
by { ext a, exact affine_map.congr_fun h a, }

lemma to_continuous_map_injective {f g : P →A[R] Q}
  (h : (f : C(P, Q)) = (g : C(P, Q))) : f = g :=
by { ext a, exact continuous_map.congr_fun h a, }

@[norm_cast] lemma coe_affine_map_mk (f : P →ᵃ[R] Q) (h) :
  ((⟨f, h⟩ : P →A[R] Q) : P →ᵃ[R] Q) = f :=
rfl

@[norm_cast] lemma coe_continuous_map_mk (f : P →ᵃ[R] Q) (h) :
  ((⟨f, h⟩ : P →A[R] Q) : C(P, Q)) = ⟨f, h⟩ :=
rfl

@[simp] lemma coe_mk (f : P →ᵃ[R] Q) (h) :
  ((⟨f, h⟩ : P →A[R] Q) : P → Q) = f :=
rfl

@[simp] lemma mk_coe (f : P →A[R] Q) (h) :
  (⟨(f : P →ᵃ[R] Q), h⟩ : P →A[R] Q) = f :=
by { ext, refl, }

@[continuity]
protected lemma continuous (f : P →A[R] Q) : continuous f := f.2

/-- The linear map underlying a continuous affine map is continuous. -/
def continuous_linear (f : P →A[R] Q) : V →L[R] W :=
{ to_fun := f.linear,
  cont   := by { rw affine_map.continuous_linear_iff, exact f.cont, },
  .. f.linear, }

@[simp] lemma coe_continuous_linear_eq_linear (f : P →A[R] Q) :
  (f.continuous_linear : V →ₗ[R] W) = (f : P →ᵃ[R] Q).linear :=
by { ext, refl, }

@[simp] lemma coe_linear_eq_coe_continuous_linear (f : P →A[R] Q) :
  ((f : P →ᵃ[R] Q).linear : V → W) = (⇑f.continuous_linear : V → W) :=
rfl

@[simp] lemma map_vadd (f : P →A[R] Q) (p : P) (v : V) :
  f (v +ᵥ p) = f.continuous_linear v +ᵥ f p :=
f.map_vadd' p v

@[simp] lemma linear_map_vsub (f : P →A[R] Q) (p₁ p₂ : P) :
  f.continuous_linear (p₁ -ᵥ p₂) = f p₁ -ᵥ f p₂ :=
f.to_affine_map.linear_map_vsub p₁ p₂

variables (R P)

/-- The constant map is a continuous affine map. -/
def const (q : Q) : P →A[R] Q :=
{ to_fun := affine_map.const R P q,
  cont   := continuous_const,
  .. affine_map.const R P q, }

@[simp] lemma coe_const (q : Q) : (const R P q : P → Q) = function.const P q := rfl

@[simp] lemma const_continuous_linear (q : Q) : (const R P q).continuous_linear = 0 := rfl

lemma continuous_linear_eq_zero_iff_exists_const (f : P →A[R] Q) :
  f.continuous_linear = 0 ↔ ∃ q, f = const R P q :=
begin
  have h₁ : f.continuous_linear = 0 ↔ (f : P →ᵃ[R] Q).linear = 0,
  { refine ⟨λ h, _, λ h, _⟩;
    ext,
    { rw [← coe_continuous_linear_eq_linear, h], refl, },
    { rw [← coe_linear_eq_coe_continuous_linear, h], refl, }, },
  have h₂ : ∀ (q : Q), f = const R P q ↔ (f : P →ᵃ[R] Q) = affine_map.const R P q,
  { intros q,
    refine ⟨λ h, _, λ h, _⟩;
    ext,
    { rw h, refl, },
    { rw [← coe_to_affine_map, h], refl, }, },
  simp_rw [h₁, h₂],
  exact (f : P →ᵃ[R] Q).linear_eq_zero_iff_exists_const,
end

noncomputable instance : inhabited (P →A[R] Q) :=
⟨const R P $ nonempty.some (by apply_instance : nonempty Q)⟩

variables {R P} {W₂ Q₂ : Type*}
variables [normed_group W₂] [normed_space R W₂] [metric_space Q₂] [normed_add_torsor W₂ Q₂]

include W₂

/-- The composition of morphisms is a morphism. -/
def comp (f : Q →A[R] Q₂) (g : P →A[R] Q) : P →A[R] Q₂ :=
{ cont := f.cont.comp g.cont,
  .. (f : Q →ᵃ[R] Q₂).comp (g : P →ᵃ[R] Q), }

@[simp, norm_cast] lemma coe_comp (f : Q →A[R] Q₂) (g : P →A[R] Q) :
  (f.comp g : P → Q₂) = (f : Q → Q₂) ∘ (g : P → Q) :=
rfl

lemma comp_apply (f : Q →A[R] Q₂) (g : P →A[R] Q) (x : P) :
  f.comp g x = f (g x) :=
rfl

end continuous_affine_map
