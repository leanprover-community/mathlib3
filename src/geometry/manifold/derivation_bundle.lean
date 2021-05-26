/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import geometry.manifold.algebra.smooth_functions
import ring_theory.derivation

/-!

# Derivation bundle

In this file we define the derivations at a point of a manifold on the algebra of smooth fuctions.
Moreover we define the total bundle of derivations (although at the moment it has not been given a
topology). Finally we define the differential of a function in terms of derivations.

The content of this file is not meant to be regarded as an alternative definition to the current
tangent bundle but rather as a purely algebraic theory that provides a purely algebraic definition
of the Lie algebra for a Lie group.

-/

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
(M : Type*) [topological_space M] [charted_space H M]

open_locale manifold

namespace point_derivation

instance smooth_functions_algebra : algebra 𝕜 C^∞⟮I, M; 𝕜⟯ := by apply_instance
instance smooth_functions_tower : is_scalar_tower 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ := by apply_instance

/-- The scalar multiplication depends on the point `x : M`. -/
def has_scalar (x : M) : has_scalar C^∞⟮I, M; 𝕜⟯ 𝕜 :=
{ smul := λ f k, f x * k }

lemma scalar_def {x : M} {f : C^∞⟮I, M; 𝕜⟯} {k : 𝕜} :
  @has_scalar.smul C^∞⟮I, M; 𝕜⟯ 𝕜 (has_scalar I M x) f k = f x * k := rfl

/-- The scalar multiplication defined above gives rise to a module structure. -/
def module (x : M) : module C^∞⟮I, M; 𝕜⟯ 𝕜 :=
{ one_smul := λ k, one_mul k,
  mul_smul := λ f g k, mul_assoc _ _ _,
  smul_add := λ f g k, mul_add _ _ _,
  smul_zero := λ f, mul_zero _,
  add_smul := λ f g k, add_mul _ _ _,
  zero_smul := λ f, zero_mul _,
  ..point_derivation.has_scalar I M x }

lemma is_scalar_tower (x : M) :
  @is_scalar_tower 𝕜 C^∞⟮I, M; 𝕜⟯ 𝕜 _ (has_scalar I M x) _ :=
{ smul_assoc := λ k f h, by { simp only [scalar_def, algebra.id.smul_eq_mul,
    smooth_map.coe_smul, pi.smul_apply, mul_assoc]} }

end point_derivation

/-- The derivations at a point of a manifold. Some regard this as a possible definition of the
tangent space -/
@[reducible] def point_derivation (x : M) :=
  @derivation 𝕜 C^∞⟮I, M; 𝕜⟯ _ _ _ 𝕜 _ (point_derivation.module I M x) _
    (point_derivation.is_scalar_tower I M x)

/-- The total bundle of point derivations. -/
def derivation_bundle := Σ x : M, point_derivation I M x

variables {I M}

/-- The inclusion map of derivations at a point into the total bundle. -/
def derivation_inclusion {x : M} (v : point_derivation I M x) : derivation_bundle I M :=
sigma.mk x v

instance [inhabited M] : inhabited (derivation_bundle I M) :=
⟨derivation_inclusion (0 : point_derivation I M (default M))⟩

section

/- Why do I need to rewrite extensionality rules for reducible defs? -/
namespace point_derivation

variables {I} {M} {x y : M} {v w : point_derivation I M x} (f g : C^∞⟮I, M; 𝕜⟯) (r : 𝕜)

lemma coe_injective (h : ⇑v = w) : v = w :=
@derivation.coe_injective 𝕜 _ C^∞⟮I, M; 𝕜⟯ _ _ 𝕜 _ (point_derivation.module I M x) _
  (point_derivation.is_scalar_tower I M x) v w h

@[ext] theorem ext (h : ∀ f, v f = w f) : v = w :=
coe_injective $ funext h

theorem hext {u : point_derivation I M y} (h1 : x = y) (h2 : ∀ f, v f = u f) : v == u :=
by { cases h1, rw heq_iff_eq, ext, exact h2 f }

end point_derivation

end

section

variables {I} {M} (X Y : derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯)
  (f g : C^∞⟮I, M; 𝕜⟯) (r : 𝕜)

namespace derivation

/-- Evaluation of a global derivation at a point, giving a point derivation in the most natural
possible way. -/
def eval_map (x : M) : point_derivation I M x :=
{ to_fun := λ f, (X f) x,
  map_add' := λ f g, by { rw derivation.map_add, refl },
  map_smul' := λ f g, by { rw [derivation.map_smul, algebra.id.smul_eq_mul], refl },
  leibniz' := λ h k, by { dsimp only [], rw [derivation.leibniz, algebra.id.smul_eq_mul], refl } }

/-- The evaluation is a linear map. -/
def eval_at (x : M) : (derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^⊤⟮I, M; 𝕜⟯) →ₗ[𝕜] point_derivation I M x :=
{ to_fun := λ X, X.eval_map x,
  map_add' := λ X Y, rfl,
  map_smul' := λ k X, rfl }

lemma eval_apply (x : M) : eval_at x X f = (X f) x := rfl

end derivation

variables {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M']

/-- The differential of a function interpreted in the context of derivations. -/
def fdifferential_map (f : C^∞⟮I, M; I', M'⟯) (x : M) (v : point_derivation I M x) :
  (point_derivation I' M' (f x)) :=
{ to_fun := λ g, v (g.comp f),
  map_add' := λ g h, by rw [smooth_map.add_comp, derivation.map_add],
  map_smul' := λ k g, by rw [smooth_map.smul_comp, derivation.map_smul],
  leibniz' := λ g h, by {simp only [derivation.leibniz, smooth_map.mul_comp], refl} }

/-- The differential is a linear map. -/
def fdifferential (f : C^∞⟮I, M; I', M'⟯) (x : M) : (point_derivation I M x) →ₗ[𝕜]
  (point_derivation I' M' (f x)) :=
{ to_fun := fdifferential_map f x,
  map_smul' := λ k v, rfl,
  map_add' := λ v w, rfl }

/- Standard notion for the differential. The abbreviation is `MId`. -/
localized "notation `𝒅` := fdifferential" in manifold

lemma apply_fdifferential (f : C^∞⟮I, M; I', M'⟯) (x : M) (v : point_derivation I M x)
  (g : C^∞⟮I', M'; 𝕜⟯) :
  𝒅f x v g = v (g.comp f) := rfl

variables {E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M'']

@[simp] lemma fdifferential_comp (g : C^∞⟮I', M'; I'', M''⟯) (f : C^∞⟮I, M; I', M'⟯) (x : M) :
  (𝒅g (f x)).comp (𝒅f x) = 𝒅(g.comp f) x :=
by { ext, simp only [apply_fdifferential], refl }

end
