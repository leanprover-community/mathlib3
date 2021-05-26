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
{M : Type*} [topological_space M] [charted_space H M]

open_locale manifold

namespace instances
def smooth_functions_algebra : algebra 𝕜 C^∞⟮I, M; 𝕜⟯ := infer_instance
attribute [instance, priority 10000] smooth_functions_algebra
def tower : is_scalar_tower 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ := infer_instance
attribute [instance, priority 10000] tower
def sizeof : has_sizeof (derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^⊤⟮I, M; 𝕜⟯) := infer_instance
attribute [instance, priority 100000] sizeof
end instances

namespace point_derivation

def smooth_funtions.eval' (x : M) : C^∞⟮I, M; 𝕜⟯ →+* 𝕜 :=
{ to_fun    := λ f, f x,
  map_one'  := rfl,
  map_mul'  := λ f g, rfl,
  map_zero' := rfl,
  map_add'  := λ f g, rfl }

def algebra (x : M) : algebra C^∞⟮I, M; 𝕜⟯ 𝕜 := (smooth_funtions.eval' I x).to_algebra

def smooth_functions.eval (x : M) :
  @alg_hom C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ 𝕜 _ _ _ _ (point_derivation.algebra I x) :=
{ commutes' := λ k, rfl, ..smooth_funtions.eval' I x }

/-- The scalar multiplication defined above gives rise to a module structure. -/
def module (x : M) : module C^∞⟮I, M; 𝕜⟯ 𝕜 :=
@algebra.to_module _ _ _ _ (point_derivation.algebra I x)

lemma is_scalar_tower (x : M) :
  @is_scalar_tower 𝕜 C^∞⟮I, M; 𝕜⟯ 𝕜 _ (point_derivation.algebra I x).to_has_scalar _ :=
{ smul_assoc := λ k f h, by { simp only [scalar_def, algebra.id.smul_eq_mul,
    smooth_map.coe_smul, pi.smul_apply, mul_assoc]} }

end point_derivation

/-- The derivations at a point of a manifold. Some regard this as a possible definition of the
tangent space -/
@[reducible] def point_derivation (x : M) :=
  @derivation 𝕜 C^∞⟮I, M; 𝕜⟯ _ _ _ 𝕜 _ (point_derivation.module I x) _
    (point_derivation.is_scalar_tower I x)

variable (M)

/-- The total bundle of point derivations. -/
def derivation_bundle := Σ x : M, point_derivation I x

variables {I M}

/-- The inclusion map of derivations at a point into the total bundle. -/
def derivation_inclusion {x : M} (v : point_derivation I x) : derivation_bundle I M :=
sigma.mk x v

instance [inhabited M] : inhabited (derivation_bundle I M) :=
⟨derivation_inclusion (0 : point_derivation I (default M))⟩

section

/- Why do I need to rewrite extensionality rules for reducible defs? -/
namespace point_derivation

variables {I} {M} {x y : M} {v w : point_derivation I x} (f g : C^∞⟮I, M; 𝕜⟯) (r : 𝕜)

lemma coe_injective (h : ⇑v = w) : v = w :=
@derivation.coe_injective 𝕜 _ C^∞⟮I, M; 𝕜⟯ _ _ 𝕜 _ (point_derivation.module I x) _
  (point_derivation.is_scalar_tower I x) v w h

@[ext] theorem ext (h : ∀ f, v f = w f) : v = w :=
coe_injective $ funext h

theorem hext {u : point_derivation I y} (h1 : x = y) (h2 : ∀ f, v f = u f) : v == u :=
by { cases h1, rw heq_iff_eq, ext, exact h2 f }

end point_derivation

end

section

variables (I) {M} (X Y : derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯)
  (f g : C^∞⟮I, M; 𝕜⟯) (r : 𝕜)

def smooth_function.eval_at (x : M) :
  @linear_map C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ 𝕜 _ _ _ _ (point_derivation.module I x) :=
@alg_hom.to_linear_map C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ 𝕜 _ _ _ _ (point_derivation.algebra I x)
  (point_derivation.smooth_functions.eval I x)
namespace derivation

variable {I}

/-- The evaluation at a point as a linear map. -/
def eval_at (x : M) : (derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯) →ₗ[𝕜] point_derivation I x :=
@linear_map.derivation.comp 𝕜 _ C^∞⟮I, M; 𝕜⟯ _ _ C^∞⟮I, M; 𝕜⟯ _ _ _ 𝕜 _
  (point_derivation.module I x) _ _ (point_derivation.is_scalar_tower I x)
  (smooth_function.eval_at I x)

lemma eval_apply (x : M) : eval_at x X f = (X f) x := rfl

end derivation

variables {I} {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M']

/-- The differential of a function interpreted in the context of derivations. -/
def fdifferential_map (f : C^∞⟮I, M; I', M'⟯) (x : M) (v : point_derivation I x) :
  (point_derivation I' (f x)) :=
{ to_fun := λ g, v (g.comp f),
  map_add' := λ g h, by rw [smooth_map.add_comp, derivation.map_add],
  map_smul' := λ k g, by rw [smooth_map.smul_comp, derivation.map_smul],
  leibniz' := λ g h, by {simp only [derivation.leibniz, smooth_map.mul_comp], refl} }

/-- The differential is a linear map. -/
def fdifferential (f : C^∞⟮I, M; I', M'⟯) (x : M) : (point_derivation I x) →ₗ[𝕜]
  (point_derivation I' (f x)) :=
{ to_fun := fdifferential_map f x,
  map_smul' := λ k v, rfl,
  map_add' := λ v w, rfl }

/- Standard notion for the differential. The abbreviation is `MId`. -/
localized "notation `𝒅` := fdifferential" in manifold

lemma apply_fdifferential (f : C^∞⟮I, M; I', M'⟯) (x : M) (v : point_derivation I x)
  (g : C^∞⟮I', M'; 𝕜⟯) :
  𝒅f x v g = v (g.comp f) := rfl

variables {E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M'']

@[simp] lemma fdifferential_comp' (g : C^∞⟮I', M'; I'', M''⟯) (f : C^∞⟮I, M; I', M'⟯) (x : M) :
  (𝒅g (f x)) ∘ (𝒅f x) = 𝒅(g.comp f) x :=
by { ext, simp only [apply_fdifferential], refl }

@[simp] lemma fdifferential_comp (g : C^∞⟮I', M'; I'', M''⟯) (f : C^∞⟮I, M; I', M'⟯) (x : M) :
  (𝒅g (f x)).comp (𝒅f x) = 𝒅(g.comp f) x :=
by { ext, simp only [apply_fdifferential], refl }

end
