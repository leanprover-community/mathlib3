/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import geometry.manifold.algebra.smooth_functions
import ring_theory.derivation
--import geometry.manifold.temporary_to_be_removed

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

open_locale manifold

namespace point_derivation

def has_scalar (x : M) : has_scalar C^∞⟮I, M; 𝕜⟯ 𝕜 :=
{ smul := λ f k, f x * k }

lemma scalar_def {x : M} {f : C^∞⟮I, M; 𝕜⟯} {k : 𝕜} :
  @has_scalar.smul C^∞⟮I, M; 𝕜⟯ 𝕜 (has_scalar I M x) f k = f x * k := rfl

def module (x : M) : module C^∞⟮I, M; 𝕜⟯ 𝕜 :=
{ one_smul := λ k, one_mul k,
  mul_smul := λ f g k, mul_assoc _ _ _,
  smul_add := λ f g k, mul_add _ _ _,
  smul_zero := λ f, mul_zero _,
  add_smul := λ f g k, add_mul _ _ _,
  zero_smul := λ f, zero_mul _,
  ..point_derivation.has_scalar I M x }

def is_scalar_tower (x : M) :
  @is_scalar_tower 𝕜 C^∞⟮I, M; 𝕜⟯ 𝕜 _ (has_scalar I M x) _ :=
{ smul_assoc := λ k f h, by { simp only [scalar_def, algebra.id.smul_eq_mul,
    smooth_map.coe_smul, pi.smul_apply, mul_assoc]} }

end point_derivation

@[reducible] def point_derivation (x : M) :=
  @derivation 𝕜 C^∞⟮I, M; 𝕜⟯ _ _ _ 𝕜 _ (point_derivation.module I M x) _
    (point_derivation.is_scalar_tower I M x)

def tangent_bundle_derivation := Σ x : M, point_derivation I M x

/-instance : has_add (tangent_bundle_derivation I M) :=
{ add := λ v w, sigma.mk v.1 (v.2 + w.2) }-/

variables {I M}

def tangent_space_inclusion {x : M} (v : point_derivation I M x) : tangent_bundle_derivation I M :=
sigma.mk x v

/- Something weird is happening. Does not find the instance of smooth manifolds with corners.
Moreover if I define it as a reducible def .eval does not work... It also takes very long time to
typecheck -/

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

/-
(X : @derivation 𝕜 C^∞⟮I, M; 𝕜⟯ _
  (@comm_ring.to_comm_semiring C^∞⟮I, M; 𝕜⟯ smooth_map_comm_ring) times_cont_mdiff_map.algebra C^∞⟮I, M; 𝕜⟯ _
  (semiring.to_module) (smooth_map_module) _)

  (X Y :
  @derivation 𝕜
  C^∞⟮I, M; 𝕜⟯
  (@comm_ring.to_comm_semiring 𝕜 (@semi_normed_comm_ring.to_comm_ring 𝕜 (@normed_comm_ring.to_semi_normed_comm_ring 𝕜 (@normed_field.to_normed_comm_ring 𝕜 (@nondiscrete_normed_field.to_normed_field 𝕜 _inst_1)))))
  (@comm_ring.to_comm_semiring C^∞⟮I, M; 𝕜⟯ smooth_map_comm_ring)
  times_cont_mdiff_map.algebra
  C^∞⟮I, M; 𝕜⟯
  (@add_comm_group.to_cancel_add_comm_monoid C^⊤⟮I, M; 𝓘(𝕜, 𝕜), 𝕜⟯ _)
  (semiring.to_module)
  (smooth_map_module)
  (_root_.is_scalar_tower.right))
-/

/-#check is_scalar_tower.right

set_option trace.class_instances true-/

variables {I} {M} (X Y : derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^⊤⟮I, M; 𝓘(𝕜, 𝕜), 𝕜⟯)
  (f g : C^∞⟮I, M; 𝕜⟯) (r : 𝕜)

set_option trace.class_instances false

def derivation.eval (x : M) : point_derivation I M x :=
{ to_fun := λ f, (X f) x,
  map_add' := λ f g, by { rw derivation.map_add, refl },
  map_smul' := λ f g, by { rw [derivation.map_smul, algebra.id.smul_eq_mul], refl },
  leibniz' := λ h k, by { dsimp only [], rw [derivation.leibniz, algebra.id.smul_eq_mul], refl } }

@[simp] lemma eval_apply (x : M) : X.eval x f = (X f) x := rfl

@[simp] lemma eval_add (x : M) :
  (X + Y).eval x = X.eval x + Y.eval x :=
by ext f; simp only [derivation.add_apply, eval_apply, smooth_map.coe_add, pi.add_apply]

/- to be moved -/
@[simp] lemma ring_commutator.apply {α : Type*} {R : Type*} [ring R] (f g : α → R) (a : α) :
  ⁅f, g⁆ a = ⁅f a, g a⁆ := rfl

variables {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

def fdifferential (f : C^∞⟮I, M; I', M'⟯) (x : M) (v : point_derivation I M x) :
  (point_derivation I' M' (f x)) :=
{ to_fun := λ g, v (g.comp f),
  map_add' := λ g h, by rw [smooth_map.add_comp, derivation.map_add],
  map_smul' := λ k g, by rw [smooth_map.smul_comp, derivation.map_smul],
  leibniz' := λ g h, by {simp only [derivation.leibniz, smooth_map.mul_comp], refl} } /-TODO: change it so that it is a linear map -/

localized "notation `fd` := fdifferential" in manifold

lemma apply_fdifferential (f : C^∞⟮I, M; I', M'⟯) (x : M) (v : point_derivation I M x)
  (g : C^∞⟮I', M'; 𝕜⟯) :
  fd f x v g = v (g.comp f) := rfl

variables {E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M'']

@[simp] lemma fdifferential_comp (g : C^∞⟮I', M'; I'', M''⟯) (f : C^∞⟮I, M; I', M'⟯) (x : M) :
  (fd g (f x)) ∘ (fd f x) = fd (g.comp f) x :=
by { ext, simp only [apply_fdifferential], refl }

end
