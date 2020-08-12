/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import geometry.manifold.tangent_bundle_derivation
import ring_theory.derivation

noncomputable theory

open_locale lie_group manifold

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H]

def Lb (I : model_with_corners 𝕜 E H)
  (G : Type*) [topological_space G] [charted_space H G] [smooth_manifold_with_corners I G]
  [group G] [topological_group G] [lie_group I G] (g : G) : C∞(I, G; I, G) :=
⟨(L g), smooth_mul_left⟩

@[simp] lemma Lb_apply (I : model_with_corners 𝕜 E H) (G : Type*) [topological_space G] [charted_space H G] [smooth_manifold_with_corners I G]
  [group G] [topological_group G] [lie_group I G] (g h : G) : (Lb I G g) h = g * h := rfl

/-def point_derivation_eq {I : model_with_corners 𝕜 E H}
  {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {x y : M}
  (h : x = y) (v : point_derivation I M x) : point_derivation I M y :=
by{ rw h at v, exact v }-/

lemma Lb_apply_one (I : model_with_corners 𝕜 E H) {G : Type*} [topological_space G]
  [charted_space H G] [smooth_manifold_with_corners I G] [group G] [topological_group G]
  [lie_group I G] (g : G) : (Lb I G g) 1 = g := by rw [Lb_apply, mul_one]

structure left_invariant_vector_field (I : model_with_corners 𝕜 E H)
  (G : Type*) [topological_space G] [charted_space H G] [smooth_manifold_with_corners I G]
  [group G] [topological_group G] [lie_group I G] extends vector_field_derivation I G :=
(left_invariant' : ∀ f g, to_vector_field_derivation.eval g f = (fd (Lb I G g)) (1 : G) (to_vector_field_derivation.eval (1 : G)) f)

variables {I : model_with_corners 𝕜 E H}
  {G : Type*} [topological_space G] [charted_space H G] [smooth_manifold_with_corners I G]
  [group G] [topological_group G] [lie_group I G]

namespace left_invariant_vector_field

instance : has_coe (left_invariant_vector_field I G) (vector_field_derivation I G)
:= ⟨λ X, X.to_vector_field_derivation⟩

@[simp] lemma to_vfield_der_eq_coe (X : left_invariant_vector_field I G) :
  X.to_vector_field_derivation = X := rfl

@[simp] lemma coe_lift_eq_coe (X : left_invariant_vector_field I G) :
  ⇑(X : vector_field_derivation I G) = (X : C∞(I, G; 𝕜) → C∞(I, G; 𝕜)) := rfl

variables
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {x : M}
(X Y : left_invariant_vector_field I G) (f : C∞(I, G; 𝕜)) (g h : G)

def eval : point_derivation I G g :=
X.to_vector_field_derivation.eval g

@[simp] lemma coe_eval : (X : vector_field_derivation I G).eval g = X.eval g := rfl

@[simp] lemma eval_apply : X.eval g f = (X f) g := rfl

lemma left_invariant : X.eval g f = (fd (Lb I G g)) (1 : G) (X.eval (1 : G)) f :=
begin
  sorry,
end

lemma left_invariant_ext :
  X.eval (g * h) f = (fd (Lb I G g)) h (X.eval h) f :=
begin
  sorry,
end

@[simp] lemma leftinvfield_comp_Lb : (X f).comp (Lb I G g) = X (f.comp (Lb I G g)) :=
by ext h; rw [smooth_map.comp_apply, Lb_apply, ←eval_apply, left_invariant_ext,
  apply_fdifferential, eval_apply]

instance : has_bracket (left_invariant_vector_field I G) :=
{ bracket := λ X Y, ⟨⁅X, Y⁆, begin
    intros f g,
    have hX := X.left_invariant' (Y f) g, have hY := Y.left_invariant' (X f) g,
    simp only [apply_fdifferential, to_vfield_der_eq_coe, vector_field_derivation.eval_apply,
      coe_lift_eq_coe] at hX hY,
    simp only [apply_fdifferential, vector_field_derivation.eval_apply,
      vector_field_derivation.commutator_apply, coe_lift_eq_coe, to_vfield_der_eq_coe,
      smooth_map.sub_apply, hX, hY, leftinvfield_comp_Lb], end⟩ }

  @[simp] lemma commutator_apply : ⁅X, Y⁆ f = X (Y f) - Y (X f) :=
by rw [commutator_coe_vector_field_derivation, vector_field_derivation.commutator_apply]; refl

end left_invariant_vector_field
