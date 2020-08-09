/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import geometry.manifold.tangent_bundle_derivation
import ring_theory.derivation

open_locale lie_group manifold

open vector_field_derivation

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H]

def Lb (I : model_with_corners 𝕜 E H)
  (G : Type*) [topological_space G] [charted_space H G] [smooth_manifold_with_corners I G]
  [group G] [topological_group G] [lie_group I G] (g : G) : C∞(I, G; I, G) :=
⟨(L g), smooth_mul_left⟩

@[simp] lemma asdf (I : model_with_corners 𝕜 E H) (G : Type*) [topological_space G] [charted_space H G] [smooth_manifold_with_corners I G]
  [group G] [topological_group G] [lie_group I G] (g h : G) : (Lb I G g) h = g * h := rfl

structure left_invariant_vector_field (I : model_with_corners 𝕜 E H)
  (G : Type*) [topological_space G] [charted_space H G] [smooth_manifold_with_corners I G]
  [group G] [topological_group G] [lie_group I G] :=
(X : vector_field_derivation I G)
(left_invariant : ∀ g : G, X.eval g == (fd (Lb I G g)) (1 : G) (X.eval (1 : G)))

variables {I : model_with_corners 𝕜 E H}
  {G : Type*} [topological_space G] [charted_space H G] [smooth_manifold_with_corners I G]
  [group G] [topological_group G] [lie_group I G]

instance : has_coe (left_invariant_vector_field I G) (derivation 𝕜 C∞(I, G; 𝕜) C∞(I, G; 𝕜))
:= ⟨λ x, x.X⟩

instance : has_bracket (left_invariant_vector_field I G) :=
{ bracket := λ X Y, ⟨⁅X, Y⁆, by {intro g, sqeeze_simp [eval_commutator]}⟩,
}
