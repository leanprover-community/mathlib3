/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import geometry.manifold.times_cont_mdiff
import topology.continuous_map

/-!
# Smooth bundled map

In this file we define the type `smooth_map` of smooth bundled maps.
-/

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
(I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
(M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
{E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H'']
{I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M'']
(n : with_top ℕ)

@[protect_proj]
structure times_cont_mdiff_map :=
(to_fun                   : M → M')
(times_cont_mdiff_to_fun  : times_cont_mdiff I I' n to_fun)

/-- Bundled smooth maps. -/
def smooth_map := times_cont_mdiff_map I I' M M' ⊤

notation `C[` n `](` I `, ` M `; ` I' `, ` M' `)` := times_cont_mdiff_map I I' M M' n
notation `C[` n `](` I `, ` M `; ` k `)` := times_cont_mdiff_map I (model_with_corners_self k k) M k n
notation `C[` n `](` I `, ` M `)` := times_cont_mdiff_map I (model_with_corners_self ℝ ℝ) M ℝ n
notation `C∞(` I `, ` M `; ` I' `, ` M' `)` := times_cont_mdiff_map I I' M M' ⊤
notation `C∞(` I `, ` M `; ` k `)` := times_cont_mdiff_map I (model_with_corners_self k k) M k ⊤
notation `C∞(` I `, ` M `)` := times_cont_mdiff_map I (model_with_corners_self ℝ ℝ) M ℝ ⊤

namespace times_cont_mdiff_map

variables {I} {I'} {M} {M'}

instance : has_coe_to_fun C[n](I, M; I', M') := ⟨_, times_cont_mdiff_map.to_fun⟩
instance : has_coe C[n](I, M; I', M') C(M, M') :=
⟨λ f, ⟨f.to_fun, f.times_cont_mdiff_to_fun.continuous⟩⟩

variables {f g : C[n](I, M; I', M')}

protected lemma times_cont_mdiff (f : C[n](I, M; I', M')) :
  times_cont_mdiff I I' n f := f.times_cont_mdiff_to_fun

protected lemma smooth (f : C∞(I, M; I', M')) :
  smooth I I' f := f.times_cont_mdiff_to_fun

lemma coe_inj ⦃f g : C[n](I, M; I', M')⦄ (h : (f : M → M') = g) : f = g :=
by cases f; cases g; cases h; refl

@[ext] theorem ext (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext h

/-- The identity as a smooth map. -/
def id : C[n](I, M; I, M) := ⟨id, times_cont_mdiff_id⟩

/-- The composition of smooth maps, as a smooth map. -/
def comp (f : C[n](I', M'; I'', M'')) (g : C[n](I, M; I', M')) : C[n](I, M; I'', M'') :=
{ to_fun := λ a, f (g a),
  times_cont_mdiff_to_fun := f.times_cont_mdiff_to_fun.comp g.times_cont_mdiff_to_fun, }

instance [inhabited M'] : inhabited C[n](I, M; I', M') :=
⟨⟨λ _, default _, times_cont_mdiff_const⟩⟩

/-- Constant map as a smooth map -/
def const (y : M') : C[n](I, M; I', M') := ⟨λ x, y, times_cont_mdiff_const⟩

end times_cont_mdiff_map

namespace smooth_map

variables {I} {I'} {M} {M'}

/-- Constant map as a smooth map -/
def const (y : M') : C∞(I, M; I', M') := ⟨λ x, y, smooth_const⟩

end smooth_map
