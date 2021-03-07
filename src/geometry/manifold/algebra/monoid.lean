/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import geometry.manifold.times_cont_mdiff

/-!
# Smooth monoid
A smooth monoid is a monoid that is also a smooth manifold, in which multiplication is a smooth map
of the product manifold `G` × `G` into `G`.

In this file we define the basic structures to talk about smooth monoids: `has_smooth_mul` and its
additive counterpart `has_smooth_add`. These structures are general enough to also talk about smooth
semigroups.
-/

section

set_option old_structure_cmd true

/-- Basic hypothesis to talk about a smooth (Lie) additive monoid or a smooth additive
semigroup. A smooth additive monoid over `α`, for example, is obtained by requiring both the
instances `add_monoid α` and `has_smooth_add α`. -/
@[ancestor smooth_manifold_with_corners]
class has_smooth_add {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
  (G : Type*) [has_add G] [topological_space G] [charted_space H G]
  extends smooth_manifold_with_corners I G : Prop :=
(smooth_add : smooth (I.prod I) I (λ p : G×G, p.1 + p.2))

/-- Basic hypothesis to talk about a smooth (Lie) monoid or a smooth semigroup.
A smooth monoid over `G`, for example, is obtained by requiring both the instances `monoid G`
and `has_smooth_mul I G`. -/
@[ancestor smooth_manifold_with_corners, to_additive]
class has_smooth_mul {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
  (G : Type*) [has_mul G] [topological_space G] [charted_space H G]
  extends smooth_manifold_with_corners I G : Prop :=
(smooth_mul : smooth (I.prod I) I (λ p : G×G, p.1 * p.2))

end

section has_smooth_mul

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{H : Type*} [topological_space H]
{E : Type*} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H}
{G : Type*} [has_mul G] [topological_space G] [charted_space H G] [has_smooth_mul I G]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H' M]

section

variables (I)

@[to_additive]
lemma smooth_mul : smooth (I.prod I) I (λ p : G×G, p.1 * p.2) :=
has_smooth_mul.smooth_mul

@[to_additive]
lemma has_continuous_mul_of_smooth : has_continuous_mul G :=
⟨(smooth_mul I).continuous⟩

end

@[to_additive]
lemma smooth.mul {f : M → G} {g : M → G} (hf : smooth I' I f) (hg : smooth I' I g) :
  smooth I' I (f * g) :=
(smooth_mul I).comp (hf.prod_mk hg)

@[to_additive]
lemma smooth_mul_left {a : G} : smooth I I (λ b : G, a * b) :=
smooth_const.mul smooth_id

@[to_additive]
lemma smooth_mul_right {a : G} : smooth I I (λ b : G, b * a) :=
smooth_id.mul smooth_const

@[to_additive]
lemma smooth_on.mul {f : M → G} {g : M → G} {s : set M}
  (hf : smooth_on I' I f s) (hg : smooth_on I' I g s) :
  smooth_on I' I (f * g) s :=
((smooth_mul I).comp_smooth_on (hf.prod_mk hg) : _)

/- Instance of product -/
@[to_additive]
instance has_smooth_mul.prod {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  (G : Type*) [topological_space G] [charted_space H G]
  [has_mul G] [has_smooth_mul I G]
  {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
  (G' : Type*) [topological_space G'] [charted_space H' G']
  [has_mul G'] [has_smooth_mul I' G'] :
  has_smooth_mul (I.prod I') (G×G') :=
{ smooth_mul := ((smooth_fst.comp smooth_fst).smooth.mul (smooth_fst.comp smooth_snd)).prod_mk
    ((smooth_snd.comp smooth_fst).smooth.mul (smooth_snd.comp smooth_snd)),
  .. smooth_manifold_with_corners.prod G G' }

variable (I)

end has_smooth_mul

section monoid

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{H : Type*} [topological_space H]
{E : Type*} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H}
{G : Type*} [monoid G] [topological_space G] [charted_space H G] [has_smooth_mul I G]
{H' : Type*} [topological_space H']
{E' : Type*} [normed_group E'] [normed_space 𝕜 E'] {I' : model_with_corners 𝕜 E' H'}
{G' : Type*} [monoid G'] [topological_space G'] [charted_space H' G'] [has_smooth_mul I' G']

lemma smooth_pow : ∀ n : ℕ, smooth I I (λ a : G, a ^ n)
| 0 := by { simp only [pow_zero], exact smooth_const }
| (k+1) := show smooth I I (λ (a : G), a * a ^ k), from smooth_id.mul (smooth_pow _)

/-- Morphism of additive smooth monoids. -/
structure smooth_add_monoid_morphism
  (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
  (G : Type*) [topological_space G] [charted_space H G] [add_monoid G] [has_smooth_add I G]
  (G' : Type*) [topological_space G'] [charted_space H' G'] [add_monoid G'] [has_smooth_add I' G']
  extends G →+ G' :=
(smooth_to_fun : smooth I I' to_fun)

/-- Morphism of smooth monoids. -/
@[to_additive] structure smooth_monoid_morphism
  (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
  (G : Type*) [topological_space G] [charted_space H G] [monoid G] [has_smooth_mul I G]
  (G' : Type*) [topological_space G'] [charted_space H' G'] [monoid G'] [has_smooth_mul I' G']
  extends G →* G' :=
(smooth_to_fun : smooth I I' to_fun)

@[to_additive]
instance : has_one (smooth_monoid_morphism I I' G G') :=
⟨{ smooth_to_fun := smooth_const, to_monoid_hom := 1 }⟩

@[to_additive]
instance : inhabited (smooth_monoid_morphism I I' G G') := ⟨1⟩

@[to_additive]
instance : has_coe_to_fun (smooth_monoid_morphism I I' G G') := ⟨_, λ a, a.to_fun⟩

end monoid
