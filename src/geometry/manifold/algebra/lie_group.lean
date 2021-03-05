/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import geometry.manifold.algebra.monoid

/-!
# Lie groups

A Lie group is a group that is also a smooth manifold, in which the group operations of
multiplication and inversion are smooth maps. Smoothness of the group multiplication means that
multiplication is a smooth mapping of the product manifold `G` × `G` into `G`.

Note that, since a manifold here is not second-countable and Hausdorff a Lie group here is not
guaranteed to be second-countable (even though it can be proved it is Hausdorff). Note also that Lie
groups here are not necessarily finite dimensional.

## Main definitions and statements

* `lie_add_group I G` : a Lie additive group where `G` is a manifold on the model with corners `I`.
* `lie_group I G`     : a Lie multiplicative group where `G` is a manifold on the model with
                        corners `I`.
* `lie_add_group_morphism I I' G G'`  : morphism of addittive Lie groups
* `lie_group_morphism I I' G G'`      : morphism of Lie groups

## Implementation notes
A priori, a Lie group here is a manifold with corners.

The definition of Lie group cannot require `I : model_with_corners 𝕜 E E` with the same space as the
model space and as the model vector space, as one might hope, beause in the product situation,
the model space is `model_prod E E'` and the model vector space is `E × E'`, which are not the same,
so the definition does not apply. Hence the definition should be more general, allowing
`I : model_with_corners 𝕜 E H`.
-/

noncomputable theory

section
set_option old_structure_cmd true

/-- A Lie (additive) group is a group and a smooth manifold at the same time in which
the addition and negation operations are smooth. -/
@[ancestor has_smooth_add]
class lie_add_group {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
  (G : Type*) [add_group G] [topological_space G] [charted_space H G]
  extends has_smooth_add I G : Prop :=
(smooth_neg : smooth I I (λ a:G, -a))

/-- A Lie group is a group and a smooth manifold at the same time in which
the multiplication and inverse operations are smooth. -/
@[ancestor has_smooth_mul, to_additive]
class lie_group {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
  (G : Type*) [group G] [topological_space G] [charted_space H G]
  extends has_smooth_mul I G : Prop :=
(smooth_inv : smooth I I (λ a:G, a⁻¹))

end

section lie_group

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{H : Type*} [topological_space H]
{E : Type*} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H}
{F : Type*} [normed_group F] [normed_space 𝕜 F] {J : model_with_corners 𝕜 F F}
{G : Type*} [topological_space G] [charted_space H G] [group G] [lie_group I G]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H' M]
{E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M' : Type*} [topological_space M'] [charted_space H'' M']

localized "notation `L_add` := left_add" in lie_group

localized "notation `R_add` := right_add" in lie_group

localized "notation `L` := left_mul" in lie_group

localized "notation `R` := right_mul" in lie_group

section

variable (I)

@[to_additive]
lemma smooth_inv : smooth I I (λ x : G, x⁻¹) :=
lie_group.smooth_inv

@[to_additive]
lemma topological_group_of_lie_group : topological_group G :=
{ continuous_inv := (smooth_inv I).continuous,
  .. has_continuous_mul_of_smooth I }

end

@[to_additive]
lemma smooth.inv {f : M → G}
  (hf : smooth I' I f) : smooth I' I (λx, (f x)⁻¹) :=
(smooth_inv I).comp hf

@[to_additive]
lemma smooth_on.inv {f : M → G} {s : set M}
  (hf : smooth_on I' I f s) : smooth_on I' I (λx, (f x)⁻¹) s :=
(smooth_inv I).comp_smooth_on hf

end lie_group

section prod_lie_group

/- Instance of product group -/
@[to_additive]
instance {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]  {I : model_with_corners 𝕜 E H}
  {G : Type*} [topological_space G] [charted_space H G] [group G] [lie_group I G]
  {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {G' : Type*} [topological_space G'] [charted_space H' G']
  [group G'] [lie_group I' G'] :
  lie_group (I.prod I') (G×G') :=
{ smooth_inv := smooth_fst.inv.prod_mk smooth_snd.inv,
  ..has_smooth_mul.prod _ _ _ _ }

end prod_lie_group

section normed_space_lie_group

/-! ### Normed spaces are Lie groups -/

instance normed_space_lie_group {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] :
  lie_add_group (model_with_corners_self 𝕜 E) E :=
{ smooth_add := smooth_iff.2 ⟨continuous_add, λ x y, times_cont_diff_add.times_cont_diff_on⟩,
  smooth_neg := smooth_iff.2 ⟨continuous_neg, λ x y, times_cont_diff_neg.times_cont_diff_on⟩ }

end normed_space_lie_group
