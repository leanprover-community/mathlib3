/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Heather Macbeth
-/

import geometry.manifold.algebra.lie_group
import analysis.normed_space.units

/-!
# Units of normed algebra

In this file we aim to prove that the units of a complete normed algebra are a Lie group.

## TODO

We are still missing the main result, i.e. the instance

```
instance units_of_normed_algebra.lie_group
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {R : Type*} [normed_ring R] [normed_algebra 𝕜 R] [complete_space R] :
  lie_group (model_with_corners_self 𝕜 R) (units R) :=
{ smooth_mul := begin
    sorry,
  end,
  smooth_inv := begin
    sorry,
  end,
  ..units.smooth_manifold_with_corners,
  /- Why does it not find the instance alone? -/ }
```
-/

noncomputable theory

open_locale manifold

instance {R : Type*} [normed_ring R] [complete_space R] : charted_space R (units R) :=
units.open_embedding_coe.singleton_charted_space

namespace units

variables {R : Type*} [normed_ring R] [complete_space R]

@[simp, mfld_simps] lemma chart_at_apply {a : units R} {b : units R} : chart_at R a b = b := rfl
@[simp, mfld_simps] lemma chart_at_source {a : units R} : (chart_at R a).source = set.univ := rfl

end units

instance {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {R : Type*} [normed_ring R] [normed_algebra 𝕜 R] [complete_space R] :
  smooth_manifold_with_corners 𝓘(𝕜, R) (units R) :=
units.open_embedding_coe.singleton_smooth_manifold_with_corners 𝓘(𝕜, R)
