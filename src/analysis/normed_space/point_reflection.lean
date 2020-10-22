/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import topology.metric_space.isometry
import analysis.normed_space.add_torsor

/-!
# Point reflection in a point as an `isometric` homeomorphism

Given a `normed_group E` and `x : E`, we define `isometric.point_reflection x` to be
the point reflection in `x` interpreted as an `isometric` homeomorphism.

Point reflection is defined as an `equiv.perm` in `data.equiv.mul_add`. In this file
we restate results about `equiv.point_reflection` for an `isometric.point_reflection`, and
add a few results about `dist`.

## Tags

point reflection, isometric
-/

variables (R : Type*) {E PE : Type*} [normed_group E] [add_comm_group PE]
  [metric_space PE] [normed_add_torsor E PE]

namespace isometric

section normed_group

end normed_group

section module

variables [ring R] [invertible (2:R)] [normed_group E] [module R E]

variable (R)

include R

end module


end isometric
