/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/

import algebra.algebra.bilinear
import algebra.algebra.tower.basic

/-!
# Facts about algebra towers involving bilinear maps and tensor products

We move a few basic statements about algebra towers out of `algebra.algebra.tower.basic`,
in order to avoid importing `linear_algebra.bilinear_map` and
`linear_algebra.tensor_product` unnecessarily.
-/

universes u v

variables (R : Type u) (A : Type v)

namespace algebra

variables [comm_semiring R] [semiring A] [algebra R A]

variables {A}

lemma lmul_algebra_map (x : R) :
  algebra.lmul R A (algebra_map R A x) = algebra.lsmul R A x :=
eq.symm $ linear_map.ext $ smul_def x

end algebra
