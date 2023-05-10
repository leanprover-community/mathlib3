/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/

import linear_algebra.determinant
import linear_algebra.free_module.finite.basic

/-!
# Determinants in free (finite) modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Quite a lot of our results on determinants (that you might know in vector spaces) will work for all
free (finite) modules over any commutative ring.

## Main results

 * `linear_map.det_zero''`: The determinant of the constant zero map is zero, in a finite free
   nontrivial module.
-/

@[simp] lemma linear_map.det_zero'' {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
  [module.free R M] [module.finite R M] [nontrivial M] :
  linear_map.det (0 : M →ₗ[R] M) = 0 :=
begin
  letI : nonempty (module.free.choose_basis_index R M) :=
    (module.free.choose_basis R M).index_nonempty,
  nontriviality R,
  exact linear_map.det_zero' (module.free.choose_basis R M)
end
