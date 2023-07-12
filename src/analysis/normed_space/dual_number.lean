/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.dual_number
import analysis.normed_space.triv_sq_zero_ext

/-!
# Results on `dual_number R` related to the norm

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These are just restatements of similar statements about `triv_sq_zero_ext R M`.

## Main results

* `exp_eps`

-/

namespace dual_number
open triv_sq_zero_ext

variables (𝕜 : Type*) {R : Type*}

variables [is_R_or_C 𝕜] [normed_comm_ring R] [normed_algebra 𝕜 R]
variables [topological_ring R] [complete_space R] [t2_space R]

@[simp] lemma exp_eps : exp 𝕜 (eps : dual_number R) = 1 + eps :=
exp_inr _ _

@[simp] lemma exp_smul_eps (r : R) : exp 𝕜 (r • eps : dual_number R) = 1 + r • eps :=
by rw [eps, ←inr_smul, exp_inr]

end dual_number
