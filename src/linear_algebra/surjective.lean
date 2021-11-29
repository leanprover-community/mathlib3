/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import linear_algebra.bilinear_map

/-!
# Pushing module structure around surjections

This file contains some results on module structures induced by a surjection,
for example a surjective ring hom `R →+* S`, if the kernel is contained
within the kernel of `(•) : R →ₗ (M →ₗ M)`, transports the `R`-module structure
on `M` to an `S`-module structure.

## Main definitions

 * `function.surjective.module'_left_of_ring`: let `M` be an `R`-module,
   then a surjective map `f : R →+* S` induces an `S`-module structure on `M`,
   if the kernel of `f` are zero-smul-divisors.
-/

/-- Let `M` be an `R`-module, then a surjective map `f : R →+* S` induces an
`S`-module structure on `M`, if the kernel of `f` are zero-smul-divisors.

See also `function.surjective.module_left` if you want more control over the definition of `(•)`,
and `function.surjective.module_left'` if `R` and `S` don't have additive inverses.
-/
@[reducible]
noncomputable def function.surjective.module_left'_of_ring {R S M : Type*} [comm_ring R]
  [add_comm_group M] [module R M] [ring S]
  {f : R →+* S} (hf : function.surjective f) (hsmul : f.ker ≤ (linear_map.lsmul R M).ker) :
  module S M :=
hf.module_left' $ λ a b hab, begin
  suffices : linear_map.lsmul R M a = linear_map.lsmul R M b,
  { intros, simp only [← linear_map.lsmul_apply, this] },
  rw [← sub_eq_zero, ← linear_map.map_sub, ← linear_map.mem_ker],
  rw [← sub_eq_zero, ← ring_hom.map_sub, ← ring_hom.mem_ker] at hab,
  exact hsmul hab
end

lemma function.surjective.module_left'_of_ring_smul {R S M : Type*} [comm_ring R]
  [add_comm_group M] [module R M] [ring S]
  {f : R →+* S} (hf : function.surjective f) (hsmul : f.ker ≤ (linear_map.lsmul R M).ker)
  (c : R) (x : M) :
  by { letI := hf.module_left'_of_ring hsmul, exact f c • x } = c • x :=
hf.module_left'_smul _ _ _
