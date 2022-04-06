/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import algebra.direct_sum.module
import data.finsupp.to_dfinsupp

/-!
# Results on direct sums and finitely supported functions.

1. The linear equivalence between finitely supported functions `ι →₀ M` and
the direct sum of copies of `M` indexed by `ι`.
-/

universes u v w

noncomputable theory
open_locale direct_sum

open linear_map submodule
variables {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M]

section finsupp_lequiv_direct_sum

variables (R M) (ι : Type*) [decidable_eq ι]

/-- The finitely supported functions `ι →₀ M` are in linear equivalence with the direct sum of
copies of M indexed by ι. -/
def finsupp_lequiv_direct_sum : (ι →₀ M) ≃ₗ[R] ⨁ i : ι, M :=
by haveI : Π m : M, decidable (m ≠ 0) := classical.dec_pred _; exact finsupp_lequiv_dfinsupp R

@[simp] theorem finsupp_lequiv_direct_sum_single (i : ι) (m : M) :
  finsupp_lequiv_direct_sum R M ι (finsupp.single i m) = direct_sum.lof R ι _ i m :=
finsupp.to_dfinsupp_single i m

@[simp] theorem finsupp_lequiv_direct_sum_symm_lof (i : ι) (m : M) :
  (finsupp_lequiv_direct_sum R M ι).symm (direct_sum.lof R ι _ i m) = finsupp.single i m :=
begin
  letI : Π m : M, decidable (m ≠ 0) := classical.dec_pred _,
  exact (dfinsupp.to_finsupp_single i m),
end

end finsupp_lequiv_direct_sum
