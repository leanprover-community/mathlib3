/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import linear_algebra.multilinear.basic
import linear_algebra.matrix.to_lin

/-! # Multilinear maps over finite dimensional spaces

The main result of this file is `multilinear_map.finite_dimensional`.

We do not put this in `linear_algebra/multilinear_map/basic`, as `matrix.to_lin` pulls in a lot of
imports, which can cause timeouts downstream.
-/

namespace multilinear_map

variables {ι R M₂ : Type*} {M₁ : ι → Type*}
variables [decidable_eq ι]
variables [fintype ι] [field R] [add_comm_group M₂] [module R M₂] [finite_dimensional R M₂]
variables [∀ i, add_comm_group (M₁ i)] [∀ i, module R (M₁ i)] [∀ i, finite_dimensional R (M₁ i)]

instance : finite_dimensional R (multilinear_map R M₁ M₂) :=
begin
  suffices : ∀ n (N : fin n → Type*) [∀ i, add_comm_group (N i)],
    by exactI ∀ [∀ i, module R (N i)], by exactI ∀ [∀ i, finite_dimensional R (N i)],
    finite_dimensional R (multilinear_map R N M₂),
  { haveI := this _ (M₁ ∘ (fintype.equiv_fin ι).symm),
    have e := dom_dom_congr_linear_equiv' R M₁ M₂ (fintype.equiv_fin ι),
    exact e.symm.finite_dimensional, },
  intros,
  induction n with n ih,
  { exactI (const_linear_equiv_of_is_empty R N M₂ : _).finite_dimensional, },
  { resetI,
    suffices : finite_dimensional R (N 0 →ₗ[R] multilinear_map R (λ (i : fin n), N i.succ) M₂),
    { exact (multilinear_curry_left_equiv R N M₂).finite_dimensional, },
    apply linear_map.finite_dimensional, },
end

end multilinear_map
