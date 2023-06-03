/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import linear_algebra.multilinear.basic
import linear_algebra.free_module.finite.matrix

/-! # Multilinear maps over finite dimensional spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The main results are that multilinear maps over finitely-generated, free modules are
finitely-generated and free.

* `module.finite.multilinear_map`
* `module.free.multilinear_map`

We do not put this in `linear_algebra/multilinear_map/basic` to avoid making the imports too large
there.
-/

namespace multilinear_map

variables {ι R M₂ : Type*} {M₁ : ι → Type*}
variables [finite ι]
variables [comm_ring R] [add_comm_group M₂] [module R M₂]
variables [Π i, add_comm_group (M₁ i)] [Π i, module R (M₁ i)]
variables [module.finite R M₂] [module.free R M₂]
variables [∀ i, module.finite R (M₁ i)] [∀ i, module.free R (M₁ i)]

-- the induction requires us to show both at once
private lemma free_and_finite :
  module.free R (multilinear_map R M₁ M₂) ∧ module.finite R (multilinear_map R M₁ M₂) :=
begin
  -- the `fin n` case is sufficient
  suffices : ∀ n (N : fin n → Type*) [Π i, add_comm_group (N i)],
    by exactI ∀ [Π i, module R (N i)],
    by exactI ∀ [∀ i, module.finite R (N i)] [∀ i, module.free R (N i)],
      module.free R (multilinear_map R N M₂) ∧ module.finite R (multilinear_map R N M₂),
  { casesI nonempty_fintype ι,
    casesI this _ (M₁ ∘ (fintype.equiv_fin ι).symm),
    have e := dom_dom_congr_linear_equiv' R M₁ M₂ (fintype.equiv_fin ι),
    exact ⟨module.free.of_equiv e.symm, module.finite.equiv e.symm⟩, },
  introsI n N _ _ _ _,
  unfreezingI { induction n with n ih },
  { exact ⟨module.free.of_equiv (const_linear_equiv_of_is_empty R N M₂),
           module.finite.equiv (const_linear_equiv_of_is_empty R N M₂)⟩ },
  { suffices :
      module.free R (N 0 →ₗ[R] multilinear_map R (λ (i : fin n), N i.succ) M₂) ∧
      module.finite R (N 0 →ₗ[R] multilinear_map R (λ (i : fin n), N i.succ) M₂),
    { casesI this,
      exact ⟨module.free.of_equiv (multilinear_curry_left_equiv R N M₂),
            module.finite.equiv (multilinear_curry_left_equiv R N M₂)⟩ },
    casesI ih (λ i, N i.succ),
    exact ⟨module.free.linear_map _ _ _, module.finite.linear_map _ _⟩ },
end

instance _root_.module.finite.multilinear_map : module.finite R (multilinear_map R M₁ M₂) :=
free_and_finite.2

instance _root_.module.free.multilinear_map : module.free R (multilinear_map R M₁ M₂) :=
free_and_finite.1

end multilinear_map
