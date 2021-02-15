/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import linear_algebra.pi_tensor_product

/-!
# Tensor power of a semimodule over a commutative semirings

We define the `n`th tensor power of `M` as the n-ary tensor product indexed by `fin n` of `M`,
`⨂[R] (i : fin n), M`. This is a special case of `pi_tensor_product`
-/

open_locale tensor_product

/-- Homogenous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for
`⨂[R] (i : fin n), M`. -/
protected abbreviation tensor_power (R : Type*) (n : ℕ) (M : Type*)
  [comm_semiring R] [add_comm_monoid M] [semimodule R M] : Type* :=
⨂[R] (i : fin n), M

variables {R : Type*} {M : Type*} [comm_semiring R] [add_comm_monoid M] [semimodule R M]

localized "notation `⨂[`:100 R `]^`:80 n:max := pi_tensor_product.fin R n"
  in tensor_product

namespace tensor_power

def one : ⨂[R]^0 M := pi_tensor_product.tprod R 0

def mul_equiv {n m : ℕ} : (⨂[R]^n M) ⊗[R] (⨂[R]^m M) ≃ₗ[R] ⨂[R]^(n + m) M :=
begin
  have : (⨂[R]^n M) ⊗[R] _ ≃ₗ[R] _ := pi_tensor_product.tmul_equiv,
  apply this.trans,
  sorry,
end

end
