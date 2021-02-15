/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import linear_algebra.pi_tensor_product
import data.equiv.fin

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

localized "notation `⨂[`:100 R `]^`:80 n:max := tensor_power R n"
  in tensor_product

namespace tensor_power
open_locale tensor_product

/-- The canonical map from `R` to `⨂[R]^0 M` corresponding to the algebra_map of the tensor
algebra. -/
def algebra_map : R ≃ₗ[R] ⨂[R]^0 M :=
((pi_tensor_product.reindex R M fin_zero_equiv').trans pi_tensor_product.pempty_equiv).symm

def one : ⨂[R]^0 M := algebra_map 1

instance {α : pempty → Type*} : unique (Π x, α x) :=
⟨⟨λ x, pempty.elim x⟩, λ f, funext $ λ x, pempty.elim x ⟩

lemma one_eq_tprod : one = pi_tensor_product.tprod R (λ i : fin 0, (i.elim0 : M)) :=
begin
  simp [one, algebra_map],
  congr,
end

/---/
def mul_equiv {n m : ℕ} : (⨂[R]^n M) ⊗[R] (⨂[R]^m M) ≃ₗ[R] ⨂[R]^(n + m) M :=
(pi_tensor_product.tmul_equiv R M).trans (pi_tensor_product.reindex R M sum_fin_sum_equiv)

end tensor_power
