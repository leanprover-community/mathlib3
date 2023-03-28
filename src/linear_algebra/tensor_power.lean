/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import linear_algebra.pi_tensor_product
import logic.equiv.fin
import algebra.graded_monoid

/-!
# Tensor power of a semimodule over a commutative semirings

We define the `n`th tensor power of `M` as the n-ary tensor product indexed by `fin n` of `M`,
`⨂[R] (i : fin n), M`. This is a special case of `pi_tensor_product`.

This file introduces the notation `⨂[R]^n M` for `tensor_power R n M`, which in turn is an
abbreviation for `⨂[R] i : fin n, M`.

## Main definitions:

* `tensor_power.ghas_one`
* `tensor_power.ghas_mul`

## TODO

Show `direct_sum.galgebra R (λ i, ⨂[R]^i M)` and `algebra R (⨁ n : ℕ, ⨂[R]^n M)`.


## Implementation notes

In this file we use `ₜ1` and `ₜ*` as local notation for the graded multiplicative structure on
tensor powers. Elsewhere, using `1` and `*` on `graded_monoid` should be preferred.
-/

open_locale tensor_product

/-- Homogenous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for
`⨂[R] (i : fin n), M`. -/
@[reducible] protected def tensor_power (R : Type*) (n : ℕ) (M : Type*)
  [comm_semiring R] [add_comm_monoid M] [module R M] : Type* :=
⨂[R] i : fin n, M

variables {R : Type*} {M : Type*} [comm_semiring R] [add_comm_monoid M] [module R M]

localized "notation (name := tensor_power)
  `⨂[`:100 R `]^`:80 n:max := tensor_power R n" in tensor_product

namespace tensor_power
open_locale tensor_product
open pi_tensor_product

/-- As a graded monoid, `⨂[R]^i M` has a `1 : ⨂[R]^0 M`. -/
instance ghas_one : graded_monoid.ghas_one (λ i, ⨂[R]^i M) :=
{ one := tprod R fin.elim0 }

local notation `ₜ1` := @graded_monoid.ghas_one.one ℕ (λ i, ⨂[R]^i M) _ _

lemma ghas_one_def : ₜ1 = tprod R fin.elim0 := rfl

/-- A variant of `pi_tensor_prod.tmul_equiv` with the result indexed by `fin (n + m)`. -/
def mul_equiv {n m : ℕ} : (⨂[R]^n M) ⊗[R] (⨂[R]^m M) ≃ₗ[R] ⨂[R]^(n + m) M :=
(tmul_equiv R M).trans (reindex R M fin_sum_fin_equiv)

/-- As a graded monoid, `⨂[R]^i M` has a `(*) : ⨂[R]^i M → ⨂[R]^j M → ⨂[R]^(i + j) M`. -/
instance ghas_mul : graded_monoid.ghas_mul (λ i, ⨂[R]^i M) :=
{ mul := λ i j a b, mul_equiv (a ⊗ₜ b) }

local infix ` ₜ* `:70 := @graded_monoid.ghas_mul.mul ℕ (λ i, ⨂[R]^i M) _ _ _ _

lemma ghas_mul_def {i j} (a : ⨂[R]^i M) (b : ⨂[R]^j M) : a ₜ* b = mul_equiv (a ⊗ₜ b) := rfl

end tensor_power
