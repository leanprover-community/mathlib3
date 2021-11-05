/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Jakob von Raumer
-/
import group_theory.congruence
import linear_algebra.tensor_product.def

/-!
# The canonical left action on a tensor product of modules

This file describes left actions of various algebraic structures on the left of the
tensor product of modules, based on the fact that if `M` is an `R'`-`R` bimodule,
`R'` acts on `M ⊗[R] N` by `r • (m ⊗ n) := (r • m ⊗ n)`.

## Tags

group action, tensor product
-/
namespace tensor_product

section semiring

variables {R : Type*} [semiring R]
variables {R' : Type*} [monoid R']
variables {R'' : Type*} [semiring R'']
variables {M N : Type*}

variables [add_comm_monoid M] [add_comm_monoid N]
variables [module Rᵒᵖ M] [module R N]

end semiring

section ring

end ring

end tensor_product
