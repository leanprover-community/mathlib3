/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import algebra.symmetrized
import algebra.jordan.basic

/-!
# Special Jordan algebras

A commutative multiplication on a real or complex space can be constructed from any multiplication
by "symmetrisation" i.e
```
a∘b = 1/2(ab+ba).
```
When the original multiplication is associative, the symmetrised algebra is a commutative Jordan
algebra. A commutative Jordan algebra which can be constructed in this way from an associative
multiplication is said to be a special Jordan algebra.

## Main results

- `is_comm_jordan` : The symmeterised algebra arising from an associative algebra is a commutative
  Jordan algebra.

## References

* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
-/

open sym_alg

/- The symmetrisation of a real (unital, associative) algebra multiplication is a commutative
Jordan non-associative ring -/
instance (α : Type*) [ring α] [invertible (2 : α)] : is_comm_jordan (αˢʸᵐ) :=
{ mul_comm := sym_alg.mul_comm,
  lmul_comm_rmul_rmul := sym_alg.mul_jordan }
