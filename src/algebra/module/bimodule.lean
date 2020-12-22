/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson, Adam Topaz, Yury Kudryashov
-/
import algebra.module.basic

/-!
# Right (semi-)modules and Bi(semi)modules

In this file, we generalize `algebra.module.basic` to

## Main Definitions
* `right_semimodule` and `right_module` are analogous to `semimodule` and `module`, but with
  scalar multiplication from the right, represented by `•ᵣ`.
* `bisemimodule` is a mixin on a `semimodule` and a `right_semimodule` structure, to indicate that
  the two scalar multiplications commute.
* `bimodule` is a `bisemimodule` where all structures involved have subtraction.

## Implementation Details
* Right scalar multiplication (`•ᵣ`) is implemented as scalar multiplication by the opposite ring.

-/

abbreviation right_semimodule (A : Type*) (M : Type*) [semiring A] [add_comm_monoid M] :=
semimodule (opposite A) M

abbreviation right_module (A : Type*) (M : Type*) [ring A] [add_comm_group M] :=
right_semimodule A M

namespace semiring

instance (A : Type*) [semiring A] : right_semimodule A A :=
{ smul := λ a b, b * a.unop,
  one_smul := by simp,
  mul_smul := by simp [mul_assoc],
  smul_add := by simp [add_mul],
  smul_zero := by simp,
  add_smul := by simp [mul_add],
  zero_smul := by simp }

end semiring

notation m ` •ᵣ `:72 a:72 := (opposite.op a) • m

@[simp] lemma rsmul_eq_mul {A : Type*} [semiring A] {a b : A} : a •ᵣ b = a * b := smul_eq_mul

abbreviation bisemimodule (A : Type*) (B : Type*) (M : Type*)
  [semiring A] [semiring B] [add_comm_monoid M] [semimodule A M] [right_semimodule B M] :=
smul_comm_class A (opposite B) M

abbreviation bimodule (A : Type*) (B : Type*) (M : Type*)
  [ring A] [ring B] [add_comm_group M] [module A M] [right_module B M] :=
bisemimodule A B M

namespace semiring

instance (A : Type*) [semiring A] : bisemimodule A A A :=
⟨λ a b c, by { change _ * (_ * _ ) = _, rw ←mul_assoc, refl }⟩

end semiring

variables {A : Type*} [semiring A] {B : Type*} [semiring B] {M : Type*} [add_comm_monoid M]
variables [semimodule A M] [right_semimodule B M]

example {a1 a2 : A} {b1 b2 : B} {m1 m2 : M} :
  a1 •ᵣ a2 = a1 * a2 := by simp
