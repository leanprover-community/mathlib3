/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import algebra.ring.basic
import algebra.lie.of_associative
import data.real.basic
import linear_algebra.basic

/-!
# Jordan algebras

We define a set of conditions, formulated in terms of commuting multiplication operators, for the
multiplication on a non-unital, non-associative semiring to be a Jordan multiplication. When the
multiplication is commutative, these take a particularly simple form.

A real Jordan algebra `A` can be introduced by
```
variables {A : Type*} [non_unital_non_assoc_ring A] [module ℝ A] [smul_comm_class ℝ A A]
  [is_scalar_tower ℝ A A] [comm_jordan A]
```

## Main results

- lin_jordan : Linearisation of the commutative Jordan axiom

## Implementation notes

We shall primarily be interested in linear Jordan algebras (i.e. over rings of characteristic not
two) leaving quadratic algebras to those better versed in that theory.

The conventional way to linearise the Jordan axiom is to equate coefficients (more formally, assume
that the axiom holds in all field extensions). For simplicity we use brute force algebraic expansion
and substitution instead.

## References

* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
* [Cabrera García and Rodríguez Palacios, Non-associative normed algebras. Volume 1]
  [cabreragarciarodriguezpalacios2014]
-/

set_option old_structure_cmd true

variables {A : Type*} [non_unital_non_assoc_ring A]

namespace non_unital_non_assoc_ring
-- For some reason `def L : A→+add_monoid.End A := add_monoid_hom.mul` doesn't work here?
/--
Left multiplication operator
-/
@[simps] def L : A →+ add_monoid.End A :=
{ to_fun := add_monoid_hom.mul_left,
  map_zero' := add_monoid_hom.ext $ zero_mul,
  map_add' := λ a b, add_monoid_hom.ext $ add_mul a b }

/--
Right multiplication operator
-/
@[simps] def R : A→+(add_monoid.End A) :=
{ to_fun := add_monoid_hom.mul_right,
  map_zero' := add_monoid_hom.ext $ mul_zero,
  map_add' := λ a b, add_monoid_hom.ext $ λ c,
  begin
    simp,
    rw mul_add c a,
  end }

lemma L_def (a b : A) : L a b = a*b := rfl

lemma R_def (a b : A) : R a b = b*a := rfl

end non_unital_non_assoc_ring

open non_unital_non_assoc_ring
/--
A non unital, non-associative ring with a (non-commutative) Jordan multiplication.
-/
class jordan (A : Type*) [non_unital_non_assoc_ring A] :=
(commL1R1: ∀ a : A, ⁅L a, R a⁆ = 0)
(commL1L2: ∀ a : A, ⁅L a, L (a*a)⁆ = 0)
(commL1R2: ∀ a : A, ⁅L a, R (a*a)⁆ = 0)
(commL2R1: ∀ a : A, ⁅L (a*a), R a⁆ = 0)
(commR1R2: ∀ a : A, ⁅R a, R (a*a)⁆ = 0)

universe u

/- A (unital, associative) ring satisfies the (non-commutative) Jordan axioms-/
@[priority 100] -- see Note [lower instance priority]
instance ring_jordan (B : Type u) [ring B] : jordan (B) :=
{ commL1R1 := begin
    intro,
    ext b,
    rw ring.lie_def,
    simp only [add_monoid_hom.coe_mul_right, add_monoid_hom.zero_apply, add_monoid_hom.coe_mul_left,
      add_monoid_hom.sub_apply, function.comp_app, L_apply, R_apply, add_monoid.coe_mul],
    rw [mul_assoc, sub_self],
  end,
  commL1L2 := begin
    intro,
    ext b,
    rw ring.lie_def,
    simp only [add_monoid_hom.zero_apply, comp_mul_left, add_monoid_hom.coe_mul_left,
      add_monoid_hom.sub_apply, L_apply, add_monoid.coe_mul],
    rw [← mul_assoc, sub_self],
  end,
  commL1R2 := begin
    intro,
    ext b,
    rw ring.lie_def,
    simp only [add_monoid_hom.coe_mul_right, add_monoid_hom.zero_apply, add_monoid_hom.coe_mul_left,
      add_monoid_hom.sub_apply, function.comp_app, L_apply, R_apply, add_monoid.coe_mul],
    rw [mul_assoc, sub_self],
  end,
  commL2R1 := begin
    intro,
    ext b,
    rw ring.lie_def,
    simp only [add_monoid_hom.coe_mul_right, add_monoid_hom.zero_apply, add_monoid_hom.coe_mul_left,
      add_monoid_hom.sub_apply, function.comp_app, L_apply, R_apply, add_monoid.coe_mul],
    rw [←mul_assoc, sub_self],
  end,
  commR1R2 := begin
    intro,
    ext b,
    rw ring.lie_def,
    simp only [add_monoid_hom.coe_mul_right, add_monoid_hom.zero_apply, comp_mul_right,
      add_monoid_hom.sub_apply, R_apply, add_monoid.coe_mul],
    rw [mul_assoc, sub_self],
  end, }


/--
A non unital, non-associative ring with a commutative Jordan multipication
-/
class comm_jordan (A : Type*) [non_unital_non_assoc_ring A] :=
(comm: ∀ a : A, R a = L a) -- Can we reduce this to `R = L`?
(jordan: ∀ a : A, ⁅L a, L (a*a)⁆ = 0)

-- A (commutative) Jordan multiplication is also a Jordan multipication
@[priority 100] -- see Note [lower instance priority]
instance comm_jordan_is_jordan [comm_jordan A] : jordan A :=
{ commL1R1 := λ _, by rw [comm_jordan.comm, lie_self],
  commL1L2 := λ _, by rw comm_jordan.jordan,
  commL1R2 := λ _, by rw [comm_jordan.comm, comm_jordan.jordan],
  commL2R1 :=  λ _, by rw [comm_jordan.comm, ←lie_skew, comm_jordan.jordan, neg_zero],
  commR1R2 := λ _, by rw [comm_jordan.comm, comm_jordan.comm, comm_jordan.jordan], }

variable [comm_jordan A]

lemma jordan_mul_comm (a b :A) : a*b = b*a := by rw [← L_def, ← R_def, comm_jordan.comm]

/- Linearise the Jordan axiom with two variables-/
lemma mul_op_com1 (a b : A) :
  ⁅L a, L (b*b)⁆ + ⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L a, L (a*b)⁆ + (2:ℤ)•⁅L b, L (a*b)⁆  = 0 :=
begin
  symmetry,
  calc 0 = ⁅L (a+b), L ((a+b)*(a+b))⁆ : by rw comm_jordan.jordan
    ... = ⁅L a + L b, L (a*a+a*b+(b*a+b*b))⁆ : by rw [add_mul, mul_add, mul_add, map_add]
    ... = ⁅L a + L b, L (a*a) + L(a*b) + (L(a*b) + L(b*b))⁆ :
      by rw [map_add, map_add, map_add, jordan_mul_comm b a]
    ... = ⁅L a + L b, L (a*a) + (2:ℤ)•L(a*b) + L(b*b)⁆ : by abel
    ... = ⁅L a, L (a*a)⁆ + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, L(b*b)⁆
      + (⁅L b, L (a*a)⁆ + ⁅L b,(2:ℤ)•L(a*b)⁆ + ⁅L b,L(b*b)⁆) :
        by rw [add_lie, lie_add, lie_add, lie_add, lie_add]
    ... = (2:ℤ)•⁅L a, L(a*b)⁆ + ⁅L a, L(b*b)⁆ + (⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L b,L(a*b)⁆) :
      by rw [comm_jordan.jordan, comm_jordan.jordan, lie_smul, lie_smul, zero_add, add_zero]
    ... = ⁅L a, L (b*b)⁆ + ⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L a, L (a*b)⁆ + (2:ℤ)•⁅L b, L (a*b)⁆: by abel
end

/- Linearise the Jordan axiom with three variables-/
lemma lin_jordan (a b c : A) : (2:ℤ)•(⁅L a, L (b*c)⁆ + ⁅L b, L (a*c)⁆ + ⁅L c, L (a*b)⁆) = 0 :=
begin
  symmetry,
  calc 0 = ⁅L (a+b+c), L ((a+b+c)*(a+b+c))⁆ : by rw comm_jordan.jordan
  ... = ⁅L a + L b + L c,
    L (a*a) + L(a*b) + L (a*c) + (L(b*a) + L(b*b) + L(b*c)) + (L(c*a) + L(c*b) + L(c*c))⁆ :
    by rw [add_mul, add_mul, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add,
      map_add, map_add, map_add, map_add, map_add, map_add, map_add, map_add, map_add, map_add]
  ... = ⁅L a + L b + L c,
    L (a*a) + L(a*b) + L (a*c) + (L(a*b) + L(b*b) + L(b*c)) + (L(a*c) + L(b*c) + L(c*c))⁆ :
    by rw [jordan_mul_comm b a, jordan_mul_comm c a, jordan_mul_comm c b]
  ... = ⁅L a + L b + L c, L (a*a) + L(b*b) + L(c*c) + (2:ℤ)•L(a*b) + (2:ℤ)•L(a*c) + (2:ℤ)•L(b*c) ⁆ :
    by abel
  ... = ⁅L a, L (a*a)⁆ + ⁅L a, L(b*b)⁆ + ⁅L a, L(c*c)⁆ + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, (2:ℤ)•L(a*c)⁆
          + ⁅L a, (2:ℤ)•L(b*c)⁆
        + (⁅L b, L (a*a)⁆ + ⁅L b, L(b*b)⁆ + ⁅L b, L(c*c)⁆ + ⁅L b, (2:ℤ)•L(a*b)⁆
          + ⁅L b, (2:ℤ)•L(a*c)⁆ + ⁅L b, (2:ℤ)•L(b*c)⁆)
        + (⁅L c, L (a*a)⁆ + ⁅L c, L(b*b)⁆ + ⁅L c, L(c*c)⁆ + ⁅L c, (2:ℤ)•L(a*b)⁆
          + ⁅L c, (2:ℤ)•L(a*c)⁆ + ⁅L c, (2:ℤ)•L(b*c)⁆) :
    by rw [add_lie, add_lie, lie_add, lie_add, lie_add, lie_add, lie_add, lie_add, lie_add, lie_add,
     lie_add, lie_add, lie_add, lie_add, lie_add, lie_add, lie_add]
  ... = ⁅L a, L(b*b)⁆ + ⁅L a, L(c*c)⁆ + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, (2:ℤ)•L(a*c)⁆
          + ⁅L a, (2:ℤ)•L(b*c)⁆
        + (⁅L b, L (a*a)⁆ + ⁅L b, L(c*c)⁆ + ⁅L b, (2:ℤ)•L(a*b)⁆ + ⁅L b, (2:ℤ)•L(a*c)⁆
          + ⁅L b, (2:ℤ)•L(b*c)⁆)
        + (⁅L c, L (a*a)⁆ + ⁅L c, L(b*b)⁆ + ⁅L c, (2:ℤ)•L(a*b)⁆ + ⁅L c, (2:ℤ)•L(a*c)⁆
          + ⁅L c, (2:ℤ)•L(b*c)⁆) :
    by rw [comm_jordan.jordan, comm_jordan.jordan, comm_jordan.jordan, zero_add, add_zero, add_zero]
  ... = ⁅L a, L(b*b)⁆ + ⁅L a, L(c*c)⁆ + (2:ℤ)•⁅L a, L(a*b)⁆ + (2:ℤ)•⁅L a, L(a*c)⁆
          + (2:ℤ)•⁅L a, L(b*c)⁆
        + (⁅L b, L (a*a)⁆ + ⁅L b, L(c*c)⁆ + (2:ℤ)•⁅L b, L(a*b)⁆ + (2:ℤ)•⁅L b, L(a*c)⁆
          + (2:ℤ)•⁅L b, L(b*c)⁆)
        + (⁅L c, L (a*a)⁆ + ⁅L c, L(b*b)⁆ + (2:ℤ)•⁅L c, L(a*b)⁆ + (2:ℤ)•⁅L c, L(a*c)⁆
          + (2:ℤ)•⁅L c, L(b*c)⁆) :
    by rw [lie_smul, lie_smul, lie_smul, lie_smul, lie_smul, lie_smul, lie_smul, lie_smul, lie_smul]
  ... = (⁅L a, L(b*b)⁆+ ⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L a, L(a*b)⁆ + (2:ℤ)•⁅L b, L(a*b)⁆)
        + (⁅L a, L(c*c)⁆ + ⁅L c, L (a*a)⁆ + (2:ℤ)•⁅L a, L(a*c)⁆ + (2:ℤ)•⁅L c, L(a*c)⁆)
        + (⁅L b, L(c*c)⁆ + ⁅L c, L(b*b)⁆ + (2:ℤ)•⁅L b, L(b*c)⁆ + (2:ℤ)•⁅L c, L(b*c)⁆)
        + ((2:ℤ)•⁅L a, L(b*c)⁆ + (2:ℤ)•⁅L b, L(a*c)⁆ + (2:ℤ)•⁅L c, L(a*b)⁆) : by abel
  ... = (2:ℤ)•⁅L a, L(b*c)⁆ + (2:ℤ)•⁅L b, L(a*c)⁆ + (2:ℤ)•⁅L c, L(a*b)⁆ :
    by rw [mul_op_com1,mul_op_com1, mul_op_com1, zero_add, zero_add, zero_add]
  ... = (2:ℤ)•(⁅L a, L (b*c)⁆ + ⁅L b, L (a*c)⁆ + ⁅L c, L (a*b)⁆) : by rw [smul_add, smul_add]
end
