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

Let `A` be a non-associative algebra (i.e. a module equipped with a bilinear multiplication
operation). Then `A` is said to be a (commutative) Jordan algebra if the multiplication is
commutative and satisfies a weak associativity law known as the Jordan Identity: for all `a` and `b`
in `A`,
```
(a * b) * a^2 = a * (b * a^2)
```
i.e. the operators of multiplication by `a` and `a^2` commute. Every associative algebra can be
equipped with a second  multiplication making it into a commutative Jordan algebra.
Jordan algebras arising this way are said to be special. There are also exceptional Jordan algebras
which can be shown not to be the symmetrisation of any associative algebra. The 3x3
matrices of octonions is the canonical example.

Commutative Jordan algebras were introduced by Jordan, von Neumann and Wigner
([jordanvonneumannwigner1934]) as a mathematical model for the observables of a quantum mechanical
physical system (for a C*-algebra the self-adjoint part is closed under the symmetrised Jordan
multiplication). Jordan algebras have subsequently been studied from the points of view of abstract
algebra and functional analysis. They have connections to Lie algebras and differential geometry.

A more general concept of a (non-commutative) Jordan algebra can also be defined, as a
(non-commutative, non-associative) algebra `A` where, for each `a` in `A`, the operators of left and
right multiplication by `a` and `a^2` commute. Such algebras have connected to the Vidav-Palmer
theorem [cabreragarciarodriguezpalacios2014].

A comprehensive overview of the algebraic theory can be found in [mccrimmon2004].

A real Jordan algebra `A` can be introduced by
```
variables {A : Type*} [non_unital_non_assoc_ring A] [module ℝ A] [smul_comm_class ℝ A A]
  [is_scalar_tower ℝ A A] [comm_jordan A]
```

## Main results

- `lin_jordan` : Linearisation of the commutative Jordan axiom

## Implementation notes

We shall primarily be interested in linear Jordan algebras (i.e. over rings of characteristic not
two) leaving quadratic algebras to those better versed in that theory.

The conventional way to linearise the Jordan axiom is to equate coefficients (more formally, assume
that the axiom holds in all field extensions). For simplicity we use brute force algebraic expansion
and substitution instead.

## References

* [Cabrera García and Rodríguez Palacios, Non-associative normed algebras. Volume 1]
  [cabreragarciarodriguezpalacios2014]
* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
* [Jordan, von Neumann and Wigner, 1934][jordanvonneumannwigner1934]
* [McCrimmon, A taste of Jordan algebras][mccrimmon2004]


-/

set_option old_structure_cmd true

section non_unital_non_assoc_ring

variables {A : Type*} [non_unital_non_assoc_semiring A]

namespace non_unital_non_assoc_ring
/--
Left multiplication operator
-/
@[simps] def L : A →+ add_monoid.End A := add_monoid_hom.mul

/--
Right multiplication operator
-/
@[simps] def R : A→+(add_monoid.End A) := add_monoid_hom.flip (L : A →+ add_monoid.End A)

lemma L_def (a b : A) : L a b = a*b := rfl

lemma R_def (a b : A) : R a b = b*a := rfl

end non_unital_non_assoc_ring

end non_unital_non_assoc_ring

open non_unital_non_assoc_ring
/--
A non unital, non-associative ring with a (non-commutative) Jordan multiplication.
-/
class jordan (A : Type*) [non_unital_non_assoc_ring A] :=
(commL1R1: ∀ a b : A, (a * b) * a = a * (b * a))
(commL1L2: ∀ a b : A, a * ((a * a) * b) = (a * a) * (a * b))
(commL1R2: ∀ a b : A, a* (b * (a * a)) = (a * b) * (a * a) )
(commL2R1: ∀ a b : A, (a * a) * (b * a) = ((a * a) * b) * a)
(commR1R2: ∀ a b : A, (b * (a * a)) * a = (b * a) * (a * a))

lemma jordan_operators (A : Type*) [non_unital_non_assoc_ring A] [jordan A] (a : A) :
(⁅L a, R a⁆ = 0) ∧ (⁅L a, L (a * a)⁆ = 0) ∧ (⁅L a, R (a * a)⁆ = 0) ∧ (⁅L (a * a), R a⁆ = 0) ∧
(⁅R a, R (a * a)⁆ = 0) :=
begin
  rw [ring.lie_def, ring.lie_def, ring.lie_def, ring.lie_def, ring.lie_def ],
  split,
  { ext b,
    simp only [add_monoid_hom.zero_apply, add_monoid_hom.sub_apply, function.comp_app,
      R_apply_apply, add_monoid.coe_mul, L_apply_apply],
    rw jordan.commL1R1, rw sub_self, },
  split,
  { ext b,
    simp only [add_monoid_hom.zero_apply, add_monoid_hom.sub_apply, function.comp_app,
      R_apply_apply, add_monoid.coe_mul, L_apply_apply],
    rw jordan.commL1L2, rw sub_self, },
  split,
  { ext b,
    simp only [add_monoid_hom.zero_apply, add_monoid_hom.sub_apply, function.comp_app,
      R_apply_apply, add_monoid.coe_mul, L_apply_apply],
    rw jordan.commL1R2, rw sub_self, },
  split,
  { ext b,
    simp only [add_monoid_hom.zero_apply, add_monoid_hom.sub_apply, function.comp_app,
      R_apply_apply, add_monoid.coe_mul, L_apply_apply],
    rw jordan.commL2R1, rw sub_self, },
  { ext b,
    simp only [add_monoid_hom.zero_apply, add_monoid_hom.sub_apply, function.comp_app,
      R_apply_apply, add_monoid.coe_mul, L_apply_apply],
    rw jordan.commR1R2, rw sub_self, },
end

universe u

/- A (unital, associative) ring satisfies the (non-commutative) Jordan axioms-/
@[priority 100] -- see Note [lower instance priority]
instance ring_jordan (B : Type u) [ring B] : jordan (B) :=
{ commL1R1 := by { intros, rw mul_assoc },
  commL1L2 := by { intros, [mul_assoc, mul_assoc] },
  commL1R2 := by { intros, rw [mul_assoc] },
  commL2R1 := by { intros, rw [←mul_assoc] },
  commR1R2 := by { intros, rw [← mul_assoc, ← mul_assoc] } }

variables (A : Type*) [non_unital_non_assoc_ring A]

/--
A non unital, non-associative ring with a commutative Jordan multipication
-/
class comm_jordan :=
(mul_comm: ∀ a b : A, a * b = b * a)
(jordan: ∀ a b : A, (a * b) * (a * a) = a * (b * (a *a)))

variable [comm_jordan A]

lemma comm_jordan_operators  {A : Type*} [non_unital_non_assoc_ring A] [comm_jordan A] :
  (∀ a: A, L a = R a) ∧ (∀ a: A, ⁅L a, L (a*a)⁆ = 0) :=
begin
  split,
  { intro, ext b, simp, rw mul_comm, },
  { intro,
    ext b,
    rw ring.lie_def,
    simp only [add_monoid_hom.zero_apply, add_monoid_hom.sub_apply, function.comp_app,
      add_monoid.coe_mul, L_apply_apply],
    rw [comm_jordan.comm (a * a) (a * b), comm_jordan.jordan, comm_jordan.comm b (a * a),
    sub_self], }
end

-- A (commutative) Jordan multiplication is also a Jordan multipication
@[priority 100] -- see Note [lower instance priority]
instance comm_jordan_is_jordan : jordan A :=
{ commL1R1 := λ a b, by rw [comm_jordan.comm, comm_jordan.comm a b],
  commL1L2 := λ a b, by rw [comm_jordan.comm (a * a) (a * b), comm_jordan.jordan,
    comm_jordan.comm b (a * a)],
  commL1R2 := λ a b, by rw [comm_jordan.comm, comm_jordan.jordan, comm_jordan.comm],
  commL2R1 :=  λ a b, by rw [comm_jordan.comm (a * a) (b * a), comm_jordan.comm b a,
    comm_jordan.jordan, comm_jordan.comm, comm_jordan.comm b (a * a)],
  commR1R2 := λ a b, by rw [comm_jordan.comm b a, comm_jordan.jordan, comm_jordan.comm], }

/- Linearise the Jordan axiom with two variables-/
lemma mul_op_com1 (a b : A) :
  ⁅L a, L (b*b)⁆ + ⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L a, L (a*b)⁆ + (2:ℤ)•⁅L b, L (a*b)⁆  = 0 :=
begin
  symmetry,
  calc 0 = ⁅L (a+b), L ((a+b)*(a+b))⁆ : by rw (comm_jordan_operators.2 (a + b))
    ... = ⁅L a + L b, L (a*a+a*b+(b*a+b*b))⁆ : by rw [add_mul, mul_add, mul_add, map_add]
    ... = ⁅L a + L b, L (a*a) + L(a*b) + (L(a*b) + L(b*b))⁆ :
      by rw [map_add, map_add, map_add, comm_jordan.comm b a]
    ... = ⁅L a + L b, L (a*a) + (2:ℤ)•L(a*b) + L(b*b)⁆ : by abel
    ... = ⁅L a, L (a*a)⁆ + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, L(b*b)⁆
      + (⁅L b, L (a*a)⁆ + ⁅L b,(2:ℤ)•L(a*b)⁆ + ⁅L b,L(b*b)⁆) :
        by rw [add_lie, lie_add, lie_add, lie_add, lie_add]
    ... = (2:ℤ)•⁅L a, L(a*b)⁆ + ⁅L a, L(b*b)⁆ + (⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L b,L(a*b)⁆) :
      by rw [comm_jordan_operators.2 a, comm_jordan_operators.2 b, lie_smul, lie_smul, zero_add,
        add_zero]
    ... = ⁅L a, L (b*b)⁆ + ⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L a, L (a*b)⁆ + (2:ℤ)•⁅L b, L (a*b)⁆: by abel
end

/- Linearise the Jordan axiom with three variables-/
lemma lin_jordan (a b c : A) : (2:ℤ)•(⁅L a, L (b*c)⁆ + ⁅L b, L (a*c)⁆ + ⁅L c, L (a*b)⁆) = 0 :=
begin
  symmetry,
  calc 0 = ⁅L (a+b+c), L ((a+b+c)*(a+b+c))⁆ : by rw (comm_jordan_operators.2 (a + b + c))
  ... = ⁅L a + L b + L c,
    L (a*a) + L(a*b) + L (a*c) + (L(b*a) + L(b*b) + L(b*c)) + (L(c*a) + L(c*b) + L(c*c))⁆ :
    by rw [add_mul, add_mul, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add,
      map_add, map_add, map_add, map_add, map_add, map_add, map_add, map_add, map_add, map_add]
  ... = ⁅L a + L b + L c,
    L (a*a) + L(a*b) + L (a*c) + (L(a*b) + L(b*b) + L(b*c)) + (L(a*c) + L(b*c) + L(c*c))⁆ :
    by rw [comm_jordan.comm b a, comm_jordan.comm c a, comm_jordan.comm c b]
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
    by rw [comm_jordan_operators.2 a, comm_jordan_operators.2 b, comm_jordan_operators.2 c,
      zero_add, add_zero, add_zero]
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
