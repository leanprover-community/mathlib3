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
operation). Then `A` is said to be a (commutative, linear) Jordan algebra if the multiplication is
commutative and satisfies a weak associativity law known as the Jordan Identity: for all `a` and `b`
in `A`,
```
(a * b) * a^2 = a * (b * a^2)
```
i.e. the operators of multiplication by `a` and `a^2` commute. Every associative algebra can be
equipped with a second  multiplication making it into a commutative Jordan algebra.
Jordan algebras arising this way are said to be special. There are also exceptional Jordan algebras
which can be shown not to be the symmetrization of any associative algebra. The 3x3
matrices of octonions is the canonical example.

Every Jordan algebra `A` has a triple product defined, for `a` `b` and `c` in `A` by
```
⦃a b c⦄ = (a * b) * c - (a * c) * b + a * (b * c).
```
Via this triple product Jordan algebras are related to a number of other mathematical structures:
Jordan triples, partial Jordan triples, Jordan pairs and quadratic Jordan algebras. In addition to
their considerable algebraic interest ([mccrimmon2004]) these structures have been shown to have
deep connections to mathematical physics, functional analysis and differential geometry. For more
information about these connections the interested reader is referred to [alfsenshultz2003],
[chu2012], [friedmanscarr2005], [iordanescu2003] and [upmeier1987].

A more general concept of a (non-commutative) Jordan algebra can also be defined, as a
(non-commutative, non-associative) algebra `A` where, for each `a` in `A`, the operators of left and
right multiplication by `a` and `a^2` commute. Such algebras have connections to the Vidav-Palmer
theorem [cabreragarciarodriguezpalacios2014].

A real Jordan algebra `A` can be introduced by
```
variables {A : Type*} [non_unital_non_assoc_ring A] [module ℝ A] [smul_comm_class ℝ A A]
  [is_scalar_tower ℝ A A] [is_comm_jordan A]
```

## Main results

- `two_lie_L_L_mul_add_lie_L_L_mul_add_lie_L_L_mul` : Linearisation of the commutative Jordan axiom

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
* [McCrimmon, A taste of Jordan algebras][mccrimmon2004]

-/

/-- A (non-commutative) Jordan multiplication. -/
class is_jordan (A : Type*) [has_mul A] :=
(lmul_comm_rmul : ∀ a b : A, (a * b) * a = a * (b * a))
(lmul_lmul_comm_lmul : ∀ a b : A, (a * a) * (a * b) = a * ((a * a) * b))
(lmul_lmul_comm_rmul : ∀ a b : A, (a * a) * (b * a) = ((a * a) * b) * a)
(lmul_comm_rmul_rmul : ∀ a b : A, (a * b) * (a * a) = a * (b * (a * a)))
(rmul_comm_rmul_rmul : ∀ a b : A, (b * a) * (a * a) = (b * (a * a)) * a)

/-- A commutative Jordan multipication -/
class is_comm_jordan (A : Type*) [has_mul A]:=
(mul_comm : ∀ a b : A, a * b = b * a)
(jordan : ∀ a b : A, (a * b) * (a * a) = a * (b * (a *a)))

-- A (commutative) Jordan multiplication is also a Jordan multipication
@[priority 100] -- see Note [lower instance priority]
instance is_comm_jordan.to_is_jordan (A : Type*) [has_mul A] [is_comm_jordan A] : is_jordan A :=
{ lmul_comm_rmul := λ a b, by rw [is_comm_jordan.mul_comm, is_comm_jordan.mul_comm a b],
  lmul_lmul_comm_lmul := λ a b, by rw [is_comm_jordan.mul_comm (a * a) (a * b),
    is_comm_jordan.jordan, is_comm_jordan.mul_comm b (a * a)],
  lmul_comm_rmul_rmul := λ a b, by rw [is_comm_jordan.mul_comm, ←is_comm_jordan.jordan,
    is_comm_jordan.mul_comm],
  lmul_lmul_comm_rmul :=  λ a b, by rw [is_comm_jordan.mul_comm (a * a) (b * a),
    is_comm_jordan.mul_comm b a, is_comm_jordan.jordan, is_comm_jordan.mul_comm,
    is_comm_jordan.mul_comm b (a * a)],
  rmul_comm_rmul_rmul := λ a b, by rw [is_comm_jordan.mul_comm b a, is_comm_jordan.jordan,
    is_comm_jordan.mul_comm], }

universe u

/-- Semigroup multiplication satisfies the (non-commutative) Jordan axioms-/
@[priority 100] -- see Note [lower instance priority]
instance semigroup.is_jordan (B : Type u) [semigroup B] : is_jordan B :=
{ lmul_comm_rmul := λ a b, by rw mul_assoc,
  lmul_lmul_comm_lmul := λ a b, by rw [mul_assoc, mul_assoc],
  lmul_comm_rmul_rmul := λ a b, by rw [mul_assoc],
  lmul_lmul_comm_rmul := λ a b, by rw [←mul_assoc],
  rmul_comm_rmul_rmul := λ a b, by rw [← mul_assoc, ← mul_assoc], }

@[priority 100] -- see Note [lower instance priority]
instance comm_semigroup.is_comm_jordan (B : Type u) [comm_semigroup B] : is_comm_jordan B :=
{ mul_comm := mul_comm,
  jordan := λ a b, mul_assoc _ _ _, }

variables {A : Type*}

namespace add_monoid.End
variables [non_unital_non_assoc_semiring A]

/-- Left multiplication operator. This is a variant of `add_monoid_hom.mul_left`. -/
@[simps] def L : A →+ add_monoid.End A := add_monoid_hom.mul

/-- Right multiplication operator. This is a variant of `add_monoid_hom.mul_right`. -/
@[simps] def R : A →+ add_monoid.End A := (L : A →+ add_monoid.End A).flip

end add_monoid.End

open add_monoid.End (L R)

/-! The Jordan axioms can be expressed in terms of commuting multiplication operators -/
section lie
variables [non_unital_non_assoc_ring A] [is_jordan A]

@[simp] lemma lie_L_R (a : A) : ⁅L a, R a⁆ = 0 :=
add_monoid_hom.ext $ λ b, sub_eq_zero_of_eq (is_jordan.lmul_comm_rmul _ _).symm

@[simp] lemma lie_L_L_sq (a : A) : ⁅L a, L (a * a)⁆ = 0 :=
add_monoid_hom.ext $ λ b, sub_eq_zero_of_eq (is_jordan.lmul_lmul_comm_lmul _ _).symm

@[simp] lemma lie_L_R_sq (a : A) : ⁅L a, R (a * a)⁆ = 0 :=
add_monoid_hom.ext $ λ b, sub_eq_zero_of_eq (is_jordan.lmul_comm_rmul_rmul _ _).symm

@[simp] lemma lie_L_sq_R (a : A) : ⁅L (a * a), R a⁆ = 0 :=
add_monoid_hom.ext $ λ b, sub_eq_zero_of_eq (is_jordan.lmul_lmul_comm_rmul _ _)

@[simp] lemma lie_R_R_sq (a : A) : ⁅R a, R (a * a)⁆ = 0 :=
add_monoid_hom.ext $ λ b, sub_eq_zero_of_eq (is_jordan.rmul_comm_rmul_rmul _ _).symm

end lie

variables [non_unital_non_assoc_ring A] [is_comm_jordan A]

/-- Linearise the operator form of the Jordan axiom (`lie_L_L_sq`) by substituting in a → a + b and
expanding. -/
lemma lie_L_L_sq_add_lie_L_L_sq_add_two_lie_L_L_mul_add_two_lie_L_L_mul (a b : A) :
  ⁅L a, L (b*b)⁆ + ⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L a, L (a*b)⁆ + (2:ℤ)•⁅L b, L (a*b)⁆ = 0 :=
begin
  symmetry,
  calc 0 = ⁅L (a+b), L ((a+b)*(a+b))⁆ : by rw (lie_L_L_sq (a + b))
    ... = ⁅L a + L b, L (a*a+a*b+(b*a+b*b))⁆ : by rw [add_mul, mul_add, mul_add, map_add]
    ... = ⁅L a + L b, L (a*a) + L(a*b) + (L(a*b) + L(b*b))⁆ :
      by rw [map_add, map_add, map_add, is_comm_jordan.mul_comm b a]
    ... = ⁅L a + L b, L (a*a) + (2:ℤ)•L(a*b) + L(b*b)⁆ : by abel
    ... = ⁅L a, L (a*a)⁆ + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, L(b*b)⁆
      + (⁅L b, L (a*a)⁆ + ⁅L b,(2:ℤ)•L(a*b)⁆ + ⁅L b,L(b*b)⁆) :
        by rw [add_lie, lie_add, lie_add, lie_add, lie_add]
    ... = (2:ℤ)•⁅L a, L(a*b)⁆ + ⁅L a, L(b*b)⁆ + (⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L b,L(a*b)⁆) :
      by rw [lie_L_L_sq a, lie_L_L_sq b, lie_smul, lie_smul,
        zero_add, add_zero]
    ... = ⁅L a, L (b*b)⁆ + ⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L a, L (a*b)⁆ + (2:ℤ)•⁅L b, L (a*b)⁆: by abel
end

/-- Linearise the operator form of the Jordan axiom (`lie_L_L_sq`) by substituting in a → a + b + c
and expanding. When the Jordan axiom holds in all scalar extensions of `A`, an alternative proof is
to substitute in a → a + λb + μc and equate coefficients of λμ.-/
lemma two_lie_L_L_mul_add_lie_L_L_mul_add_lie_L_L_mul (a b c : A) :
  (2:ℤ)•(⁅L a, L (b*c)⁆ + ⁅L b, L (a*c)⁆ + ⁅L c, L (a*b)⁆) = 0 :=
begin
  symmetry,
  calc 0 = ⁅L (a+b+c), L ((a+b+c)*(a+b+c))⁆ : by rw (lie_L_L_sq (a + b + c))
  ... = ⁅L a + L b + L c,
    L (a*a) + L(a*b) + L (a*c) + (L(b*a) + L(b*b) + L(b*c)) + (L(c*a) + L(c*b) + L(c*c))⁆ :
    by rw [add_mul, add_mul, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add,
      map_add, map_add, map_add, map_add, map_add, map_add, map_add, map_add, map_add, map_add]
  ... = ⁅L a + L b + L c,
    L (a*a) + L(a*b) + L (a*c) + (L(a*b) + L(b*b) + L(b*c)) + (L(a*c) + L(b*c) + L(c*c))⁆ :
    by rw [is_comm_jordan.mul_comm b a, is_comm_jordan.mul_comm c a,
      is_comm_jordan.mul_comm c b]
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
    by rw [lie_L_L_sq a, lie_L_L_sq b,
      lie_L_L_sq c, zero_add, add_zero, add_zero]
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
    by rw [lie_L_L_sq_add_lie_L_L_sq_add_two_lie_L_L_mul_add_two_lie_L_L_mul,
      lie_L_L_sq_add_lie_L_L_sq_add_two_lie_L_L_mul_add_two_lie_L_L_mul,
      lie_L_L_sq_add_lie_L_L_sq_add_two_lie_L_L_mul_add_two_lie_L_L_mul, zero_add, zero_add,
      zero_add]
  ... = (2:ℤ)•(⁅L a, L (b*c)⁆ + ⁅L b, L (a*c)⁆ + ⁅L c, L (a*b)⁆) : by rw [smul_add, smul_add]
end
