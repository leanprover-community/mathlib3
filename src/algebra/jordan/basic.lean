/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import algebra.ring.basic
import algebra.lie.of_associative
import data.real.basic

/-!
# Jordan algebras

We define a set of conditions, formulated in terms of commuting multiplication operators, for the
multiplication on a non-unital, non-associative semiring to be a Jordan multiplication. When the
multiplication is commutative, these take a particularly simple form.

## Main results

- lin_jordan : Liniarisation of the commutative Jordan axiom
-/

set_option old_structure_cmd true

/-- A not-necessarily-unital, not-necessarily-associative ring. -/
@[protect_proj, ancestor add_comm_group non_unital_non_assoc_semiring ]
class non_unital_non_assoc_ring (α : Type*) extends
  add_comm_group α, non_unital_non_assoc_semiring α

variables {A : Type*}

@[priority 100] -- see Note [lower instance priority]
instance ring.to_non_unital_non_assoc_semiring (B :Type*) [_i : ring B] :
  non_unital_non_assoc_ring B :=
{ zero_mul := zero_mul,
  mul_zero := mul_zero,
  .. _i }

variables [non_unital_non_assoc_ring A]

-- For some reason `def T : A→+add_monoid.End A := add_monoid_hom.mul` doesn't work here?
/--
Left multiplication operator
-/
@[simps] def T : A→+add_monoid.End A :=
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

lemma T_def (a b : A) : T a b = a*b := rfl

lemma R_def (a b : A) : R a b = b*a := rfl

/--
A non unital, non-associative ring with a (non-commutative) Jordan multipication
-/
class jordan (A : Type*) [non_unital_non_assoc_ring A] :=
(commL1R1: ∀ a : A, ⁅T a, R a⁆ = 0)
(commL1L2: ∀ a : A, ⁅T a, T (a*a)⁆ = 0)
(commL1R2: ∀ a : A, ⁅T a, R (a*a)⁆ = 0)
(commL2R1: ∀ a : A, ⁅T (a*a), R a⁆ = 0)
(commR1R2: ∀ a : A, ⁅R a, R (a*a)⁆ = 0)

universe u

@[priority 100] -- see Note [lower instance priority]
instance  ring_jordan (B : Type u) [ring B] : jordan (B) :=
{ commL1R1 := begin
    intro,
    ext b,
    rw ring.lie_def,
    simp only [add_monoid_hom.coe_mul_right, add_monoid_hom.zero_apply, add_monoid_hom.coe_mul_left,
      add_monoid_hom.sub_apply, function.comp_app, T_apply, R_apply, add_monoid.coe_mul],
    rw [mul_assoc, sub_self],
  end,
  commL1L2 := begin
    intro,
    ext b,
    rw ring.lie_def,
    simp only [add_monoid_hom.zero_apply, comp_mul_left, add_monoid_hom.coe_mul_left,
      add_monoid_hom.sub_apply, T_apply,      add_monoid.coe_mul],
    rw [← mul_assoc, sub_self],
  end,
  commL1R2 := begin
    intro,
    ext b,
    rw ring.lie_def,
    simp only [add_monoid_hom.coe_mul_right, add_monoid_hom.zero_apply, add_monoid_hom.coe_mul_left,
      add_monoid_hom.sub_apply, function.comp_app, T_apply, R_apply, add_monoid.coe_mul],
    rw [mul_assoc, sub_self],
  end,
  commL2R1 := begin
    intro,
    ext b,
    rw ring.lie_def,
    simp only [add_monoid_hom.coe_mul_right, add_monoid_hom.zero_apply, add_monoid_hom.coe_mul_left,
      add_monoid_hom.sub_apply, function.comp_app, T_apply, R_apply, add_monoid.coe_mul],
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
(comm: ∀ a : A, R a = T a) -- Can we reduce this to `R = T`?
(jordan: ∀ a : A, ⁅T a, T (a*a)⁆ = 0)

-- A (commutative) Jordan multiplication is also a Jordan multipication
@[priority 100] -- see Note [lower instance priority]
instance comm_jordan_is_jordan [comm_jordan A] : jordan A :=
{ commL1R1 := λ _, by rw [comm_jordan.comm, lie_self],
  commL1L2 := λ _, by rw comm_jordan.jordan,
  commL1R2 := λ _, by rw [comm_jordan.comm, comm_jordan.jordan],
  commL2R1 :=  λ _, by rw [comm_jordan.comm, ←lie_skew, comm_jordan.jordan, neg_zero],
  commR1R2 := λ _, by rw [comm_jordan.comm, comm_jordan.comm, comm_jordan.jordan], }

variable [comm_jordan A]

lemma jordan_mul_comm (a b :A) : a*b = b*a := by rw [← T_def, ← R_def, comm_jordan.comm]

lemma mul_op_com1 (a b : A) :
  ⁅T a, T (b*b)⁆ + ⁅T b, T (a*a)⁆ + (2:ℤ)•⁅T a, T (a*b)⁆ + (2:ℤ)•⁅T b, T (a*b)⁆  = 0 :=
begin
  symmetry,
  calc 0 = ⁅T (a+b), T ((a+b)*(a+b))⁆ : by rw comm_jordan.jordan
    ... = ⁅T (a+b), T (a*(a+b)+b*(a+b))⁆ : by rw add_mul
    ... = ⁅T (a+b), T (a*a+a*b+(b*a+b*b))⁆ : by rw [mul_add, mul_add]
    ... = ⁅T a + T b, T (a*a+a*b+(b*a+b*b))⁆ : by rw map_add
    ... = ⁅T a + T b, T (a*a) + T(a*b) + T(b*a+b*b)⁆ : by rw [map_add, map_add]
    ... = ⁅T a + T b, T (a*a) + T(a*b) + (T(b*a) + T(b*b))⁆ : by rw map_add
    ... = ⁅T a + T b, T (a*a) + T(a*b) + (T(a*b) + T(b*b))⁆ : by rw jordan_mul_comm b a
    ... = ⁅T a + T b, T (a*a) + (2:ℤ)•T(a*b) + T(b*b)⁆ : by abel
    ... = ⁅T a, T (a*a) + (2:ℤ)•T(a*b) + T(b*b)⁆ + ⁅T b, T (a*a) + (2:ℤ)•T(a*b) + T(b*b)⁆ :
      by rw add_lie
    ... = ⁅T a, T(a*a)⁆ + ⁅T a, (2:ℤ)•T(a*b)⁆ + ⁅T a, T(b*b)⁆
      + ⁅T b, T(a*a) + (2:ℤ)•T(a*b) + T(b*b)⁆ : by rw [lie_add, lie_add]
    ... = ⁅T a, T (a*a)⁆ + ⁅T a, (2:ℤ)•T(a*b)⁆ + ⁅T a, T(b*b)⁆
      + (⁅T b, T (a*a)⁆ + ⁅T b,(2:ℤ)•T(a*b)⁆ + ⁅T b,T(b*b)⁆) : by rw [lie_add, lie_add]
    ... = 0 + ⁅T a, (2:ℤ)•T(a*b)⁆ + ⁅T a, T(b*b)⁆ + (⁅T b, T (a*a)⁆ + ⁅T b,(2:ℤ)•T(a*b)⁆ + 0) :
      by rw [comm_jordan.jordan, comm_jordan.jordan]
    ... = 0 + (2:ℤ)•⁅T a, T(a*b)⁆ + ⁅T a, T(b*b)⁆ + (⁅T b, T (a*a)⁆ + (2:ℤ)•⁅T b,T(a*b)⁆ + 0) :
      by rw [lie_smul, lie_smul]
    ... = (2:ℤ)•⁅T a, T(a*b)⁆ + ⁅T a, T(b*b)⁆ + (⁅T b, T (a*a)⁆ + (2:ℤ)•⁅T b,T(a*b)⁆) :
      by rw [zero_add, add_zero]
    ... = ⁅T a, T (b*b)⁆ + ⁅T b, T (a*a)⁆ + (2:ℤ)•⁅T a, T (a*b)⁆ + (2:ℤ)•⁅T b, T (a*b)⁆: by abel
end

lemma lin_jordan (a b c : A) : (2:ℤ)•(⁅T a, T (b*c)⁆ + ⁅T b, T (a*c)⁆ + ⁅T c, T (a*b)⁆) = 0 :=
begin
  symmetry,
  calc 0 = ⁅T (a+b+c), T ((a+b+c)*(a+b+c))⁆ : by rw comm_jordan.jordan
  ... = ⁅T (a+b+c), T (a*(a+b+c)+b*(a+b+c)+c*(a+b+c))⁆ : by rw [add_mul, add_mul]
  ... = ⁅T (a+b+c), T (a*a+a*b+a*c+(b*a+b*b+b*c)+(c*a+c*b+c*c))⁆ :
    by rw [mul_add, mul_add, mul_add, mul_add, mul_add, mul_add]
  ... = ⁅T a + T b + T c, T (a*a+a*b+a*c+(b*a+b*b+b*c)+(c*a+c*b+c*c))⁆ : by rw [map_add, map_add]
  ... = ⁅T a + T b + T c, T (a*a) + T(a*b) + T(a*c) + T(b*a+b*b+b*c) + T(c*a+c*b+c*c)⁆ :
    by rw [map_add, map_add, map_add, map_add]
  ... = ⁅T a + T b + T c,
    T (a*a) + T(a*b) + T(a*c) + (T(b*a) + T(b*b) + T(b*c)) + (T(c*a) + T(c*b) + T(c*c))⁆ :
    by rw [map_add, map_add, map_add, map_add]
  ... = ⁅T a + T b + T c,
    T (a*a) + T(a*b) + T(a*c) + (T(a*b) + T(b*b) + T(b*c)) + (T(a*c) + T(b*c) + T(c*c))⁆ :
    by rw [jordan_mul_comm b a, jordan_mul_comm c a, jordan_mul_comm c b]
  ... = ⁅T a + T b + T c, T(a*a) + T(b*b) + T(c*c) + (2:ℤ)•T(a*b) + (2:ℤ)•T(a*c) + (2:ℤ)•T(b*c) ⁆ :
    by abel
  ... = ⁅T a, T(a*a) + T(b*b) + T(c*c) + (2:ℤ)•T(a*b) + (2:ℤ)•T(a*c) + (2:ℤ)•T(b*c) ⁆
        + ⁅T b, T(a*a) + T(b*b) + T(c*c) + (2:ℤ)•T(a*b) + (2:ℤ)•T(a*c) + (2:ℤ)•T(b*c)⁆
        + ⁅T c, T(a*a) + T(b*b) + T(c*c) + (2:ℤ)•T(a*b) + (2:ℤ)•T(a*c) + (2:ℤ)•T(b*c)⁆ :
    by rw [add_lie, add_lie]
  ... = ⁅T a, T(a*a)⁆ + ⁅T a, T(b*b)⁆ + ⁅T a, T(c*c)⁆ + ⁅T a, (2:ℤ)•T(a*b)⁆ + ⁅T a, (2:ℤ)•T(a*c)⁆
    + ⁅T a, (2:ℤ)•T(b*c)⁆
        + ⁅T b, T(a*a) + T(b*b) + T(c*c) + (2:ℤ)•T(a*b) + (2:ℤ)•T(a*c) + (2:ℤ)•T(b*c)⁆
        + ⁅T c, T(a*a) + T(b*b) + T(c*c) + (2:ℤ)•T(a*b) + (2:ℤ)•T(a*c) + (2:ℤ)•T(b*c)⁆ :
    by rw [lie_add, lie_add, lie_add, lie_add, lie_add]
  ... = ⁅T a, T(a*a)⁆ + ⁅T a, T(b*b)⁆ + ⁅T a, T(c*c)⁆ + ⁅T a, (2:ℤ)•T(a*b)⁆ + ⁅T a, (2:ℤ)•T(a*c)⁆
          + ⁅T a, (2:ℤ)•T(b*c)⁆
        + (⁅T b, T(a*a)⁆ + ⁅T b, T(b*b)⁆ + ⁅T b, T(c*c)⁆ + ⁅T b, (2:ℤ)•T(a*b)⁆
          + ⁅T b, (2:ℤ)•T(a*c)⁆ + ⁅T b, (2:ℤ)•T(b*c)⁆)
        + ⁅T c, T(a*a) + T(b*b) + T(c*c) + (2:ℤ)•T(a*b) + (2:ℤ)•T(a*c) + (2:ℤ)•T(b*c)⁆ :
          by rw [lie_add, lie_add, lie_add, lie_add, lie_add]
  ... = ⁅T a, T(a*a)⁆ + ⁅T a, T(b*b)⁆ + ⁅T a, T(c*c)⁆ + ⁅T a, (2:ℤ)•T(a*b)⁆ + ⁅T a, (2:ℤ)•T(a*c)⁆
          + ⁅T a, (2:ℤ)•T(b*c)⁆
        + (⁅T b, T(a*a)⁆ + ⁅T b, T(b*b)⁆ + ⁅T b, T(c*c)⁆ + ⁅T b, (2:ℤ)•T(a*b)⁆
          + ⁅T b, (2:ℤ)•T(a*c)⁆ + ⁅T b, (2:ℤ)•T(b*c)⁆)
        + (⁅T c, T(a*a)⁆ + ⁅T c, T(b*b)⁆ + ⁅T c, T(c*c)⁆ + ⁅T c, (2:ℤ)•T(a*b)⁆
          + ⁅T c, (2:ℤ)•T(a*c)⁆ + ⁅T c, (2:ℤ)•T(b*c)⁆) :
    by rw [lie_add, lie_add, lie_add, lie_add, lie_add]
  ... = 0 + ⁅T a, T(b*b)⁆ + ⁅T a, T(c*c)⁆ + ⁅T a, (2:ℤ)•T(a*b)⁆ + ⁅T a, (2:ℤ)•T(a*c)⁆
          + ⁅T a, (2:ℤ)•T(b*c)⁆
        + (⁅T b, T(a*a)⁆ + 0 + ⁅T b, T(c*c)⁆ + ⁅T b, (2:ℤ)•T(a*b)⁆ + ⁅T b, (2:ℤ)•T(a*c)⁆
          + ⁅T b, (2:ℤ)•T(b*c)⁆)
        + (⁅T c, T(a*a)⁆ + ⁅T c, T(b*b)⁆ + 0 + ⁅T c, (2:ℤ)•T(a*b)⁆ + ⁅T c, (2:ℤ)•T(a*c)⁆
          + ⁅T c, (2:ℤ)•T(b*c)⁆) :
    by rw [comm_jordan.jordan, comm_jordan.jordan, comm_jordan.jordan]
  ... = ⁅T a, T(b*b)⁆ + ⁅T a, T(c*c)⁆ + ⁅T a, (2:ℤ)•T(a*b)⁆ + ⁅T a, (2:ℤ)•T(a*c)⁆
          + ⁅T a, (2:ℤ)•T(b*c)⁆
        + (⁅T b, T(a*a)⁆ + ⁅T b, T(c*c)⁆ + ⁅T b, (2:ℤ)•T(a*b)⁆ + ⁅T b, (2:ℤ)•T(a*c)⁆
          + ⁅T b, (2:ℤ)•T(b*c)⁆)
        + (⁅T c, T(a*a)⁆ + ⁅T c, T(b*b)⁆ + ⁅T c, (2:ℤ)•T(a*b)⁆ + ⁅T c, (2:ℤ)•T(a*c)⁆
          + ⁅T c, (2:ℤ)•T(b*c)⁆) :
    by rw [zero_add, add_zero, add_zero]
  ... = ⁅T a, T(b*b)⁆ + ⁅T a, T(c*c)⁆ + (2:ℤ)•⁅T a, T(a*b)⁆ + (2:ℤ)•⁅T a, T(a*c)⁆
          + (2:ℤ)•⁅T a, T(b*c)⁆
        + (⁅T b, T(a*a)⁆ + ⁅T b, T(c*c)⁆ + (2:ℤ)•⁅T b, T(a*b)⁆ + (2:ℤ)•⁅T b, T(a*c)⁆
          + (2:ℤ)•⁅T b, T(b*c)⁆)
        + (⁅T c, T(a*a)⁆ + ⁅T c, T(b*b)⁆ + (2:ℤ)•⁅T c, T(a*b)⁆ + (2:ℤ)•⁅T c, T(a*c)⁆
          + (2:ℤ)•⁅T c, T(b*c)⁆) :
    by rw [lie_smul, lie_smul, lie_smul, lie_smul, lie_smul, lie_smul, lie_smul, lie_smul, lie_smul]
  ... = (⁅T a, T(b*b)⁆+ ⁅T b, T(a*a)⁆ + (2:ℤ)•⁅T a, T(a*b)⁆ + (2:ℤ)•⁅T b, T(a*b)⁆)
        + (⁅T a, T(c*c)⁆ + ⁅T c, T(a*a)⁆ + (2:ℤ)•⁅T a, T(a*c)⁆ + (2:ℤ)•⁅T c, T(a*c)⁆)
        + (⁅T b, T(c*c)⁆ + ⁅T c, T(b*b)⁆ + (2:ℤ)•⁅T b, T(b*c)⁆ + (2:ℤ)•⁅T c, T(b*c)⁆)
        + ((2:ℤ)•⁅T a, T(b*c)⁆ + (2:ℤ)•⁅T b, T(a*c)⁆ + (2:ℤ)•⁅T c, T(a*b)⁆) : by abel
  ... = 0
         + (⁅T a, T(c*c)⁆ + ⁅T c, T(a*a)⁆ + (2:ℤ)•⁅T a, T(a*c)⁆ + (2:ℤ)•⁅T c, T(a*c)⁆)
        + (⁅T b, T(c*c)⁆ + ⁅T c, T(b*b)⁆ + (2:ℤ)•⁅T b, T(b*c)⁆ + (2:ℤ)•⁅T c, T(b*c)⁆)
        + ((2:ℤ)•⁅T a, T(b*c)⁆ + (2:ℤ)•⁅T b, T(a*c)⁆ + (2:ℤ)•⁅T c, T(a*b)⁆) : by rw mul_op_com1
  ... = 0 + 0 + 0
        + ((2:ℤ)•⁅T a, T(b*c)⁆ + (2:ℤ)•⁅T b, T(a*c)⁆ + (2:ℤ)•⁅T c, T(a*b)⁆) :
    by rw [mul_op_com1, mul_op_com1]
  ... = (2:ℤ)•⁅T a, T(b*c)⁆ + (2:ℤ)•⁅T b, T(a*c)⁆ + (2:ℤ)•⁅T c, T(a*b)⁆ :
    by rw [zero_add, zero_add, zero_add]
  ... = (2:ℤ)•(⁅T a, T(b*c)⁆ + ⁅T b, T(a*c)⁆ + ⁅T c, T(a*b)⁆) : by rw [smul_add, smul_add]
end
