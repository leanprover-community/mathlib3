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

-- For some reason `def L : A→+add_monoid.End A := add_monoid_hom.mul` doesn't work here?
/--
Left multiplication operator
-/
@[simps] def L : A→+add_monoid.End A :=
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

/--
A non unital, non-associative ring with a (non-commutative) Jordan multipication
-/
class jordan (A : Type*) [non_unital_non_assoc_ring A] :=
(commL1R1: ∀ a : A, ⁅L a, R a⁆ = 0)
(commL1L2: ∀ a : A, ⁅L a, L (a*a)⁆ = 0)
(commL1R2: ∀ a : A, ⁅L a, R (a*a)⁆ = 0)
(commL2R1: ∀ a : A, ⁅L (a*a), R a⁆ = 0)
(commR1R2: ∀ a : A, ⁅R a, R (a*a)⁆ = 0)

@[priority 100] -- see Note [lower instance priority]
instance  ring_jordan (B : Type*) [ring B] : jordan (B) :=
{
  commL1R1 := begin
    intro,
    ext b,
    rw ring.lie_def,
    simp only [add_monoid_hom.coe_mul_right, add_monoid_hom.zero_apply, add_monoid_hom.coe_mul_left, add_monoid_hom.sub_apply,
      function.comp_app, L_apply, R_apply, add_monoid.coe_mul],
    rw [mul_assoc, sub_self],
  end,
  commL1L2 := begin
    intro,
    ext b,
    rw ring.lie_def,
    simp only [add_monoid_hom.zero_apply, comp_mul_left, add_monoid_hom.coe_mul_left, add_monoid_hom.sub_apply, L_apply,
      add_monoid.coe_mul],
    rw [← mul_assoc, sub_self],
  end,
  commL1R2 := begin
    intro,
    ext b,
    rw ring.lie_def,
    simp only [add_monoid_hom.coe_mul_right, add_monoid_hom.zero_apply, add_monoid_hom.coe_mul_left, add_monoid_hom.sub_apply,
      function.comp_app, L_apply, R_apply, add_monoid.coe_mul],
    rw [mul_assoc, sub_self],
  end,
  commL2R1 := begin
    intro,
    ext b,
    rw ring.lie_def,
    simp only [add_monoid_hom.coe_mul_right, add_monoid_hom.zero_apply, add_monoid_hom.coe_mul_left, add_monoid_hom.sub_apply,
      function.comp_app, L_apply, R_apply, add_monoid.coe_mul],
    rw [←mul_assoc, sub_self],
  end,
  commR1R2 := begin
    intro,
    ext b,
    rw ring.lie_def,
    simp only [add_monoid_hom.coe_mul_right, add_monoid_hom.zero_apply, comp_mul_right, add_monoid_hom.sub_apply, R_apply,
      add_monoid.coe_mul],
    rw [mul_assoc, sub_self],
  end,
}


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

lemma mul_op_com1 (a b : A) :
  ⁅L a, L (b*b)⁆ + ⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L a, L (a*b)⁆ + (2:ℤ)•⁅L b, L (a*b)⁆  = 0 :=
begin
  symmetry,
  calc 0 = ⁅L (a+b), L ((a+b)*(a+b))⁆ : by rw comm_jordan.jordan
    ... = ⁅L (a+b), L (a*(a+b)+b*(a+b))⁆ : by rw add_mul
    ... = ⁅L (a+b), L (a*a+a*b+(b*a+b*b))⁆ : by rw [mul_add, mul_add]
    ... = ⁅L a + L b, L (a*a+a*b+(b*a+b*b))⁆ : by rw map_add
    ... = ⁅L a + L b, L (a*a) + L(a*b) + L(b*a+b*b)⁆ : by rw [map_add, map_add]
    ... = ⁅L a + L b, L (a*a) + L(a*b) + (L(b*a) + L(b*b))⁆ : by rw map_add
    ... = ⁅L a + L b, L (a*a) + L(a*b) + (L(a*b) + L(b*b))⁆ : by rw jordan_mul_comm b a
    ... = ⁅L a + L b, L (a*a) + (2:ℤ)•L(a*b) + L(b*b)⁆ : by abel
    ... = ⁅L a, L (a*a) + (2:ℤ)•L(a*b) + L(b*b)⁆ + ⁅L b, L (a*a) + (2:ℤ)•L(a*b) + L(b*b)⁆ :
      by rw add_lie
    ... = ⁅L a, L(a*a)⁆ + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, L(b*b)⁆
      + ⁅L b, L(a*a) + (2:ℤ)•L(a*b) + L(b*b)⁆ : by rw [lie_add, lie_add]
    ... = ⁅L a, L (a*a)⁆ + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, L(b*b)⁆
      + (⁅L b, L (a*a)⁆ + ⁅L b,(2:ℤ)•L(a*b)⁆ + ⁅L b,L(b*b)⁆) : by rw [lie_add, lie_add]
    ... = 0 + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, L(b*b)⁆ + (⁅L b, L (a*a)⁆ + ⁅L b,(2:ℤ)•L(a*b)⁆ + 0) :
      by rw [comm_jordan.jordan, comm_jordan.jordan]
    ... = 0 + (2:ℤ)•⁅L a, L(a*b)⁆ + ⁅L a, L(b*b)⁆ + (⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L b,L(a*b)⁆ + 0) :
      by rw [lie_smul, lie_smul]
    ... = (2:ℤ)•⁅L a, L(a*b)⁆ + ⁅L a, L(b*b)⁆ + (⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L b,L(a*b)⁆) :
      by rw [zero_add, add_zero]
    ... = ⁅L a, L (b*b)⁆ + ⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L a, L (a*b)⁆ + (2:ℤ)•⁅L b, L (a*b)⁆: by abel
end

lemma lin_jordan (a b c : A) : (2:ℤ)•(⁅L a, L (b*c)⁆ + ⁅L b, L (a*c)⁆ + ⁅L c, L (a*b)⁆) = 0 :=
begin
  symmetry,
  calc 0 = ⁅L (a+b+c), L ((a+b+c)*(a+b+c))⁆ : by rw comm_jordan.jordan
  ... = ⁅L (a+b+c), L (a*(a+b+c)+b*(a+b+c)+c*(a+b+c))⁆ : by rw [add_mul, add_mul]
  ... = ⁅L (a+b+c), L (a*a+a*b+a*c+(b*a+b*b+b*c)+(c*a+c*b+c*c))⁆ :
    by rw [mul_add, mul_add, mul_add, mul_add, mul_add, mul_add]
  ... = ⁅L a + L b + L c, L (a*a+a*b+a*c+(b*a+b*b+b*c)+(c*a+c*b+c*c))⁆ : by rw [map_add, map_add]
  ... = ⁅L a + L b + L c, L (a*a) + L(a*b) + L (a*c) + L(b*a+b*b+b*c) + L(c*a+c*b+c*c)⁆ :
    by rw [map_add, map_add, map_add, map_add]
  ... = ⁅L a + L b + L c,
    L (a*a) + L(a*b) + L (a*c) + (L(b*a) + L(b*b) + L(b*c)) + (L(c*a) + L(c*b) + L(c*c))⁆ :
    by rw [map_add, map_add, map_add, map_add]
  ... = ⁅L a + L b + L c,
    L (a*a) + L(a*b) + L (a*c) + (L(a*b) + L(b*b) + L(b*c)) + (L(a*c) + L(b*c) + L(c*c))⁆ :
    by rw [jordan_mul_comm b a, jordan_mul_comm c a, jordan_mul_comm c b]
  ... = ⁅L a + L b + L c, L (a*a) + L(b*b) + L(c*c) + (2:ℤ)•L(a*b) + (2:ℤ)•L(a*c) + (2:ℤ)•L(b*c) ⁆ :
    by abel
  ... = ⁅L a, L (a*a) + L(b*b) + L(c*c) + (2:ℤ)•L(a*b) + (2:ℤ)•L(a*c) + (2:ℤ)•L(b*c) ⁆
        + ⁅L b, L (a*a) + L(b*b) + L(c*c) + (2:ℤ)•L(a*b) + (2:ℤ)•L(a*c) + (2:ℤ)•L(b*c)⁆
        + ⁅L c, L (a*a) + L(b*b) + L(c*c) + (2:ℤ)•L(a*b) + (2:ℤ)•L(a*c) + (2:ℤ)•L(b*c)⁆ :
    by rw [add_lie, add_lie]
  ... = ⁅L a, L (a*a)⁆ + ⁅L a, L(b*b)⁆ + ⁅L a, L(c*c)⁆ + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, (2:ℤ)•L(a*c)⁆
    + ⁅L a, (2:ℤ)•L(b*c)⁆
        + ⁅L b, L (a*a) + L(b*b) + L(c*c) + (2:ℤ)•L(a*b) + (2:ℤ)•L(a*c) + (2:ℤ)•L(b*c)⁆
        + ⁅L c, L (a*a) + L(b*b) + L(c*c) + (2:ℤ)•L(a*b) + (2:ℤ)•L(a*c) + (2:ℤ)•L(b*c)⁆ :
    by rw [lie_add, lie_add, lie_add, lie_add, lie_add]
  ... = ⁅L a, L (a*a)⁆ + ⁅L a, L(b*b)⁆ + ⁅L a, L(c*c)⁆ + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, (2:ℤ)•L(a*c)⁆
          + ⁅L a, (2:ℤ)•L(b*c)⁆
        + (⁅L b, L (a*a)⁆ + ⁅L b, L(b*b)⁆ + ⁅L b, L(c*c)⁆ + ⁅L b, (2:ℤ)•L(a*b)⁆
          + ⁅L b, (2:ℤ)•L(a*c)⁆ + ⁅L b, (2:ℤ)•L(b*c)⁆)
        + ⁅L c, L (a*a) + L(b*b) + L(c*c) + (2:ℤ)•L(a*b) + (2:ℤ)•L(a*c) + (2:ℤ)•L(b*c)⁆ :
          by rw [lie_add, lie_add, lie_add, lie_add, lie_add]
  ... = ⁅L a, L (a*a)⁆ + ⁅L a, L(b*b)⁆ + ⁅L a, L(c*c)⁆ + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, (2:ℤ)•L(a*c)⁆
          + ⁅L a, (2:ℤ)•L(b*c)⁆
        + (⁅L b, L (a*a)⁆ + ⁅L b, L(b*b)⁆ + ⁅L b, L(c*c)⁆ + ⁅L b, (2:ℤ)•L(a*b)⁆
          + ⁅L b, (2:ℤ)•L(a*c)⁆ + ⁅L b, (2:ℤ)•L(b*c)⁆)
        + (⁅L c, L (a*a)⁆ + ⁅L c, L(b*b)⁆ + ⁅L c, L(c*c)⁆ + ⁅L c, (2:ℤ)•L(a*b)⁆
          + ⁅L c, (2:ℤ)•L(a*c)⁆ + ⁅L c, (2:ℤ)•L(b*c)⁆) :
    by rw [lie_add, lie_add, lie_add, lie_add, lie_add]
  ... = 0 + ⁅L a, L(b*b)⁆ + ⁅L a, L(c*c)⁆ + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, (2:ℤ)•L(a*c)⁆
          + ⁅L a, (2:ℤ)•L(b*c)⁆
        + (⁅L b, L (a*a)⁆ + 0 + ⁅L b, L(c*c)⁆ + ⁅L b, (2:ℤ)•L(a*b)⁆ + ⁅L b, (2:ℤ)•L(a*c)⁆
          + ⁅L b, (2:ℤ)•L(b*c)⁆)
        + (⁅L c, L (a*a)⁆ + ⁅L c, L(b*b)⁆ + 0 + ⁅L c, (2:ℤ)•L(a*b)⁆ + ⁅L c, (2:ℤ)•L(a*c)⁆
          + ⁅L c, (2:ℤ)•L(b*c)⁆) :
    by rw [comm_jordan.jordan, comm_jordan.jordan, comm_jordan.jordan]
  ... = ⁅L a, L(b*b)⁆ + ⁅L a, L(c*c)⁆ + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, (2:ℤ)•L(a*c)⁆
          + ⁅L a, (2:ℤ)•L(b*c)⁆
        + (⁅L b, L (a*a)⁆ + ⁅L b, L(c*c)⁆ + ⁅L b, (2:ℤ)•L(a*b)⁆ + ⁅L b, (2:ℤ)•L(a*c)⁆
          + ⁅L b, (2:ℤ)•L(b*c)⁆)
        + (⁅L c, L (a*a)⁆ + ⁅L c, L(b*b)⁆ + ⁅L c, (2:ℤ)•L(a*b)⁆ + ⁅L c, (2:ℤ)•L(a*c)⁆
          + ⁅L c, (2:ℤ)•L(b*c)⁆) :
    by rw [zero_add, add_zero, add_zero]
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
  ... = 0
         + (⁅L a, L(c*c)⁆ + ⁅L c, L (a*a)⁆ + (2:ℤ)•⁅L a, L(a*c)⁆ + (2:ℤ)•⁅L c, L(a*c)⁆)
        + (⁅L b, L(c*c)⁆ + ⁅L c, L(b*b)⁆ + (2:ℤ)•⁅L b, L(b*c)⁆ + (2:ℤ)•⁅L c, L(b*c)⁆)
        + ((2:ℤ)•⁅L a, L(b*c)⁆ + (2:ℤ)•⁅L b, L(a*c)⁆ + (2:ℤ)•⁅L c, L(a*b)⁆) : by rw mul_op_com1
  ... = 0 + 0 + 0
        + ((2:ℤ)•⁅L a, L(b*c)⁆ + (2:ℤ)•⁅L b, L(a*c)⁆ + (2:ℤ)•⁅L c, L(a*b)⁆) :
    by rw [mul_op_com1, mul_op_com1]
  ... = (2:ℤ)•⁅L a, L(b*c)⁆ + (2:ℤ)•⁅L b, L(a*c)⁆ + (2:ℤ)•⁅L c, L(a*b)⁆ :
    by rw [zero_add, zero_add, zero_add]
  ... = (2:ℤ)•(⁅L a, L (b*c)⁆ + ⁅L b, L (a*c)⁆ + ⁅L c, L (a*b)⁆) : by rw [smul_add, smul_add]
end
