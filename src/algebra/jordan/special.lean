/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import algebra.jordan.basic

/-!
# Special Jordan algebras

A commutative multiplication on a real or complex space can be constructed from any multiplicaion by
"symmetrisation" i.e
```
a∘b = 1/2(ab+ba).
```
When the original multiplication is associative, the symmetrised algebra is a commutative Jordan
algebra. A commutative Jordan algebra which can be constructed in this way from an associative
multiplication is said to be a special Jordan algebra.

## Implementation notes

The approach taken here is inspired by algebra.opposites
-/

/--
The symmetrised algebra has the same underlying space as the original algebra.
-/
def sym_alg (α : Type*) : Type* := α

postfix `ˢʸᵐ`:std.prec.max_plus := sym_alg

namespace sym_alg

variables {α : Type*}

/-- The element of `sym_alg α` that represents `a : α`. -/
@[pp_nodot]
def sym : α → αˢʸᵐ := id

/-- The element of `α` represented by `x : αᵐᵒᵖ`. -/
@[pp_nodot]
def unsym : αˢʸᵐ → α := id

instance [inhabited α] : inhabited αˢʸᵐ := ⟨sym (default α)⟩

@[simp] lemma unsym_sym (x : α) : unsym (sym x) = x := rfl
@[simp] lemma sym_unsym (x : α) : sym (unsym x) = x := rfl


instance [has_add α] : has_add αˢʸᵐ :=
{ add := λ a b, sym (unsym a + unsym b) }

@[simp] lemma sym_add [has_add α] (a b : α) : sym (a + b) = sym a + sym b := rfl
@[simp] lemma unsym_add [has_add α] (x y : αˢʸᵐ) : unsym (x + y) = unsym x + unsym y := rfl


instance [has_neg α] : has_neg αˢʸᵐ :=
{ neg := λ a, sym ( -(unsym a)) }

instance {R : Type*} [has_scalar R α] : has_scalar R αˢʸᵐ :=
{ smul := λ r a, sym (r•(unsym a)) }

@[simp] lemma sym_smul {R : Type*} [has_scalar R α] (c : R) (a : α) : sym (c • a) = c • sym a := rfl

lemma add_smul (α : Type*) [ring α] [algebra ℝ α] (a:α) (r s : ℝ): (r+s)•a = (r•a +s•a)   :=
begin
  unfold algebra.smul_def',
  rw ← add_mul,
  simp only [map_add, ring_hom.to_fun_eq_coe],
end

lemma smul_add' (α : Type*) [ring α] [algebra ℝ α] (a b:α) (r : ℝ): r•(a+b) = r•a + r•b   :=
begin
  unfold algebra.smul_def',
  rw ← mul_add,
end

--variables [semiring α] [algebra ℝ α]


instance {α : Type*} [add_comm_group α] : add_comm_group (αˢʸᵐ) :=
{ zero := sym 0,
  add := λ a b, a+b,
  add_assoc := λ a b c : α, add_assoc a b c,
  add_comm := λ a b : α, add_comm a b,
  zero_add := λ a, zero_add (unsym a),
  add_zero := λ a, add_zero (unsym a),
  neg := λ a, sym ( -(unsym a)),
  add_left_neg := λ a, add_left_neg (unsym a), }


noncomputable instance (α : Type*) [ring α] [algebra ℝ α] : non_unital_non_assoc_ring (αˢʸᵐ) :=
{ zero := sym 0,
  add := λ a b, a+b,
  add_assoc := λ a b c : α, add_assoc a b c,
  add_comm := λ a b : α, add_comm a b,
  zero_add := λ a, zero_add (unsym a),
  add_zero := λ a, add_zero (unsym a),
  neg := λ a, -a,
  add_left_neg := λ a, add_left_neg (unsym a),
  mul := λ a b, (sym ((1/2:ℝ)•(unsym(a)*unsym(b)+unsym(b)*unsym(a)))),
  zero_mul := λ _, by simp,
  mul_zero :=  λ _, by simp,
  left_distrib := λ a b c, begin
    change (1/2:ℝ)•(unsym(a)*(unsym(b)+unsym(c))+(unsym(b)+unsym(c))*unsym(a)) =
      (1/2:ℝ)•(unsym(a)*unsym(b)+unsym(b)*unsym(a))+(1/2:ℝ)•(unsym(a)*unsym(c)+unsym(c)*unsym(a)),
    rw [mul_add, add_mul, smul_add, smul_add, smul_add, smul_add, smul_add],
    abel,
  end,
  right_distrib := λ a b c, begin
    change (1/2:ℝ)•((unsym(a)+unsym(b))*unsym(c)+unsym(c)*(unsym(a)+unsym(b))) =
      (1/2:ℝ)•(unsym(a)*unsym(c)+unsym(c)*unsym(a))+(1/2:ℝ)•(unsym(b)*unsym(c)+unsym(c)*unsym(b)),
    rw [mul_add, add_mul, smul_add, smul_add, smul_add, smul_add, smul_add],
    abel,
  end, }

end sym_alg
