/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.group.defs
import data.equiv.basic
import logic.nontrivial

/-!
# Multiplicative opposite and algebraic operations on it

In this file we define `mul_opposite α = αᵐᵒᵖ` to be the multiplicative opposite of `α`. It
inherits all additive algebraic structures on `α` (in other files), and reverses the order of
multipliers in multiplicative structures, i.e., `op (x * y) = op x * op y`, where `mul_opposite.op`
is the canonical map from `α` to `αᵐᵒᵖ`.

## Notation

`αᵐᵒᵖ = mul_opposite α`
-/

universes u v
open function

/-- Multiplicative opposite of a type. This type inherits all additive structures on `α` and
reverses left and right in multiplication.-/
def mul_opposite (α : Type u) : Type u := α

postfix `ᵐᵒᵖ`:std.prec.max_plus := mul_opposite

namespace mul_opposite

variables {α : Type u}

/-- The element of `mul_opposite α` that represents `x : α`. -/
@[pp_nodot]
def op : α → αᵐᵒᵖ := id

/-- The element of `α` represented by `x : αᵐᵒᵖ`. -/
@[pp_nodot]
def unop : αᵐᵒᵖ → α := id

@[simp] lemma unop_op (x : α) : unop (op x) = x := rfl
@[simp] lemma op_unop (x : αᵐᵒᵖ) : op (unop x) = x := rfl
@[simp] lemma op_comp_unop : (op : α → αᵐᵒᵖ) ∘ unop = id := rfl
@[simp] lemma unop_comp_op : (unop : αᵐᵒᵖ → α) ∘ op = id := rfl

attribute [irreducible] mul_opposite

/-- A recursor for `opposite`. Use as `induction x using mul_opposite.rec`. -/
@[simp]
protected def rec {F : Π (X : αᵐᵒᵖ), Sort v} (h : Π X, F (op X)) : Π X, F X :=
λ X, h (unop X)

/-- The canonical bijection between `αᵐᵒᵖ` and `α`. -/
@[simps apply symm_apply { fully_applied := ff }]
def op_equiv : α ≃ αᵐᵒᵖ := ⟨op, unop, unop_op, op_unop⟩

lemma op_bijective : bijective (op : α → αᵐᵒᵖ) := op_equiv.bijective
lemma unop_bijective : bijective (unop : αᵐᵒᵖ → α) := op_equiv.symm.bijective
lemma op_injective : injective (op : α → αᵐᵒᵖ) := op_bijective.injective
lemma op_surjective : surjective (op : α → αᵐᵒᵖ) := op_bijective.surjective
lemma unop_injective : injective (unop : αᵐᵒᵖ → α) := unop_bijective.injective
lemma unop_surjective : surjective (unop : αᵐᵒᵖ → α) := unop_bijective.surjective

@[simp] lemma op_inj {x y : α} : op x = op y ↔ x = y := op_injective.eq_iff
@[simp] lemma unop_inj {x y : αᵐᵒᵖ} : unop x = unop y ↔ x = y := unop_injective.eq_iff

variable (α)

instance [nontrivial α] : nontrivial αᵐᵒᵖ := op_injective.nontrivial
instance [inhabited α] : inhabited αᵐᵒᵖ := ⟨op (default α)⟩
instance [subsingleton α] : subsingleton αᵐᵒᵖ := unop_injective.subsingleton
instance [unique α] : unique αᵐᵒᵖ := unique.mk' _
instance [is_empty α] : is_empty αᵐᵒᵖ := function.is_empty unop

instance [has_zero α] : has_zero αᵐᵒᵖ := { zero := op 0 }

instance [has_one α] : has_one αᵐᵒᵖ := { one := op 1 }

instance [has_add α] : has_add αᵐᵒᵖ :=
{ add := λ x y, op (unop x + unop y) }

instance [has_sub α] : has_sub αᵐᵒᵖ :=
{ sub := λ x y, op (unop x - unop y) }

instance [has_neg α] : has_neg αᵐᵒᵖ :=
{ neg := λ x, op $ -(unop x) }

instance [has_mul α] : has_mul αᵐᵒᵖ :=
{ mul := λ x y, op (unop y * unop x) }

instance [has_inv α] : has_inv αᵐᵒᵖ :=
{ inv := λ x, op $ (unop x)⁻¹ }

instance (R : Type*) [has_scalar R α] : has_scalar R αᵐᵒᵖ :=
{ smul := λ c x, op (c • unop x) }

section
variables (α)

@[simp] lemma op_zero [has_zero α] : op (0 : α) = 0 := rfl
@[simp] lemma unop_zero [has_zero α] : unop (0 : αᵐᵒᵖ) = 0 := rfl

@[simp] lemma op_one [has_one α] : op (1 : α) = 1 := rfl
@[simp] lemma unop_one [has_one α] : unop (1 : αᵐᵒᵖ) = 1 := rfl

variable {α}

@[simp] lemma op_add [has_add α] (x y : α) : op (x + y) = op x + op y := rfl
@[simp] lemma unop_add [has_add α] (x y : αᵐᵒᵖ) : unop (x + y) = unop x + unop y := rfl

@[simp] lemma op_neg [has_neg α] (x : α) : op (-x) = -op x := rfl
@[simp] lemma unop_neg [has_neg α] (x : αᵐᵒᵖ) : unop (-x) = -unop x := rfl

@[simp] lemma op_mul [has_mul α] (x y : α) : op (x * y) = op y * op x := rfl
@[simp] lemma unop_mul [has_mul α] (x y : αᵐᵒᵖ) : unop (x * y) = unop y * unop x := rfl

@[simp] lemma op_inv [has_inv α] (x : α) : op (x⁻¹) = (op x)⁻¹ := rfl
@[simp] lemma unop_inv [has_inv α] (x : αᵐᵒᵖ) : unop (x⁻¹) = (unop x)⁻¹ := rfl

@[simp] lemma op_sub [has_sub α] (x y : α) : op (x - y) = op x - op y := rfl
@[simp] lemma unop_sub [has_sub α] (x y : αᵐᵒᵖ) : unop (x - y) = unop x - unop y := rfl

@[simp] lemma op_smul {R : Type*} [has_scalar R α] (c : R) (a : α) : op (c • a) = c • op a := rfl
@[simp] lemma unop_smul {R : Type*} [has_scalar R α] (c : R) (a : αᵐᵒᵖ) :
  unop (c • a) = c • unop a := rfl

end

@[simp] lemma unop_eq_zero_iff {α} [has_zero α] (a : αᵐᵒᵖ) : a.unop = (0 : α) ↔ a = (0 : αᵐᵒᵖ) :=
unop_injective.eq_iff' rfl

@[simp] lemma op_eq_zero_iff {α} [has_zero α] (a : α) : op a = (0 : αᵐᵒᵖ) ↔ a = (0 : α) :=
op_injective.eq_iff' rfl

lemma unop_ne_zero_iff {α} [has_zero α] (a : αᵐᵒᵖ) : a.unop ≠ (0 : α) ↔ a ≠ (0 : αᵐᵒᵖ) :=
not_congr $ unop_eq_zero_iff a

lemma op_ne_zero_iff {α} [has_zero α] (a : α) : op a ≠ (0 : αᵐᵒᵖ) ↔ a ≠ (0 : α) :=
not_congr $ op_eq_zero_iff a

@[simp] lemma unop_eq_one_iff {α} [has_one α] (a : αᵐᵒᵖ) : a.unop = 1 ↔ a = 1 :=
unop_injective.eq_iff' rfl

@[simp] lemma op_eq_one_iff {α} [has_one α] (a : α) : op a = 1 ↔ a = 1 :=
op_injective.eq_iff' rfl

end mul_opposite
