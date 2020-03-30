/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Type tags `multiplicative` and `additive` that turn additive structures into multiplicative, and vice versa
-/
import algebra.group.hom

universes u v
variables {α : Type u} {β : Type v}

def additive (α : Type*) := α
def multiplicative (α : Type*) := α

/-- Reinterpret `x : α` as an element of `additive α`. -/
def to_add (x : α) : additive α := x

/-- Reinterpret `x : additive α` as an element of `α`. -/
def of_add (x : additive α) : α := x

lemma of_add_inj : function.injective (@of_add α) := λ _ _, id
lemma to_add_inj : function.injective (@to_add α) := λ _ _, id

/-- Reinterpret `x : α` as an element of `multiplicative α`. -/
def to_mul (x : α) : multiplicative α := x

/-- Reinterpret `x : multiplicative α` as an element of `α`. -/
def of_mul (x : multiplicative α) : α := x

lemma of_mul_inj : function.injective (@of_mul α) := λ _ _, id
lemma to_mul_inj : function.injective (@to_mul α) := λ _ _, id

@[simp] lemma to_add_of_add (x : additive α) : to_add (of_add x) = x := rfl
@[simp] lemma of_add_to_add (x : α) : of_add (to_add x) = x := rfl

@[simp] lemma to_mul_of_mul (x : multiplicative α) : to_mul (of_mul x) = x := rfl
@[simp] lemma of_mul_to_mul (x : α) : of_mul (to_mul x) = x := rfl

instance [inhabited α] : inhabited (additive α) := ⟨to_add (default α)⟩
instance [inhabited α] : inhabited (multiplicative α) := ⟨to_mul (default α)⟩

instance additive.has_add [has_mul α] : has_add (additive α) :=
{ add := λ x y, to_add (of_add x * of_add y) }

instance [has_add α] : has_mul (multiplicative α) :=
{ mul := λ x y, to_mul (of_mul x + of_mul y) }

@[simp] lemma to_mul_add [has_add α] (x y : α) :
  to_mul (x + y) = to_mul x * to_mul y :=
rfl

@[simp] lemma of_mul_mul [has_add α] (x y : multiplicative α) :
  of_mul (x * y) = of_mul x + of_mul y :=
rfl

@[simp] lemma to_add_mul [has_mul α] (x y : α) :
  to_add (x * y) = to_add x + to_add y :=
rfl

@[simp] lemma of_add_add [has_mul α] (x y : additive α) :
  of_add (x + y) = of_add x * of_add y :=
rfl

instance [semigroup α] : add_semigroup (additive α) :=
{ add_assoc := @mul_assoc α _,
  ..additive.has_add }

instance [add_semigroup α] : semigroup (multiplicative α) :=
{ mul_assoc := @add_assoc α _,
  ..multiplicative.has_mul }

instance [comm_semigroup α] : add_comm_semigroup (additive α) :=
{ add_comm := @mul_comm _ _,
  ..additive.add_semigroup }

instance [add_comm_semigroup α] : comm_semigroup (multiplicative α) :=
{ mul_comm := @add_comm _ _,
  ..multiplicative.semigroup }

instance [left_cancel_semigroup α] : add_left_cancel_semigroup (additive α) :=
{ add_left_cancel := @mul_left_cancel _ _,
  ..additive.add_semigroup }

instance [add_left_cancel_semigroup α] : left_cancel_semigroup (multiplicative α) :=
{ mul_left_cancel := @add_left_cancel _ _,
  ..multiplicative.semigroup }

instance [right_cancel_semigroup α] : add_right_cancel_semigroup (additive α) :=
{ add_right_cancel := @mul_right_cancel _ _,
  ..additive.add_semigroup }

instance [add_right_cancel_semigroup α] : right_cancel_semigroup (multiplicative α) :=
{ mul_right_cancel := @add_right_cancel _ _,
  ..multiplicative.semigroup }

instance [has_one α] : has_zero (additive α) := ⟨to_add 1⟩

@[simp] lemma to_add_one [has_one α] : @to_add α 1 = 0 := rfl

@[simp] lemma of_add_zero [has_one α] : @of_add α 0 = 1 := rfl

instance [has_zero α] : has_one (multiplicative α) := ⟨to_mul 0⟩

@[simp] lemma to_mul_zero [has_zero α] : @to_mul α 0 = 1 := rfl

@[simp] lemma of_mul_one [has_zero α] : @of_mul α 1 = 0 := rfl

instance [monoid α] : add_monoid (additive α) :=
{ zero     := 0,
  zero_add := @one_mul _ _,
  add_zero := @mul_one _ _,
  ..additive.add_semigroup }

instance [add_monoid α] : monoid (multiplicative α) :=
{ one     := 1,
  one_mul := @zero_add _ _,
  mul_one := @add_zero _ _,
  ..multiplicative.semigroup }

instance [comm_monoid α] : add_comm_monoid (additive α) :=
{ .. additive.add_monoid, .. additive.add_comm_semigroup }

instance [add_comm_monoid α] : comm_monoid (multiplicative α) :=
{ ..multiplicative.monoid, .. multiplicative.comm_semigroup }

instance [has_inv α] : has_neg (additive α) := ⟨λ x, to_add (of_add x)⁻¹⟩

@[simp] lemma to_add_inv [has_inv α] (x : α) : to_add x⁻¹ = -(to_add x) := rfl

@[simp] lemma of_add_neg [has_inv α] (x : additive α) : of_add (-x) = (of_add x)⁻¹ := rfl

instance [has_neg α] : has_inv (multiplicative α) := ⟨λ x, to_mul (-(of_mul x))⟩

@[simp] lemma to_mul_neg [has_neg α] (x : α) : to_mul (-x) = (to_mul x)⁻¹ := rfl

@[simp] lemma of_mul_inv [has_neg α] (x : multiplicative α) : of_mul x⁻¹ = -of_mul x := rfl

instance [group α] : add_group (additive α) :=
{ add_left_neg := @mul_left_inv α _,
  .. additive.has_neg, .. additive.add_monoid }

instance [add_group α] : group (multiplicative α) :=
{ mul_left_inv := @add_left_neg α _,
  .. multiplicative.has_inv, ..multiplicative.monoid }

instance [comm_group α] : add_comm_group (additive α) :=
{ .. additive.add_group, .. additive.add_comm_monoid }

instance [add_comm_group α] : comm_group (multiplicative α) :=
{ .. multiplicative.group, .. multiplicative.comm_monoid }

/-- Reinterpret `f : α →+ β` as `multiplicative α →* multiplicative β`. -/
def add_monoid_hom.to_multiplicative [add_monoid α] [add_monoid β] (f : α →+ β) :
  multiplicative α →* multiplicative β :=
⟨f.1, f.2, f.3⟩

/-- Reinterpret `f : α →* β` as `additive α →+ additive β`. -/
def monoid_hom.to_additive [monoid α] [monoid β] (f : α →* β) : additive α →+ additive β :=
⟨f.1, f.2, f.3⟩

attribute [irreducible] multiplicative additive
