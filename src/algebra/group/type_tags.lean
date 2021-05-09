/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.group.hom
import data.equiv.basic
/-!
# Type tags that turn additive structures into multiplicative, and vice versa

We define two type tags:

* `additive α`: turns any multiplicative structure on `α` into the corresponding
  additive structure on `additive α`;
* `multiplicative α`: turns any additive structure on `α` into the corresponding
  multiplicative structure on `multiplicative α`.

We also define instances `additive.*` and `multiplicative.*` that actually transfer the structures.
-/

universes u v
variables {α : Type u} {β : Type v}

/-- If `α` carries some multiplicative structure, then `additive α` carries the corresponding
additive structure. -/
def additive (α : Type*) := α
/-- If `α` carries some additive structure, then `multiplicative α` carries the corresponding
multiplicative structure. -/
def multiplicative (α : Type*) := α

namespace additive

/-- Reinterpret `x : α` as an element of `additive α`. -/
def of_mul : α ≃ additive α := ⟨λ x, x, λ x, x, λ x, rfl, λ x, rfl⟩

/-- Reinterpret `x : additive α` as an element of `α`. -/
def to_mul : additive α ≃ α := of_mul.symm

@[simp] lemma of_mul_symm_eq : (@of_mul α).symm = to_mul := rfl

@[simp] lemma to_mul_symm_eq : (@to_mul α).symm = of_mul := rfl

end additive

namespace multiplicative

/-- Reinterpret `x : α` as an element of `multiplicative α`. -/
def of_add : α ≃ multiplicative α := ⟨λ x, x, λ x, x, λ x, rfl, λ x, rfl⟩

/-- Reinterpret `x : multiplicative α` as an element of `α`. -/
def to_add : multiplicative α ≃ α := of_add.symm

@[simp] lemma of_add_symm_eq : (@of_add α).symm = to_add := rfl

@[simp] lemma to_add_symm_eq : (@to_add α).symm = of_add := rfl

end multiplicative

@[simp] lemma to_add_of_add (x : α) : (multiplicative.of_add x).to_add = x := rfl
@[simp] lemma of_add_to_add (x : multiplicative α) : multiplicative.of_add x.to_add = x := rfl

@[simp] lemma to_mul_of_mul (x : α) : (additive.of_mul x).to_mul = x := rfl
@[simp] lemma of_mul_to_mul (x : additive α) : additive.of_mul x.to_mul = x := rfl

instance [inhabited α] : inhabited (additive α) := ⟨additive.of_mul (default α)⟩
instance [inhabited α] : inhabited (multiplicative α) := ⟨multiplicative.of_add (default α)⟩

instance [nontrivial α] : nontrivial (additive α) :=
additive.of_mul.injective.nontrivial

instance [nontrivial α] : nontrivial (multiplicative α) :=
multiplicative.of_add.injective.nontrivial

instance additive.has_add [has_mul α] : has_add (additive α) :=
{ add := λ x y, additive.of_mul (x.to_mul * y.to_mul) }

instance [has_add α] : has_mul (multiplicative α) :=
{ mul := λ x y, multiplicative.of_add (x.to_add + y.to_add) }

@[simp] lemma of_add_add [has_add α] (x y : α) :
  multiplicative.of_add (x + y) = multiplicative.of_add x * multiplicative.of_add y :=
rfl

@[simp] lemma to_add_mul [has_add α] (x y : multiplicative α) :
  (x * y).to_add = x.to_add + y.to_add :=
rfl

@[simp] lemma of_mul_mul [has_mul α] (x y : α) :
  additive.of_mul (x * y) = additive.of_mul x + additive.of_mul y :=
rfl

@[simp] lemma to_mul_add [has_mul α] (x y : additive α) :
  (x + y).to_mul = x.to_mul * y.to_mul :=
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

instance [has_one α] : has_zero (additive α) := ⟨additive.of_mul 1⟩

@[simp] lemma of_mul_one [has_one α] : @additive.of_mul α 1 = 0 := rfl

@[simp] lemma of_mul_eq_zero {A : Type*} [has_one A] {x : A} :
  additive.of_mul x = 0 ↔ x = 1 := iff.rfl

@[simp] lemma to_mul_zero [has_one α] : (0 : additive α).to_mul = 1 := rfl

instance [has_zero α] : has_one (multiplicative α) := ⟨multiplicative.of_add 0⟩

@[simp] lemma of_add_zero [has_zero α] : @multiplicative.of_add α 0 = 1 := rfl

@[simp] lemma of_add_eq_one {A : Type*} [has_zero A] {x : A} :
  multiplicative.of_add x = 1 ↔ x = 0 := iff.rfl

@[simp] lemma to_add_one [has_zero α] : (1 : multiplicative α).to_add = 0 := rfl

instance [mul_one_class α] : add_zero_class (additive α) :=
{ zero     := 0,
  add      := (+),
  zero_add := one_mul,
  add_zero := mul_one }

instance [add_zero_class α] : mul_one_class (multiplicative α) :=
{ one     := 1,
  mul     := (*),
  one_mul := zero_add,
  mul_one := add_zero }

instance [h : monoid α] : add_monoid (additive α) :=
{ zero     := 0,
  add      := (+),
  nsmul    := @npow α h,
  nsmul_zero' := monoid.npow_zero',
  nsmul_succ' := monoid.npow_succ',
  ..additive.add_zero_class,
  ..additive.add_semigroup }

instance [h : add_monoid α] : monoid (multiplicative α) :=
{ one     := 1,
  mul     := (*),
  npow   := @nsmul α h,
  npow_zero' := add_monoid.nsmul_zero',
  npow_succ' := add_monoid.nsmul_succ',
  ..multiplicative.mul_one_class,
  ..multiplicative.semigroup }

instance [left_cancel_monoid α] : add_left_cancel_monoid (additive α) :=
{ .. additive.add_monoid, .. additive.add_left_cancel_semigroup }

instance [add_left_cancel_monoid α] : left_cancel_monoid (multiplicative α) :=
{ .. multiplicative.monoid, .. multiplicative.left_cancel_semigroup }

instance [right_cancel_monoid α] : add_right_cancel_monoid (additive α) :=
{ .. additive.add_monoid, .. additive.add_right_cancel_semigroup }

instance [add_right_cancel_monoid α] : right_cancel_monoid (multiplicative α) :=
{ .. multiplicative.monoid, .. multiplicative.right_cancel_semigroup }

instance [comm_monoid α] : add_comm_monoid (additive α) :=
{ .. additive.add_monoid, .. additive.add_comm_semigroup }

instance [add_comm_monoid α] : comm_monoid (multiplicative α) :=
{ ..multiplicative.monoid, .. multiplicative.comm_semigroup }

instance [has_inv α] : has_neg (additive α) := ⟨λ x, multiplicative.of_add x.to_mul⁻¹⟩

@[simp] lemma of_mul_inv [has_inv α] (x : α) : additive.of_mul x⁻¹ = -(additive.of_mul x) := rfl

@[simp] lemma to_mul_neg [has_inv α] (x : additive α) : (-x).to_mul = x.to_mul⁻¹ := rfl

instance [has_neg α] : has_inv (multiplicative α) := ⟨λ x, additive.of_mul (-x.to_add)⟩

@[simp] lemma of_add_neg [has_neg α] (x : α) :
  multiplicative.of_add (-x) = (multiplicative.of_add x)⁻¹ := rfl

@[simp] lemma to_add_inv [has_neg α] (x : multiplicative α) :
  (x⁻¹).to_add = -x.to_add := rfl

instance additive.has_sub [has_div α] : has_sub (additive α) :=
{ sub := λ x y, additive.of_mul (x.to_mul / y.to_mul) }

instance multiplicative.has_div [has_sub α] : has_div (multiplicative α) :=
{ div := λ x y, multiplicative.of_add (x.to_add - y.to_add) }

@[simp] lemma of_add_sub [has_sub α] (x y : α) :
  multiplicative.of_add (x - y) = multiplicative.of_add x / multiplicative.of_add y :=
rfl

@[simp] lemma to_add_div [has_sub α] (x y : multiplicative α) :
  (x / y).to_add = x.to_add - y.to_add :=
rfl

@[simp] lemma of_mul_div [has_div α] (x y : α) :
  additive.of_mul (x / y) = additive.of_mul x - additive.of_mul y :=
rfl

@[simp] lemma to_mul_sub [has_div α] (x y : additive α) :
  (x - y).to_mul = x.to_mul / y.to_mul :=
rfl

instance [div_inv_monoid α] : sub_neg_monoid (additive α) :=
{ sub_eq_add_neg := @div_eq_mul_inv α _,
  gsmul := @gpow α _,
  gsmul_zero' := div_inv_monoid.gpow_zero',
  gsmul_succ' := div_inv_monoid.gpow_succ',
  gsmul_neg' := div_inv_monoid.gpow_neg',
  .. additive.has_neg, .. additive.has_sub, .. additive.add_monoid }

instance [sub_neg_monoid α] : div_inv_monoid (multiplicative α) :=
{ div_eq_mul_inv := @sub_eq_add_neg α _,
  gpow := @gsmul α _,
  gpow_zero' := sub_neg_monoid.gsmul_zero',
  gpow_succ' := sub_neg_monoid.gsmul_succ',
  gpow_neg' := sub_neg_monoid.gsmul_neg',
  .. multiplicative.has_inv, .. multiplicative.has_div, .. multiplicative.monoid }

instance [group α] : add_group (additive α) :=
{ add_left_neg := @mul_left_inv α _,
  .. additive.sub_neg_monoid }

instance [add_group α] : group (multiplicative α) :=
{ mul_left_inv := @add_left_neg α _,
  .. multiplicative.div_inv_monoid }

instance [comm_group α] : add_comm_group (additive α) :=
{ .. additive.add_group, .. additive.add_comm_monoid }

instance [add_comm_group α] : comm_group (multiplicative α) :=
{ .. multiplicative.group, .. multiplicative.comm_monoid }

/-- Reinterpret `α →+ β` as `multiplicative α →* multiplicative β`. -/
def add_monoid_hom.to_multiplicative [add_zero_class α] [add_zero_class β] :
  (α →+ β) ≃ (multiplicative α →* multiplicative β) :=
⟨λ f, ⟨f.1, f.2, f.3⟩, λ f, ⟨f.1, f.2, f.3⟩, λ x, by { ext, refl, }, λ x, by { ext, refl, }⟩

/-- Reinterpret `α →* β` as `additive α →+ additive β`. -/
def monoid_hom.to_additive [mul_one_class α] [mul_one_class β] :
  (α →* β) ≃ (additive α →+ additive β) :=
⟨λ f, ⟨f.1, f.2, f.3⟩, λ f, ⟨f.1, f.2, f.3⟩, λ x, by { ext, refl, }, λ x, by { ext, refl, }⟩

/-- Reinterpret `additive α →+ β` as `α →* multiplicative β`. -/
def add_monoid_hom.to_multiplicative' [mul_one_class α] [add_zero_class β] :
  (additive α →+ β) ≃ (α →* multiplicative β) :=
⟨λ f, ⟨f.1, f.2, f.3⟩, λ f, ⟨f.1, f.2, f.3⟩, λ x, by { ext, refl, }, λ x, by { ext, refl, }⟩

/-- Reinterpret `α →* multiplicative β` as `additive α →+ β`. -/
def monoid_hom.to_additive' [mul_one_class α] [add_zero_class β] :
  (α →* multiplicative β) ≃ (additive α →+ β) :=
add_monoid_hom.to_multiplicative'.symm

/-- Reinterpret `α →+ additive β` as `multiplicative α →* β`. -/
def add_monoid_hom.to_multiplicative'' [add_zero_class α] [mul_one_class β] :
  (α →+ additive β) ≃ (multiplicative α →* β) :=
⟨λ f, ⟨f.1, f.2, f.3⟩, λ f, ⟨f.1, f.2, f.3⟩, λ x, by { ext, refl, }, λ x, by { ext, refl, }⟩

/-- Reinterpret `multiplicative α →* β` as `α →+ additive β`. -/
def monoid_hom.to_additive'' [add_zero_class α] [mul_one_class β] :
  (multiplicative α →* β) ≃ (α →+ additive β) :=
add_monoid_hom.to_multiplicative''.symm

/-- If `α` has some multiplicative structure and coerces to a function,
then `additive α` should also coerce to the same function.

This allows `additive` to be used on bundled function types with a multiplicative structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance additive.has_coe_to_fun {α : Type*} [has_coe_to_fun α] :
  has_coe_to_fun (additive α) :=
⟨λ a, has_coe_to_fun.F a.to_mul, λ a, coe_fn a.to_mul⟩

/-- If `α` has some additive structure and coerces to a function,
then `multiplicative α` should also coerce to the same function.

This allows `multiplicative` to be used on bundled function types with an additive structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance multiplicative.has_coe_to_fun {α : Type*} [has_coe_to_fun α] :
  has_coe_to_fun (multiplicative α) :=
⟨λ a, has_coe_to_fun.F a.to_add, λ a, coe_fn a.to_add⟩
