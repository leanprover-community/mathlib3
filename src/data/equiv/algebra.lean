/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import data.equiv.basic algebra.field

/-!
# equivs in the algebraic hierarchy

The role of this file is twofold. In the first part there are theorems of the following
form: if α has a group structure and α ≃ β then β has a group structure, and
similarly for monoids, semigroups, rings, integral domains, fields and so on.

In the second part there are extensions of equiv called add_equiv,
mul_equiv, and ring_equiv, which are datatypes representing isomorphisms
of add_monoids/add_groups, monoids/groups and rings.

## Notations

The extended equivs all have coercions to functions, and the coercions are the canonical
notation when treating the isomorphisms as maps.

## Implementation notes

Bundling structures means that many things turn into definitions, meaning that to_additive
cannot do much work for us, and conversely that we have to do a lot of naming for it.

The fields for mul_equiv and add_equiv now avoid the unbundled `is_mul_hom` and `is_add_hom`,
as these are deprecated. However ring_equiv still relies on `is_ring_hom`; this should
be rewritten in future.

## Tags

equiv, mul_equiv, add_equiv, ring_equiv
-/

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

namespace equiv

section group
variables [group α]

@[to_additive]
protected def mul_left (a : α) : α ≃ α :=
{ to_fun    := λx, a * x,
  inv_fun   := λx, a⁻¹ * x,
  left_inv  := assume x, show a⁻¹ * (a * x) = x, from inv_mul_cancel_left a x,
  right_inv := assume x, show a * (a⁻¹ * x) = x, from mul_inv_cancel_left a x }

@[to_additive]
protected def mul_right (a : α) : α ≃ α :=
{ to_fun    := λx, x * a,
  inv_fun   := λx, x * a⁻¹,
  left_inv  := assume x, show (x * a) * a⁻¹ = x, from mul_inv_cancel_right x a,
  right_inv := assume x, show (x * a⁻¹) * a = x, from inv_mul_cancel_right x a }

@[to_additive]
protected def inv (α) [group α] : α ≃ α :=
{ to_fun    := λa, a⁻¹,
  inv_fun   := λa, a⁻¹,
  left_inv  := assume a, inv_inv a,
  right_inv := assume a, inv_inv a }

def units_equiv_ne_zero (α : Type*) [field α] : units α ≃ {a : α | a ≠ 0} :=
⟨λ a, ⟨a.1, units.ne_zero _⟩, λ a, units.mk0 _ a.2, λ ⟨_, _, _, _⟩, units.ext rfl, λ ⟨_, _⟩, rfl⟩

@[simp] lemma coe_units_equiv_ne_zero [field α] (a : units α) :
  ((units_equiv_ne_zero α a) : α) = a := rfl

end group

section instances

variables (e : α ≃ β)

protected def has_zero [has_zero β] : has_zero α := ⟨e.symm 0⟩
lemma zero_def [has_zero β] : @has_zero.zero _ (equiv.has_zero e) = e.symm 0 := rfl

protected def has_one [has_one β] : has_one α := ⟨e.symm 1⟩
lemma one_def [has_one β] : @has_one.one _ (equiv.has_one e) = e.symm 1 := rfl

protected def has_mul [has_mul β] : has_mul α := ⟨λ x y, e.symm (e x * e y)⟩
lemma mul_def [has_mul β] (x y : α) :
  @has_mul.mul _ (equiv.has_mul e) x y = e.symm (e x * e y) := rfl

protected def has_add [has_add β] : has_add α := ⟨λ x y, e.symm (e x + e y)⟩
lemma add_def [has_add β] (x y : α) :
  @has_add.add _ (equiv.has_add e) x y = e.symm (e x + e y) := rfl

protected def has_inv [has_inv β] : has_inv α := ⟨λ x, e.symm (e x)⁻¹⟩
lemma inv_def [has_inv β] (x : α) : @has_inv.inv _ (equiv.has_inv e) x = e.symm (e x)⁻¹ := rfl

protected def has_neg [has_neg β] : has_neg α := ⟨λ x, e.symm (-e x)⟩
lemma neg_def [has_neg β] (x : α) : @has_neg.neg _ (equiv.has_neg e) x = e.symm (-e x) := rfl

protected def semigroup [semigroup β] : semigroup α :=
{ mul_assoc := by simp [mul_def, mul_assoc],
  ..equiv.has_mul e }

protected def comm_semigroup [comm_semigroup β] : comm_semigroup α :=
{ mul_comm := by simp [mul_def, mul_comm],
  ..equiv.semigroup e }

protected def monoid [monoid β] : monoid α :=
{ one_mul := by simp [mul_def, one_def],
  mul_one := by simp [mul_def, one_def],
  ..equiv.semigroup e,
  ..equiv.has_one e }

protected def comm_monoid [comm_monoid β] : comm_monoid α :=
{ ..equiv.comm_semigroup e,
  ..equiv.monoid e }

protected def group [group β] : group α :=
{ mul_left_inv := by simp [mul_def, inv_def, one_def],
  ..equiv.monoid e,
  ..equiv.has_inv e }

protected def comm_group [comm_group β] : comm_group α :=
{ ..equiv.group e,
  ..equiv.comm_semigroup e }

protected def add_semigroup [add_semigroup β] : add_semigroup α :=
@additive.add_semigroup _ (@equiv.semigroup _ _ e multiplicative.semigroup)

protected def add_comm_semigroup [add_comm_semigroup β] : add_comm_semigroup α :=
@additive.add_comm_semigroup _ (@equiv.comm_semigroup _ _ e multiplicative.comm_semigroup)

protected def add_monoid [add_monoid β] : add_monoid α :=
@additive.add_monoid _ (@equiv.monoid _ _ e multiplicative.monoid)

protected def add_comm_monoid [add_comm_monoid β] : add_comm_monoid α :=
@additive.add_comm_monoid _ (@equiv.comm_monoid _ _ e multiplicative.comm_monoid)

protected def add_group [add_group β] : add_group α :=
@additive.add_group _ (@equiv.group _ _ e multiplicative.group)

protected def add_comm_group [add_comm_group β] : add_comm_group α :=
@additive.add_comm_group _ (@equiv.comm_group _ _ e multiplicative.comm_group)

protected def semiring [semiring β] : semiring α :=
{ right_distrib := by simp [mul_def, add_def, add_mul],
  left_distrib := by simp [mul_def, add_def, mul_add],
  zero_mul := by simp [mul_def, zero_def],
  mul_zero := by simp [mul_def, zero_def],
  ..equiv.has_zero e,
  ..equiv.has_mul e,
  ..equiv.has_add e,
  ..equiv.monoid e,
  ..equiv.add_comm_monoid e }

protected def comm_semiring [comm_semiring β] : comm_semiring α :=
{ ..equiv.semiring e,
  ..equiv.comm_monoid e }

protected def ring [ring β] : ring α :=
{ ..equiv.semiring e,
  ..equiv.add_comm_group e }

protected def comm_ring [comm_ring β] : comm_ring α :=
{ ..equiv.comm_monoid e,
  ..equiv.ring e }

protected def zero_ne_one_class [zero_ne_one_class β] : zero_ne_one_class α :=
{ zero_ne_one := by simp [zero_def, one_def],
  ..equiv.has_zero e,
  ..equiv.has_one e }

protected def nonzero_comm_ring [nonzero_comm_ring β] : nonzero_comm_ring α :=
{ ..equiv.zero_ne_one_class e,
  ..equiv.comm_ring e }

protected def domain [domain β] : domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := by simp [mul_def, zero_def, equiv.eq_symm_apply],
  ..equiv.has_zero e,
  ..equiv.zero_ne_one_class e,
  ..equiv.has_mul e,
  ..equiv.ring e }

protected def integral_domain [integral_domain β] : integral_domain α :=
{ ..equiv.domain e,
  ..equiv.nonzero_comm_ring e }

protected def division_ring [division_ring β] : division_ring α :=
{ inv_mul_cancel := λ _,
    by simp [mul_def, inv_def, zero_def, one_def, (equiv.symm_apply_eq _).symm];
      exact inv_mul_cancel,
  mul_inv_cancel := λ _,
    by simp [mul_def, inv_def, zero_def, one_def, (equiv.symm_apply_eq _).symm];
      exact mul_inv_cancel,
  ..equiv.has_zero e,
  ..equiv.has_one e,
  ..equiv.domain e,
  ..equiv.has_inv e }

protected def field [field β] : field α :=
{ ..equiv.integral_domain e,
  ..equiv.division_ring e }

protected def discrete_field [discrete_field β] : discrete_field α :=
{ has_decidable_eq := equiv.decidable_eq e,
  inv_zero := by simp [mul_def, inv_def, zero_def],
  ..equiv.has_mul e,
  ..equiv.has_inv e,
  ..equiv.has_zero e,
  ..equiv.field e }

end instances
end equiv

set_option old_structure_cmd true

/-- add_equiv α β is the type of an equiv α ≃ β which preserves addition. -/
structure add_equiv (α β : Type*) [has_add α] [has_add β] extends α ≃ β :=
(map_add' : ∀ x y : α, to_fun (x + y) = to_fun x + to_fun y)

/-- mul_equiv α β is the type of an equiv α ≃ β which preserves multiplication. -/
@[to_additive]
structure mul_equiv (α β : Type*) [has_mul α] [has_mul β] extends α ≃ β :=
(map_mul' : ∀ x y : α, to_fun (x * y) = to_fun x * to_fun y)

infix ` ≃* `:25 := mul_equiv
infix ` ≃+ `:25 := add_equiv

namespace mul_equiv

@[to_additive]
instance {α β} [has_mul α] [has_mul β] : has_coe_to_fun (α ≃* β) := ⟨_, mul_equiv.to_fun⟩

variables [has_mul α] [has_mul β] [has_mul γ]

/-- To show two multiplicative equivalences are equal, it suffices to show the functions are equal. -/
@[extensionality, to_additive]
lemma ext {e f : α ≃* β} (h : (e : α → β) = (f : α → β)) : e = f :=
begin
  -- first, use extensionality for equivalences to also learn that the `inv_fun`s are equal.
  replace h : e.to_equiv = f.to_equiv, { ext x, exact congr_fun h x, },
  cases e, cases f,
  congr,
  { funext x,
    exact congr_fun (congr_arg equiv.to_fun h) x, },
  { funext y,
    exact congr_fun (congr_arg equiv.inv_fun h) y, },
end

/-- A multiplicative isomorphism preserves multiplication (canonical form). -/
@[to_additive]
def map_mul (f : α ≃* β) :  ∀ x y : α, f (x * y) = f x * f y := f.map_mul'

/-- A multiplicative isomorphism preserves multiplication (deprecated). -/
@[to_additive]
instance (h : α ≃* β) : is_mul_hom h := ⟨h.map_mul⟩

/-- The identity map is a multiplicative isomorphism. -/
@[refl, to_additive]
def refl (α : Type*) [has_mul α] : α ≃* α :=
{ map_mul' := λ _ _,rfl,
..equiv.refl _}

/-- The inverse of an isomorphism is an isomorphism. -/
@[symm, to_additive]
def symm (h : α ≃* β) : β ≃* α :=
{ map_mul' := λ n₁ n₂, function.injective_of_left_inverse h.left_inv begin
    show h.to_equiv (h.to_equiv.symm (n₁ * n₂)) =
      h ((h.to_equiv.symm n₁) * (h.to_equiv.symm n₂)),
   rw h.map_mul,
   show _ = h.to_equiv (_) * h.to_equiv (_),
   rw [h.to_equiv.apply_symm_apply, h.to_equiv.apply_symm_apply, h.to_equiv.apply_symm_apply], end,
  ..h.to_equiv.symm}

@[simp, to_additive]
theorem to_equiv_symm (f : α ≃* β) : f.symm.to_equiv = f.to_equiv.symm := rfl

/-- Transitivity of multiplication-preserving isomorphisms -/
@[trans, to_additive]
def trans (h1 : α ≃* β) (h2 : β ≃* γ) : (α ≃* γ) :=
{ map_mul' := λ x y, show h2 (h1 (x * y)) = h2 (h1 x) * h2 (h1 y),
    by rw [h1.map_mul, h2.map_mul],
  ..h1.to_equiv.trans h2.to_equiv }

/-- e.right_inv in canonical form -/
@[simp, to_additive]
def apply_symm_apply (e : α ≃* β) : ∀ (y : β), e (e.symm y) = y :=
e.to_equiv.apply_symm_apply

/-- e.left_inv in canonical form -/
@[simp, to_additive]
def symm_apply_apply (e : α ≃* β) : ∀ (x : α), e.symm (e x) = x :=
equiv.symm_apply_apply (e.to_equiv)

/-- a multiplicative equiv of monoids sends 1 to 1 (and is hence a monoid isomorphism) -/
@[simp, to_additive]
def map_one {α β} [monoid α] [monoid β] (h : α ≃* β) : h 1 = 1 :=
by rw [←mul_one (h 1), ←h.apply_symm_apply 1, ←h.map_mul, one_mul]

/-- A multiplicative bijection between two monoids is an isomorphism. -/
@[to_additive to_add_monoid_hom]
def to_monoid_hom {α β} [monoid α] [monoid β] (h : α ≃* β) : (α →* β) :=
{ to_fun := h,
  map_mul' := h.map_mul,
  map_one' := h.map_one }

@[simp, to_additive to_monoid_hom_left_inv]
lemma to_monoid_hom_left_inv {X Y : Type u} [monoid X] [monoid Y] (e : X ≃* Y) (x : X) :
  e.symm.to_monoid_hom (e.to_monoid_hom x) = x :=
e.left_inv x

@[simp, to_additive to_monoid_hom_right_inv]
lemma to_monoid_hom_right_inv {X Y : Type u} [monoid X] [monoid Y] (e : X ≃* Y) (y : Y) :
  e.to_monoid_hom (e.symm.to_monoid_hom y) = y :=
e.right_inv y

/-- A multiplicative bijection between two monoids is a monoid hom
  (deprecated -- use to_monoid_hom). -/
@[to_additive is_add_monoid_hom]
instance is_monoid_hom {α β} [monoid α] [monoid β] (h : α ≃* β) : is_monoid_hom h :=
⟨h.map_one⟩

/-- A multiplicative bijection between two groups is a group hom
  (deprecated -- use to_monoid_hom). -/
@[to_additive is_add_group_hom]
instance is_group_hom {α β} [group α] [group β] (h : α ≃* β) :
  is_group_hom h := { map_mul := h.map_mul }

end mul_equiv

/-- A group is isomorphic to its group of units. -/
def to_units (α) [group α] : α ≃* units α :=
{ to_fun := λ x, ⟨x, x⁻¹, mul_inv_self _, inv_mul_self _⟩,
  inv_fun := coe,
  left_inv := λ x, rfl,
  right_inv := λ u, units.ext rfl,
  map_mul' := λ x y, units.ext rfl }

namespace units

variables [monoid α] [monoid β] [monoid γ]
(f : α → β) (g : β → γ) [is_monoid_hom f] [is_monoid_hom g]

def map_equiv (h : α ≃* β) : units α ≃* units β :=
{ inv_fun := map h.symm.to_monoid_hom,
  left_inv := λ u, ext $ h.left_inv u,
  right_inv := λ u, ext $ h.right_inv u,
  .. map h.to_monoid_hom }

end units

structure ring_equiv (α β : Type*) [ring α] [ring β] extends α ≃ β :=
(hom : is_ring_hom to_fun)

infix ` ≃r `:25 := ring_equiv

namespace ring_equiv

variables [ring α] [ring β] [ring γ]

instance : has_coe_to_fun (α ≃r β) := ⟨_, ring_equiv.to_fun⟩

instance ring_equiv.is_ring_hom (h : α ≃r β) : is_ring_hom h := h.hom
instance ring_equiv.is_ring_hom' (h : α ≃r β) : is_ring_hom h.to_equiv := h.hom

def to_mul_equiv (e : α ≃r β) : α ≃* β :=
{ map_mul' := e.hom.map_mul, .. e.to_equiv }

def to_add_equiv (e : α ≃r β) : α ≃+ β :=
{ map_add' := e.hom.map_add, .. e.to_equiv }

def to_ring_hom {α β} [ring α] [ring β] (h : α ≃r β) : (α →+* β) :=
{ to_fun := h.to_fun,
  map_add'  := λ x y, is_ring_hom.map_add h.to_fun,
  map_zero' := is_ring_hom.map_zero h.to_fun,
  map_mul'  := λ x y, is_ring_hom.map_mul h.to_fun,
  map_one'  := is_ring_hom.map_one h.to_fun }

/-- To show two ring equivalences are equal, it suffices to show the functions are equal. -/
@[extensionality]
lemma ext {e f : α ≃r β} (h : (e : α → β) = (f : α → β)) : e = f :=
begin
  -- first, use extensionality for equivalences to also learn that the `inv_fun`s are equal.
  replace h : e.to_equiv = f.to_equiv, { ext x, exact congr_fun h x, },
  cases e, cases f,
  congr,
  { funext x,
    exact congr_fun (congr_arg equiv.to_fun h) x, },
  { funext y,
    exact congr_fun (congr_arg equiv.inv_fun h) y, },
end

protected def refl (α : Type*) [ring α] : α ≃r α :=
{ hom := is_ring_hom.id, .. equiv.refl α }

protected def symm {α β : Type*} [ring α] [ring β] (e : α ≃r β) : β ≃r α :=
{ hom := { map_one := e.to_mul_equiv.symm.map_one,
           map_mul := e.to_mul_equiv.symm.map_mul,
           map_add := e.to_add_equiv.symm.map_add },
  .. e.to_equiv.symm }

protected def trans {α β γ : Type*} [ring α] [ring β] [ring γ]
  (e₁ : α ≃r β) (e₂ : β ≃r γ) : α ≃r γ :=
{ hom := is_ring_hom.comp _ _, .. e₁.to_equiv.trans e₂.to_equiv  }

@[simp]
lemma to_ring_hom_left_inv {X Y : Type u} [ring X] [ring Y] (e : X ≃r Y) (x : X) :
  e.symm.to_ring_hom (e.to_ring_hom x) = x :=
e.left_inv x

@[simp]
lemma to_ring_hom_right_inv {X Y : Type u} [ring X] [ring Y] (e : X ≃r Y) (y : Y) :
  e.to_ring_hom (e.symm.to_ring_hom y) = y :=
e.right_inv y

instance symm.is_ring_hom {e : α ≃r β} : is_ring_hom e.to_equiv.symm := hom e.symm

@[simp] lemma to_equiv_symm (e : α ≃r β) : e.symm.to_equiv = e.to_equiv.symm := rfl

@[simp] lemma to_equiv_symm_apply (e : α ≃r β) (x : β) :
  e.symm.to_equiv x = e.to_equiv.symm x := rfl

end ring_equiv
