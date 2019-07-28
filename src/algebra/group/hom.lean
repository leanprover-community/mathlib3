/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes, Johannes Hölzl, Yury Kudryashov

Homomorphisms of multiplicative and additive (semi)groups and monoids.

-/

import algebra.group.to_additive algebra.group.basic

/-!
# monoid and group homomorphisms

This file defines the basic structures for monoid and group
homomorphisms, both unbundled (e.g. `is_monoid_hom f`) and bundled
(e.g. `monoid_hom f`). The unbundled ones are deprecated and the plan is
to slowly remove them from mathlib.

## main definitions

monoid_hom, is_monoid_hom (deprecated), is_group_hom (deprecated)

## Notations

→* for bundled monoid homs (also use for group homs)
→+ for bundled add_monoid homs (also use for add_group homs)

## implementation notes

There's a coercion from bundled homs to fun, and the canonical
notation is to use the bundled hom as a function via this coercion.

There is no `group_hom` -- the idea is that `monoid_hom` is used.
The constructor for `monoid_hom` needs a proof of `map_one` as well
as `map_mul`; separate constructors `monoid_hom.mk'` and
`monoid_hom.mk''` will construct monoid homs given only a proof
that multiplication is preserved,

## Tags

is_group_hom, is_monoid_hom, monoid_hom

-/
universes u v
variables {α : Type u} {β : Type v}

/-- Predicate for maps which preserve a multiplication. -/
class is_mul_hom {α β : Type*} [has_mul α] [has_mul β] (f : α → β) : Prop :=
(map_mul : ∀ x y, f (x * y) = f x * f y)

/-- Predicate for maps which preserve an addition. -/
class is_add_hom {α β : Type*} [has_add α] [has_add β] (f : α → β) : Prop :=
(map_add : ∀ x y, f (x + y) = f x + f y)

attribute [to_additive is_add_hom] is_mul_hom
attribute [to_additive is_add_hom.cases_on] is_mul_hom.cases_on
attribute [to_additive is_add_hom.dcases_on] is_mul_hom.dcases_on
attribute [to_additive is_add_hom.drec] is_mul_hom.drec
attribute [to_additive is_add_hom.drec_on] is_mul_hom.drec_on
attribute [to_additive is_add_hom.map_add] is_mul_hom.map_mul
attribute [to_additive is_add_hom.mk] is_mul_hom.mk
attribute [to_additive is_add_hom.rec] is_mul_hom.rec
attribute [to_additive is_add_hom.rec_on] is_mul_hom.rec_on

namespace is_mul_hom
variables [has_mul α] [has_mul β] {γ : Type*} [has_mul γ]

/-- The identity map preserves multiplication. -/
@[to_additive is_add_hom.id]
instance id : is_mul_hom (id : α → α) := {map_mul := λ _ _, rfl}

/-- The composition of maps which preserve multiplication, also preserves multiplication. -/
@[to_additive is_add_hom.comp]
instance comp (f : α → β) (g : β → γ) [is_mul_hom f] [hg : is_mul_hom g] : is_mul_hom (g ∘ f) :=
{ map_mul := λ x y, by simp only [function.comp, map_mul f, map_mul g] }

/-- A product of maps which preserve multiplication,
preserves multiplication when the target is commutative. -/
@[to_additive is_add_hom.add]
lemma mul {α β} [semigroup α] [comm_semigroup β]
  (f g : α → β) [is_mul_hom f] [is_mul_hom g] :
  is_mul_hom (λa, f a * g a) :=
{ map_mul := assume a b, by simp only [map_mul f, map_mul g, mul_comm, mul_assoc, mul_left_comm] }

attribute [instance] is_mul_hom.mul is_add_hom.add

/-- The inverse of a map which preserves multiplication,
preserves multiplication when the target is commutative. -/
@[to_additive is_add_hom.neg]
lemma inv {α β} [has_mul α] [comm_group β] (f : α → β) [is_mul_hom f] :
  is_mul_hom (λa, (f a)⁻¹) :=
{ map_mul := assume a b, (map_mul f a b).symm ▸ mul_inv _ _ }

attribute [instance] is_mul_hom.inv is_add_hom.neg

end is_mul_hom

/-- Predicate for monoid homomorphisms (deprecated -- use the bundled `monoid_hom` version). -/
class is_monoid_hom [monoid α] [monoid β] (f : α → β) extends is_mul_hom f : Prop :=
(map_one : f 1 = 1)

/-- Predicate for add_monoid homomorphisms (deprecated -- use the bundled `monoid_hom` version. -/
class is_add_monoid_hom [add_monoid α] [add_monoid β] (f : α → β) extends is_add_hom f : Prop :=
(map_zero : f 0 = 0)

attribute [to_additive is_add_monoid_hom] is_monoid_hom
attribute [to_additive is_add_monoid_hom.to_is_add_hom] is_monoid_hom.to_is_mul_hom
attribute [to_additive is_add_monoid_hom.mk] is_monoid_hom.mk
attribute [to_additive is_add_monoid_hom.cases_on] is_monoid_hom.cases_on
attribute [to_additive is_add_monoid_hom.dcases_on] is_monoid_hom.dcases_on
attribute [to_additive is_add_monoid_hom.rec] is_monoid_hom.rec
attribute [to_additive is_add_monoid_hom.drec] is_monoid_hom.drec
attribute [to_additive is_add_monoid_hom.rec_on] is_monoid_hom.rec_on
attribute [to_additive is_add_monoid_hom.drec_on] is_monoid_hom.drec_on
attribute [to_additive is_add_monoid_hom.map_zero] is_monoid_hom.map_one

namespace is_monoid_hom
variables [monoid α] [monoid β] (f : α → β) [is_monoid_hom f]

/-- A monoid homomorphism preserves multiplication. -/
@[to_additive is_add_monoid_hom.map_add]
lemma map_mul (x y) : f (x * y) = f x * f y :=
is_mul_hom.map_mul f x y

end is_monoid_hom

/-- A map to a group preserving multiplication is a monoid homomorphism. -/
@[to_additive is_add_monoid_hom.of_add]
theorem is_monoid_hom.of_mul [monoid α] [group β] (f : α → β) [is_mul_hom f] :
  is_monoid_hom f :=
{ map_one := mul_self_iff_eq_one.1 $ by rw [← is_mul_hom.map_mul f, one_mul] }

namespace is_monoid_hom
variables [monoid α] [monoid β] (f : α → β) [is_monoid_hom f]

/-- The identity map is a monoid homomorphism. -/
@[to_additive is_add_monoid_hom.id]
instance id : is_monoid_hom (@id α) := { map_one := rfl }

/-- The composite of two monoid homomorphisms is a monoid homomorphism. -/
@[to_additive is_add_monoid_hom.comp]
instance comp {γ} [monoid γ] (g : β → γ) [is_monoid_hom g] :
  is_monoid_hom (g ∘ f) :=
{ map_one := show g _ = 1, by rw [map_one f, map_one g] }

end is_monoid_hom

namespace is_add_monoid_hom

/-- Left multiplication in a ring is an additive monoid morphism. -/
instance is_add_monoid_hom_mul_left {γ : Type*} [semiring γ] (x : γ) :
  is_add_monoid_hom (λ y : γ, x * y) :=
{ map_zero := mul_zero x, map_add := λ y z, mul_add x y z }

/-- Right multiplication in a ring is an additive monoid morphism. -/
instance is_add_monoid_hom_mul_right {γ : Type*} [semiring γ] (x : γ) :
  is_add_monoid_hom (λ y : γ, y * x) :=
{ map_zero := zero_mul x, map_add := λ y z, add_mul y z x }

end is_add_monoid_hom

/-- Predicate for group homomorphisms (deprecated -- use bundled `monoid_hom`). -/
class is_group_hom [group α] [group β] (f : α → β) extends is_mul_hom f : Prop

/-- Predicate for additive group homomorphism (deprecated -- use bundled `monoid_hom`). -/
class is_add_group_hom [add_group α] [add_group β] (f : α → β) extends is_add_hom f : Prop

attribute [to_additive is_add_group_hom] is_group_hom
attribute [to_additive is_add_group_hom.to_is_add_hom] is_group_hom.to_is_mul_hom
attribute [to_additive is_add_group_hom.cases_on] is_group_hom.cases_on
attribute [to_additive is_add_group_hom.dcases_on] is_group_hom.dcases_on
attribute [to_additive is_add_group_hom.rec] is_group_hom.rec
attribute [to_additive is_add_group_hom.drec] is_group_hom.drec
attribute [to_additive is_add_group_hom.rec_on] is_group_hom.rec_on
attribute [to_additive is_add_group_hom.drec_on] is_group_hom.drec_on
attribute [to_additive is_add_group_hom.mk] is_group_hom.mk

/-- Construct `is_group_hom` from its only hypothesis. The default constructor tries to get
`is_mul_hom` from class instances, and this makes some proofs fail. -/
@[to_additive is_add_group_hom.mk']
lemma is_group_hom.mk' [group α] [group β] {f : α → β} (hf : ∀ x y, f (x * y) = f x * f y) :
  is_group_hom f :=
{ map_mul := hf }

namespace is_group_hom
variables [group α] [group β] (f : α → β) [is_group_hom f]
open is_mul_hom (map_mul)

/-- A group homomorphism is a monoid homomorphism. -/
@[to_additive is_add_group_hom.to_is_add_monoid_hom]
instance to_is_monoid_hom : is_monoid_hom f :=
is_monoid_hom.of_mul f

/-- A group homomorphism sends 1 to 1. -/
@[to_additive is_add_group_hom.map_zero]
lemma map_one : f 1 = 1 := is_monoid_hom.map_one f

/-- A group homomorphism sends inverses to inverses. -/
@[to_additive is_add_group_hom.map_neg]
theorem map_inv (a : α) : f a⁻¹ = (f a)⁻¹ :=
eq_inv_of_mul_eq_one $ by rw [← map_mul f, inv_mul_self, map_one f]

/-- The identity is a group homomorphism. -/
@[to_additive is_add_group_hom.id]
instance id : is_group_hom (@id α) := { }

/-- The composition of two group homomomorphisms is a group homomorphism. -/
@[to_additive is_add_group_hom.comp]
instance comp {γ} [group γ] (g : β → γ) [is_group_hom g] : is_group_hom (g ∘ f) := { }

/-- A group homomorphism is injective iff its kernel is trivial. -/
@[to_additive is_add_group_hom.injective_iff]
lemma injective_iff (f : α → β) [is_group_hom f] :
  function.injective f ↔ (∀ a, f a = 1 → a = 1) :=
⟨λ h _, by rw ← is_group_hom.map_one f; exact @h _ _,
  λ h x y hxy, by rw [← inv_inv (f x), inv_eq_iff_mul_eq_one, ← map_inv f,
      ← map_mul f] at hxy;
    simpa using inv_eq_of_mul_eq_one (h _ hxy)⟩

/-- The product of group homomorphisms is a group homomorphism if the target is commutative. -/
@[to_additive is_add_group_hom.add]
lemma mul {α β} [group α] [comm_group β]
  (f g : α → β) [is_group_hom f] [is_group_hom g] :
  is_group_hom (λa, f a * g a) :=
{ }

attribute [instance] is_group_hom.mul is_add_group_hom.add

/-- The inverse of a group homomorphism is a group homomorphism if the target is commutative. -/
@[to_additive is_add_group_hom.neg]
lemma inv {α β} [group α] [comm_group β] (f : α → β) [is_group_hom f] :
  is_group_hom (λa, (f a)⁻¹) :=
{ }

attribute [instance] is_group_hom.inv is_add_group_hom.neg

end is_group_hom

/-- Inversion is a group homomorphism if the group is commutative. -/
@[to_additive neg.is_add_group_hom]
lemma inv.is_group_hom [comm_group α] : is_group_hom (has_inv.inv : α → α) :=
{ map_mul := mul_inv }

attribute [instance] inv.is_group_hom neg.is_add_group_hom

namespace is_add_group_hom
variables [add_group α] [add_group β] (f : α → β) [is_add_group_hom f]

/-- Additive group homomorphisms commute with subtraction. -/
lemma map_sub (a b) : f (a - b) = f a - f b :=
calc f (a + -b) = f a + f (-b) : is_add_hom.map_add f _ _
            ... = f a + -f b   : by rw [map_neg f]

end is_add_group_hom

/-- The difference of two additive group homomorphisms is an additive group
homomorphism if the target is commutative. -/
lemma is_add_group_hom.sub {α β} [add_group α] [add_comm_group β]
  (f g : α → β) [is_add_group_hom f] [is_add_group_hom g] :
  is_add_group_hom (λa, f a - g a) :=
is_add_group_hom.add f (λa, - g a)

attribute [instance] is_add_group_hom.sub

/-- Bundled monoid homomorphisms; use this for bundled group homomorphisms too. -/
structure monoid_hom (M : Type*) (N : Type*) [monoid M] [monoid N] :=
(to_fun : M → N)
(map_one' : to_fun 1 = 1)
(map_mul' : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)

infixr ` →* `:25 := monoid_hom

instance {M : Type*} {N : Type*} [monoid M] [monoid N] : has_coe_to_fun (M →* N) :=
⟨_, monoid_hom.to_fun⟩

/-- Bundled add_monoid homomorphisms; use this for bundled add_group homomorphisms too. -/
structure add_monoid_hom (M : Type*) (N : Type*) [add_monoid M] [add_monoid N] :=
(to_fun : M → N)
(map_zero' : to_fun 0 = 0)
(map_add' : ∀ x y, to_fun (x + y) = to_fun x + to_fun y)

infixr ` →+ `:25 := add_monoid_hom

instance {A : Type*} {B : Type*} [add_monoid A] [add_monoid B] : has_coe_to_fun (A →+ B) :=
⟨_, add_monoid_hom.to_fun⟩

attribute [to_additive add_monoid_hom] monoid_hom
attribute [to_additive add_monoid_hom.has_sizeof_inst] monoid_hom.has_sizeof_inst
attribute [to_additive add_monoid_hom.map_zero'] monoid_hom.map_one'
attribute [to_additive add_monoid_hom.map_add'] monoid_hom.map_mul'
attribute [to_additive add_monoid_hom.mk] monoid_hom.mk
attribute [to_additive add_monoid_hom.mk.inj] monoid_hom.mk.inj
attribute [to_additive add_monoid_hom.mk.inj_arrow] monoid_hom.mk.inj_arrow
attribute [to_additive add_monoid_hom.mk.inj_eq] monoid_hom.mk.inj_eq
attribute [to_additive add_monoid_hom.mk.sizeof_spec] monoid_hom.mk.sizeof_spec
attribute [to_additive add_monoid_hom.no_confusion] monoid_hom.no_confusion
attribute [to_additive add_monoid_hom.no_confusion_type] monoid_hom.no_confusion_type
attribute [to_additive add_monoid_hom.rec] monoid_hom.rec
attribute [to_additive add_monoid_hom.rec_on] monoid_hom.rec_on
attribute [to_additive add_monoid_hom.sizeof] monoid_hom.sizeof
attribute [to_additive add_monoid_hom.to_fun] monoid_hom.to_fun

namespace monoid_hom
variables {M : Type*} {N : Type*} {P : Type*} [monoid M] [monoid N] [monoid P]
variables {G : Type*} {H : Type*} [group G] [comm_group H]

@[extensionality] def ext (f g : M →* N) (h : (f : M → N) = g) : f = g :=
by cases f; cases g; cases h; refl

/-- If f is a monoid homomorphism then f 1 = 1. -/
@[simp] lemma map_one (f : M →* N) : f 1 = 1 := f.map_one'

/-- If f is a monoid homomorphism then f (a * b) = f a * f b. -/
@[simp] lemma map_mul (f : M →* N) (a b : M) : f (a * b) = f a * f b := f.map_mul' a b

instance {M : Type*} {N : Type*} [monoid M] [monoid N] (f : M →* N) :
  is_monoid_hom (f : M → N) :=
{ map_mul := f.map_mul,
  map_one := f.map_one }

instance {G : Type*} {H : Type*} [group G] [group H] (f : G →* H) :
  is_group_hom (f : G → H) :=
{ map_mul := f.map_mul }

/-- The identity map from a monoid to itself. -/
def id (M : Type*) [monoid M] : M →* M :=
{ to_fun := id,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

/-- Composition of monoid morphisms is a monoid morphism. -/
def comp (hnp : N →* P) (hmn : M →* N) : M →* P :=
{ to_fun := hnp ∘ hmn,
  map_one' := by simp,
  map_mul' := by simp,
}

protected def one : M →* N :=
{ to_fun := λ _, 1,
  map_one' := rfl,
  map_mul' := λ _ _, (one_mul 1).symm }

instance : has_one (M →* N) := ⟨monoid_hom.one⟩

/-- The product of two monoid morphisms is a monoid morphism if the target is commutative. -/
protected def mul {M N} [monoid M] [comm_monoid N] (f g : M →* N) : M →* N :=
{ to_fun := λ m, f m * g m,
  map_one' := show f 1 * g 1 = 1, by simp,
  map_mul' := begin intros, show f (x * y) * g (x * y) = f x * g x * (f y * g y),
    rw [f.map_mul, g.map_mul, ←mul_assoc, ←mul_assoc, mul_right_comm (f x)], end
}

instance {M N} [monoid M] [comm_monoid N] : has_mul (M →* N) := ⟨monoid_hom.mul⟩

/-- (M →* N) is a comm_monoid if N is commutative. -/
instance {M N} [monoid M] [comm_monoid N] : comm_monoid (M →* N) :=
{ mul := (*),
  mul_assoc := by intros; ext; apply mul_assoc,
  one := 1,
  one_mul := by intros; ext; apply one_mul,
  mul_one := by intros; ext; apply mul_one,
  mul_comm := by intros; ext; apply mul_comm}

/-- Group homomorphisms preserve inverse. -/
@[simp] theorem map_inv {G H} [group G] [group H] (f : G →* H) (g : G) : f g⁻¹ = (f g)⁻¹ :=
eq_inv_of_mul_eq_one $ by rw [←f.map_mul, inv_mul_self, f.map_one]

/-- Group homomorphisms preserve division. -/
@[simp] theorem map_div {G H} [group G] [group H] (f : G →* H) (g h : G) :
  f (g * h⁻¹) = (f g) * (f h)⁻¹ := by rw [f.map_mul, f.map_inv]

/-- Makes a group homomomorphism from a proof that the map preserves multiplication. -/
def mk' {f : M → G} (map_mul : ∀ a b : M, f (a * b) = f a * f b) : M →* G :=
{ to_fun := f,
  map_mul' := map_mul,
  map_one' := mul_self_iff_eq_one.1 $ by rw [←map_mul, mul_one]
}

/-- Makes a group homomorphism from a map and a proof that it preserves multiplication. -/
def mk'' (f : M → G) (map_mul : ∀ a b : M, f (a * b) = f a * f b) : M →* G := mk' map_mul

/-- The inverse of a monoid homomorphism is a monoid homomorphism if the target is
    a commutative group.-/
protected def inv {M G} [monoid M] [comm_group G] (f : M →* G) : M →* G :=
mk'' (λ g, (f g)⁻¹) $ λ a b, by rw [←mul_inv, f.map_mul]

instance {M G} [monoid M] [comm_group G] : has_inv (M →* G) := ⟨monoid_hom.inv⟩

/-- (M →* G) is a comm_group if G is a comm_group -/
instance {M G} [monoid M] [comm_group G] : comm_group (M →* G) :=
{ inv := has_inv.inv,
  mul_left_inv := by intros; ext; apply mul_left_inv,
  ..monoid_hom.comm_monoid
}

end monoid_hom

namespace add_monoid_hom
variables {A : Type*} {B : Type*} {C : Type*} [add_monoid A] [add_monoid B] [add_monoid C]
{G : Type*} [add_group G] {H : Type*} [add_group H]

/-- two additive monoid homomorphisms with equal underlying maps are equal-/
@[extensionality] def ext (f g : A →+ B) (h : (f : A → B) = g) : f = g :=
by cases f; cases g; cases h; refl

attribute [to_additive add_monoid_hom.ext] monoid_hom.ext
attribute [to_additive add_monoid_hom.ext.equations._eqn_1] monoid_hom.ext.equations._eqn_1

/-- if f is a additive monoid homomorphism then f 0 = 0-/
@[simp] def map_zero (f : A →+ B) : f 0 = 0 := f.map_zero'

attribute [to_additive add_monoid_hom.map_zero] monoid_hom.map_one

/-- if f is an additive monoid homomorphism then f (a + b) = f a + f b -/
@[simp] def map_add (f : A →+ B) : ∀ a b : A, f (a + b) = f a + f b := f.map_add'

attribute [to_additive add_monoid_hom.map_add] monoid_hom.map_mul

instance {A : Type*} {B : Type*} [add_monoid A] [add_monoid B] (f : A →+ B) :
  is_add_monoid_hom (f : A → B) :=
{ map_add := f.map_add,
  map_zero := f.map_zero }

instance {G : Type*} {H : Type*} [add_group G] [add_group H] (f : G →+ H) :
  is_add_group_hom (f : G → H) :=
{ map_add := f.map_add }

/-- the identity map from an add_monoid to itself -/
def id (A : Type*) [add_monoid A] : A →+ A :=
{ to_fun := id,
  map_zero' := rfl,
  map_add' := λ _ _, rfl}

attribute [to_additive add_monoid_hom.id._proof_1] monoid_hom.id._proof_1
attribute [to_additive add_monoid_hom.id._proof_2] monoid_hom.id._proof_2
attribute [to_additive add_monoid_hom.id.equations._eqn_1] monoid_hom.id.equations._eqn_1

/-- composition of additive monoid morphisms is an additive monoid morphism -/
def comp (fbc : B →+ C) (fab : A →+ B) : A →+ C :=
{ to_fun := fbc ∘ fab,
  map_zero' := by simp,
  map_add' := by simp,
}

attribute [to_additive add_monoid_hom.comp] monoid_hom.comp
attribute [to_additive add_monoid_hom.comp._proof_1] monoid_hom.comp._proof_1
attribute [to_additive add_monoid_hom.comp._proof_2] monoid_hom.comp._proof_2
attribute [to_additive add_monoid_hom.comp.equations._eqn_1] monoid_hom.comp.equations._eqn_1

protected def zero : A →+ B :=
{ to_fun := λ _, 0,
  map_zero' := rfl,
  map_add' := λ _ _, (zero_add 0).symm }

attribute [to_additive add_monoid_hom.zero] monoid_hom.one
attribute [to_additive add_monoid_hom.zero._proof_1] monoid_hom.one._proof_1
attribute [to_additive add_monoid_hom.zero._proof_2] monoid_hom.one._proof_2
attribute [to_additive add_monoid_hom.zero.equations._eqn_1] monoid_hom.one.equations._eqn_1

instance : has_zero (A →+ B) := ⟨add_monoid_hom.zero⟩

/-- The sum of two additive monoid morphisms is an additive monoid morphism if the
target is commutative-/
protected def add {A B} [add_monoid A] [add_comm_monoid B] (f g : A →+ B) : A →+ B :=
{ to_fun := λ m, f m + g m,
  map_zero' := show f 0 + g 0 = 0, by simp,
  map_add' := begin intros, show f (x + y) + g (x + y) = f x + g x + (f y + g y),
    rw [f.map_add, g.map_add, ←add_assoc, ←add_assoc, add_right_comm (f x)], end
}

attribute [to_additive add_monoid_hom.add] monoid_hom.mul
attribute [to_additive add_monoid_hom.add._proof_1] monoid_hom.mul._proof_1
attribute [to_additive add_monoid_hom.add._proof_2] monoid_hom.mul._proof_2
attribute [to_additive add_monoid_hom.add.equations._eqn_1] monoid_hom.mul.equations._eqn_1

instance {A B} [add_monoid A] [add_comm_monoid B] : has_add (A →+ B) := ⟨add_monoid_hom.add⟩

/-- (A →+ B) is an add_comm_monoid if B is commutative. -/
instance {A B} [add_monoid A] [add_comm_monoid B] : add_comm_monoid (A →+ B) :=
{ add := (+),
  add_assoc := λ _ _ _, by ext; apply add_assoc,
  zero := 0,
  zero_add := λ _, by ext; apply zero_add,
  add_zero := λ _, by ext; apply add_zero,
  add_comm := λ _ _, by ext; apply add_comm }

/-- Additive group homomorphisms preserve additive inverse. -/
@[simp] theorem map_neg (f : G →+ H) (a : G) : f (-a) = -(f a) :=
eq_neg_of_add_eq_zero $ by rw [←f.map_add, neg_add_self, f.map_zero]

attribute [to_additive add_monoid_hom.map_neg] monoid_hom.map_inv

/-- Additive group homomorphisms preserve subtraction. -/
@[simp] theorem map_sub {G H} [add_group G] [add_group H] (f : G →+ H) (g h : G) :
  f (g - h) = (f g) - (f h) := by simp [f.map_add, f.map_neg]

attribute [to_additive add_monoid_hom.map_sub] monoid_hom.map_div

/-- makes an additive group homomomorphism from a proof that the map preserves addition -/
def mk' {f : A → G} (map_add : ∀ x y : A, f (x + y) = f x + f y) : A →+ G :=
{ to_fun := f,
  map_add' := map_add,
  map_zero' := add_self_iff_eq_zero.1 $ by rw [←map_add, add_zero]
}
attribute [to_additive add_monoid_hom.mk'] monoid_hom.mk'
attribute [to_additive add_monoid_hom.mk'._proof_1] monoid_hom.mk'._proof_1
attribute [to_additive add_monoid_hom.mk'.equations._eqn_1] monoid_hom.mk'.equations._eqn_1

def mk'' (f : A → G) (map_add : ∀ x y : A, f (x + y) = f x + f y) : A →+ G := mk' map_add

attribute [to_additive add_monoid_hom.mk''] monoid_hom.mk''
attribute [to_additive add_monoid_hom.mk''.equations._eqn_1] monoid_hom.mk''.equations._eqn_1

/-- the additive inverse of an additive group homomorphism is an additive group homomorphism if the
target is commutative-/
protected def neg {A B} [add_monoid A] [add_comm_group B] (f : A →+ B) : A →+ B :=
mk'' (λ g, -(f g)) $ λ a b, by rw [←neg_add, f.map_add]

attribute [to_additive add_monoid_hom.neg] monoid_hom.inv
attribute [to_additive add_monoid_hom.neg._proof_1] monoid_hom.inv._proof_1
attribute [to_additive add_monoid_hom.neg.equations._eqn_1] monoid_hom.inv.equations._eqn_1

instance {A B} [add_monoid A] [add_comm_group B]: has_neg (A →+ B) := ⟨add_monoid_hom.neg⟩

/-- (A →* B) is an add_comm_group if B is an add_comm_group -/
instance {A B} [add_monoid A] [add_comm_group B] : add_comm_group (A →+ B) :=
{ neg := has_neg.neg,
  add_left_neg := by intros; ext; apply add_left_neg,
  ..add_monoid_hom.add_comm_monoid
}

end add_monoid_hom
