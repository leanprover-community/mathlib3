/-
Copyright (c) 2014 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes, Johannes Hölzl

Homomorphisms of multiplicative and additive (semi)groups and monoids.
-/
import algebra.group.to_additive algebra.group.basic

universes u v
variables {α : Type u} {β : Type v}

class is_mul_hom {α β : Type*} [has_mul α] [has_mul β] (f : α → β) : Prop :=
(map_mul : ∀ {x y}, f (x * y) = f x * f y)

class is_add_hom {α β : Type*} [has_add α] [has_add β] (f : α → β) : Prop :=
(map_add : ∀ {x y}, f (x + y) = f x + f y)

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

@[to_additive is_add_hom.id]
lemma id : is_mul_hom (id : α → α) := {map_mul := λ _ _, rfl}

@[to_additive is_add_hom.comp]
lemma comp {f : α → β} {g : β → γ} (hf : is_mul_hom f) (hg : is_mul_hom g) : is_mul_hom (g ∘ f) :=
⟨λ x y, by show _ = g _ * g _; rw [←hg.map_mul, ←hf.map_mul]⟩

@[to_additive is_add_hom.comp']
lemma comp' {f : α → β} {g : β → γ} (hf : is_mul_hom f) (hg : is_mul_hom g) :
  is_mul_hom (λ x, g (f x)) :=
⟨λ x y, by rw [←hg.map_mul, ←hf.map_mul]⟩

end is_mul_hom

class is_monoid_hom [monoid α] [monoid β] (f : α → β) extends is_mul_hom f : Prop :=
(map_one : f 1 = 1)

class is_add_monoid_hom [add_monoid α] [add_monoid β] (f : α → β) extends is_add_hom f : Prop :=
(map_zero : f 0 = 0)

attribute [to_additive is_add_monoid_hom] is_monoid_hom
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

lemma map_mul {x y} : f (x * y) = f x * f y :=
is_mul_hom.map_mul f

end is_monoid_hom

namespace is_add_monoid_hom
variables [add_monoid α] [add_monoid β] (f : α → β) [is_add_monoid_hom f]

lemma map_add {x y} : f (x + y) = f x + f y :=
is_add_hom.map_add f

attribute [to_additive is_add_monoid_hom.map_add] is_monoid_hom.map_mul

end is_add_monoid_hom

namespace is_monoid_hom
variables [monoid α] [monoid β] (f : α → β) [is_monoid_hom f]

@[to_additive is_add_monoid_hom.id]
instance id : is_monoid_hom (@id α) := by refine {..}; intros; refl

@[to_additive is_add_monoid_hom.comp]
instance comp {γ} [monoid γ] (g : β → γ) [is_monoid_hom g] :
  is_monoid_hom (g ∘ f) :=
{ map_mul := λ x y, show g _ = g _ * g _, by rw [map_mul f, map_mul g],
  map_one := show g _ = 1, by rw [map_one f, map_one g] }

end is_monoid_hom

namespace is_add_monoid_hom

instance is_add_monoid_hom_mul_left {γ : Type*} [semiring γ] (x : γ) : is_add_monoid_hom (λ y : γ, x * y) :=
{ map_zero := mul_zero x, map_add := λ y z, mul_add x y z }

instance is_add_monoid_hom_mul_right {γ : Type*} [semiring γ] (x : γ) : is_add_monoid_hom (λ y : γ, y * x) :=
{ map_zero := zero_mul x, map_add := λ y z, add_mul y z x }


end is_add_monoid_hom

/-- Predicate for group homomorphism. -/
class is_group_hom [group α] [group β] (f : α → β) : Prop :=
(map_mul : ∀ a b : α, f (a * b) = f a * f b)

class is_add_group_hom [add_group α] [add_group β] (f : α → β) : Prop :=
(map_add : ∀ a b, f (a + b) = f a + f b)

attribute [to_additive is_add_group_hom] is_group_hom
attribute [to_additive is_add_group_hom.cases_on] is_group_hom.cases_on
attribute [to_additive is_add_group_hom.dcases_on] is_group_hom.dcases_on
attribute [to_additive is_add_group_hom.rec] is_group_hom.rec
attribute [to_additive is_add_group_hom.drec] is_group_hom.drec
attribute [to_additive is_add_group_hom.rec_on] is_group_hom.rec_on
attribute [to_additive is_add_group_hom.drec_on] is_group_hom.drec_on
attribute [to_additive is_add_group_hom.map_add] is_group_hom.map_mul
attribute [to_additive is_add_group_hom.mk] is_group_hom.mk

namespace is_group_hom
variables [group α] [group β] (f : α → β) [is_group_hom f]

@[to_additive is_add_group_hom.map_zero]
theorem map_one : f 1 = 1 :=
mul_self_iff_eq_one.1 $ by rw [← map_mul f, one_mul]

@[to_additive is_add_group_hom.map_neg]
theorem map_inv (a : α) : f a⁻¹ = (f a)⁻¹ :=
eq_inv_of_mul_eq_one $ by rw [← map_mul f, inv_mul_self, map_one f]

@[to_additive is_add_group_hom.id]
instance id : is_group_hom (@id α) :=
⟨λ _ _, rfl⟩

@[to_additive is_add_group_hom.comp]
instance comp {γ} [group γ] (g : β → γ) [is_group_hom g] :
  is_group_hom (g ∘ f) :=
⟨λ x y, show g _ = g _ * g _, by rw [map_mul f, map_mul g]⟩

@[to_additive is_add_group_hom.to_is_add_monoid_hom]
lemma to_is_monoid_hom (f : α → β) [is_group_hom f] : is_monoid_hom f :=
{ map_one := is_group_hom.map_one f, map_mul := is_group_hom.map_mul f }

@[to_additive is_add_group_hom.injective_iff]
lemma injective_iff (f : α → β) [is_group_hom f] :
  function.injective f ↔ (∀ a, f a = 1 → a = 1) :=
⟨λ h _, by rw ← is_group_hom.map_one f; exact @h _ _,
  λ h x y hxy, by rw [← inv_inv (f x), inv_eq_iff_mul_eq_one, ← is_group_hom.map_inv f,
      ← is_group_hom.map_mul f] at hxy;
    simpa using inv_eq_of_mul_eq_one (h _ hxy)⟩

attribute [instance] is_group_hom.to_is_monoid_hom
  is_add_group_hom.to_is_add_monoid_hom

end is_group_hom

@[to_additive is_add_group_hom.add]
lemma is_group_hom.mul {α β} [group α] [comm_group β]
  (f g : α → β) [is_group_hom f] [is_group_hom g] :
  is_group_hom (λa, f a * g a) :=
⟨assume a b, by simp only [is_group_hom.map_mul f, is_group_hom.map_mul g, mul_comm, mul_assoc, mul_left_comm]⟩

attribute [instance] is_group_hom.mul is_add_group_hom.add

@[to_additive is_add_group_hom.neg]
lemma is_group_hom.inv {α β} [group α] [comm_group β] (f : α → β) [is_group_hom f] :
  is_group_hom (λa, (f a)⁻¹) :=
⟨assume a b, by rw [is_group_hom.map_mul f, mul_inv]⟩

attribute [instance] is_group_hom.inv is_add_group_hom.neg

@[to_additive neg.is_add_group_hom]
lemma inv.is_group_hom [comm_group α] : is_group_hom (has_inv.inv : α → α) :=
⟨by simp [mul_inv_rev, mul_comm]⟩

attribute [instance] inv.is_group_hom neg.is_add_group_hom

namespace is_add_group_hom
variables [add_group α] [add_group β] (f : α → β) [is_add_group_hom f]

lemma map_sub (a b) : f (a - b) = f a - f b :=
calc f (a - b) = f (a + -b)   : rfl
           ... = f a + f (-b) : map_add f _ _
           ... = f a - f b    : by  simp[map_neg f]

end is_add_group_hom

lemma is_add_group_hom.sub {α β} [add_group α] [add_comm_group β]
  (f g : α → β) [is_add_group_hom f] [is_add_group_hom g] :
  is_add_group_hom (λa, f a - g a) :=
is_add_group_hom.add f (λa, - g a)

attribute [instance] is_add_group_hom.sub
