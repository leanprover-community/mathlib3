/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yury Kudryashov
-/
import algebra.hom.group

/-!
# Extensionality lemmas for monoid and group structures

In this file we prove extensionality lemmas for `monoid` and higher algebraic structures with one
binary operation. Extensionality lemmas for structures that are lower in the hierarchy can be found
in `algebra.group.defs`.

## Implementation details

To get equality of `npow` etc, we define a monoid homomorphism between two monoid structures on the
same type, then apply lemmas like `monoid_hom.map_div`, `monoid_hom.map_pow` etc.

## Tags
monoid, group, extensionality
-/

universe u

@[ext, to_additive]
lemma monoid.ext {M : Type u} ⦃m₁ m₂ : monoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
begin
  have h₁ : (@monoid.to_mul_one_class _ m₁).one = (@monoid.to_mul_one_class _ m₂).one,
    from congr_arg (@mul_one_class.one M) (mul_one_class.ext h_mul),
  set f : @monoid_hom M M (@monoid.to_mul_one_class _ m₁) (@monoid.to_mul_one_class _ m₂) :=
    { to_fun := id, map_one' := h₁, map_mul' := λ x y, congr_fun (congr_fun h_mul x) y },
  have hpow : m₁.npow = m₂.npow, by { ext n x, exact @monoid_hom.map_pow M M m₁ m₂ f x n },
  unfreezingI { cases m₁, cases m₂ },
  congr; assumption
end

@[to_additive]
lemma comm_monoid.to_monoid_injective {M : Type u} :
  function.injective (@comm_monoid.to_monoid M) :=
begin
  rintros ⟨⟩ ⟨⟩ h,
  congr'; injection h,
end

@[ext, to_additive]
lemma comm_monoid.ext {M : Type*} ⦃m₁ m₂ : comm_monoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
comm_monoid.to_monoid_injective $ monoid.ext h_mul

@[to_additive]
lemma left_cancel_monoid.to_monoid_injective {M : Type u} :
  function.injective (@left_cancel_monoid.to_monoid M) :=
begin
  rintros ⟨⟩ ⟨⟩ h,
  congr'; injection h,
end

@[ext, to_additive]
lemma left_cancel_monoid.ext {M : Type u} ⦃m₁ m₂ : left_cancel_monoid M⦄
  (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
left_cancel_monoid.to_monoid_injective $ monoid.ext h_mul

@[to_additive]
lemma right_cancel_monoid.to_monoid_injective {M : Type u} :
  function.injective (@right_cancel_monoid.to_monoid M) :=
begin
  rintros ⟨⟩ ⟨⟩ h,
  congr'; injection h,
end

@[ext, to_additive]
lemma right_cancel_monoid.ext {M : Type u} ⦃m₁ m₂ : right_cancel_monoid M⦄
  (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
right_cancel_monoid.to_monoid_injective $ monoid.ext h_mul

@[to_additive]
lemma cancel_monoid.to_left_cancel_monoid_injective {M : Type u} :
  function.injective (@cancel_monoid.to_left_cancel_monoid M) :=
begin
  rintros ⟨⟩ ⟨⟩ h,
  congr'; injection h,
end

@[ext, to_additive]
lemma cancel_monoid.ext {M : Type*} ⦃m₁ m₂ : cancel_monoid M⦄
  (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
cancel_monoid.to_left_cancel_monoid_injective $ left_cancel_monoid.ext h_mul

@[to_additive]
lemma cancel_comm_monoid.to_comm_monoid_injective {M : Type u} :
  function.injective (@cancel_comm_monoid.to_comm_monoid M) :=
begin
  rintros ⟨⟩ ⟨⟩ h,
  congr'; injection h,
end

@[ext, to_additive]
lemma cancel_comm_monoid.ext {M : Type*} ⦃m₁ m₂ : cancel_comm_monoid M⦄
  (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
cancel_comm_monoid.to_comm_monoid_injective $ comm_monoid.ext h_mul

@[ext, to_additive]
lemma div_inv_monoid.ext {M : Type*} ⦃m₁ m₂ : div_inv_monoid M⦄ (h_mul : m₁.mul = m₂.mul)
  (h_inv : m₁.inv = m₂.inv) : m₁ = m₂ :=
begin
  have h₁ : (@div_inv_monoid.to_monoid _ m₁).one = (@div_inv_monoid.to_monoid _ m₂).one,
    from congr_arg (@monoid.one M) (monoid.ext h_mul),
  set f : @monoid_hom M M (by letI := m₁; apply_instance) (by letI := m₂; apply_instance) :=
    { to_fun := id, map_one' := h₁, map_mul' := λ x y, congr_fun (congr_fun h_mul x) y },
  have hpow : (@div_inv_monoid.to_monoid _ m₁).npow = (@div_inv_monoid.to_monoid _ m₂).npow :=
    congr_arg (@monoid.npow M) (monoid.ext h_mul),
  have hzpow : m₁.zpow = m₂.zpow,
  { ext m x,
    exact @monoid_hom.map_zpow' M M m₁ m₂ f (congr_fun h_inv) x m },
  have hdiv : m₁.div = m₂.div,
  { ext a b,
    exact @map_div' M M _ m₁ m₂ _ f (congr_fun h_inv) a b },
  unfreezingI { cases m₁, cases m₂ },
  congr, exacts [h_mul, h₁, hpow, h_inv, hdiv, hzpow]
end

@[ext, to_additive]
lemma group.ext {G : Type*} ⦃g₁ g₂ : group G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ :=
begin
  set f := @monoid_hom.mk' G G (by letI := g₁; apply_instance) g₂ id
    (λ a b, congr_fun (congr_fun h_mul a) b),
  exact group.to_div_inv_monoid_injective (div_inv_monoid.ext h_mul
    (funext $ @monoid_hom.map_inv G G g₁ (@group.to_division_monoid _ g₂) f))
end

@[ext, to_additive]
lemma comm_group.ext {G : Type*} ⦃g₁ g₂ : comm_group G⦄
  (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ :=
comm_group.to_group_injective $ group.ext h_mul
