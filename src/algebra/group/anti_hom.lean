/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Mario Carneiro, Johan Commelin

Various multiplicative and additive structures.
-/
import algebra.group.basic

variables {α : Type*} {β : Type*} [group α] [group β]

/-- Predicate for group anti-homomorphism, or a homomorphism
  into the opposite group. -/
class is_group_anti_hom (f : α → β) : Prop :=
(map_mul : ∀ a b : α, f (a * b) = f b * f a)

namespace is_group_anti_hom
variables (f : α → β) [w : is_group_anti_hom f]
include w

theorem map_one : f 1 = 1 :=
mul_self_iff_eq_one.1 $ by rw [← map_mul f, one_mul]

theorem map_inv (a : α) : f a⁻¹ = (f a)⁻¹ :=
eq_inv_of_mul_eq_one $ by rw [← map_mul f, mul_inv_self, map_one f]

end is_group_anti_hom

theorem inv_is_group_anti_hom : is_group_anti_hom (λ x : α, x⁻¹) :=
⟨mul_inv_rev⟩
