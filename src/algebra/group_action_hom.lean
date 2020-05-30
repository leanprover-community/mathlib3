/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.group_ring_action

/-!
# Equivariant homomorphisms

## Main definitions

* tbc
-/

universes u v w u₁

variables (M : Type u) [monoid M]
variables (X : Type v) [mul_action M X]
variables (Y : Type w) [mul_action M Y]
variables (Z : Type u₁) [mul_action M Z]
variables (A : Type v) [add_monoid A] [distrib_mul_action M A]
variables (B : Type w) [add_monoid B] [distrib_mul_action M B]
variables (C : Type u₁) [add_monoid C] [distrib_mul_action M C]
variables (R : Type v) [semiring R] [mul_semiring_action M R]
variables (S : Type w) [semiring S] [mul_semiring_action M S]
variables (T : Type u₁) [semiring T] [mul_semiring_action M T]
variables (G : Type u) [group G] (H : set G) [is_subgroup H]

set_option default_priority 100 -- see Note [default priority]
set_option old_structure_cmd true

/-- Equivariant functions. -/
@[nolint has_inhabited_instance]
structure mul_action_hom :=
(to_fun : X → Y)
(map_smul' : ∀ (m : M) (x : X), to_fun (m • x) = m • to_fun x)

notation β ` →[`:25 α:25 `] `:0 γ:0 := mul_action_hom α β γ

namespace mul_action_hom

instance : has_coe_to_fun (X →[M] Y) :=
⟨_, λ c, c.to_fun⟩

variables {M X Y} (f : X →[M] Y)

theorem map_smul (m : M) (x : X) : f (m • x) = m • f x :=
f.map_smul' m x

variables (M X)

/-- The identity map is equivariant. -/
protected def id : X →[M] X :=
⟨id, λ _ _, rfl⟩

@[simp] lemma id_apply (x : X) : mul_action_hom.id M X x = x := rfl

local attribute [instance] mul_action.regular

variables {G} (H)

/-- The canonical map to the left cosets. -/
def to_quotient : G →[G] quotient_group.quotient H :=
⟨coe, λ g x, rfl⟩

@[simp] lemma to_quotient_apply (g : G) : to_quotient H g = g := rfl

variables {M X Y Z}

/-- Composition of two equivariant maps. -/
def comp (f : X →[M] Y) (g : Y →[M] Z) : X →[M] Z :=
⟨g ∘ f, λ m x, calc
g (f (m • x)) = g (m • f x) : by rw f.map_smul
          ... = m • g (f x) : g.map_smul _ _⟩

@[simp] lemma comp_apply (f : X →[M] Y) (g : Y →[M] Z) (x : X) :
  f.comp g x = g (f x) := rfl

end mul_action_hom

/-- Equivariant additive monoid homomorphisms. -/
@[nolint has_inhabited_instance]
structure distrib_mul_action_hom extends A →[M] B, A →+ B.

/-- Reinterpret an equivariant additive monoid homomorphism as an additive monoid homomorphism. -/
add_decl_doc distrib_mul_action_hom.to_add_monoid_hom

/-- Reinterpret an equivariant additive monoid homomorphism as an equivariant function. -/
add_decl_doc distrib_mul_action_hom.to_mul_action_hom

notation β ` →+[`:25 α:25 `] `:0 γ:0 := distrib_mul_action_hom α β γ

/-- Equivariant ring homomorphisms. -/
@[nolint has_inhabited_instance]
structure mul_semiring_action_hom extends R →[M] S, R →+* S.

/-- Reinterpret an equivariant ring homomorphism as a ring homomorphism. -/
add_decl_doc mul_semiring_action_hom.to_ring_hom

/-- Reinterpret an equivariant ring homomorphism as an equivariant map. -/
add_decl_doc mul_semiring_action_hom.to_mul_action_hom

notation β ` →+*[`:25 α:25 `] `:0 γ:0 := mul_semiring_action_hom α β γ
