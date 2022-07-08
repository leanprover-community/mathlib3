/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.basic

/-!
# Homomorphisms between representations

This file defines homomorphisms between representations `rep_hom` as linear maps that commute with
the group action on the source and target spaces. Lemmas and definitions follow closely
`algebra.module.linear_map`.

## Notations

Since multiple different representations may be defined on the same vector space, the `rep_hom`s are
written to be from `ρ : representation k G V` to `ρ₂ : representation k G V₂` (denoted `ρ →ᵣ ρ₂`),
rather than from `V` to `V₂`. This is denoted `ρ →ᵣ ρ₂`

## Tags

representation, homomorphism
-/

open function
open_locale big_operators

set_option old_structure_cmd true

/-- A map from V to V₂ is a representation homomorphism if it is a linear map that commutes with
G action (through representation ρ on V and ρ₂ on V₂) -/
structure is_rep_hom
  {k G V V₂: Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [add_comm_monoid V₂] [module k V] [module k V₂]
  (ρ : representation k G V) (ρ₂ : representation k G V₂)
  (f : V → V₂) : Prop :=
(map_add : ∀ x y, f (x + y) = f x + f y)
(map_smul : ∀ (c : k) x, f (c • x) = c • f x)
(map_smulG : ∀ (g : G) x, f (ρ g x) = ρ₂ g (f x))

/-- Bundled homomorphism between representations -/
structure rep_hom
  {k G V V₂ : Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] [add_comm_monoid V₂] [module k V₂]
  (ρ : representation k G V) (ρ₂ : representation k G V₂) extends V →ₗ[k] V₂ :=
(map_smulG' : ∀ (g : G) (x : V), to_fun (ρ g x) = ρ₂ g (to_fun x))

/-- The `linear_map` underlying a `rep_hom`. -/
add_decl_doc rep_hom.to_linear_map

infixr ` →ᵣ `:25 := rep_hom

/-- `rep_hom_class F ρ ρ₂` asserts `F` is a type of bundled representation homomorphisms `ρ → ρ₂`.
A linear map `f` between `k`-modules `V` and `V₂` is a representation homomorphism if it commutes
with the group action on `V` and `V₂`: `∀ g x, f (ρ g x) = ρ₂ g (f x)`. -/
class rep_hom_class (F : Type*) {k G V V₂ : out_param Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] [add_comm_monoid V₂] [module k V₂]
  (ρ : representation k G V) (ρ₂ : representation k G V₂)
  extends semilinear_map_class F (ring_hom.id k) V V₂ :=
(map_smulG : ∀ (f : F) (g : G) (x : V), f (ρ g x) = ρ₂ g (f x))

attribute [nolint dangerous_instance] rep_hom_class.to_semilinear_map_class

export rep_hom_class (map_smulG)
