/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.basic

-- Follows algebra.module.linear_map

open function
open_locale big_operators

section

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

infixr ` →ᵣ `:25 := rep_hom

class rep_hom_class (F : Type*) {k G V V₂ : out_param Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] [add_comm_monoid V₂] [module k V₂]
  (ρ : representation k G V) (ρ₂ : representation k G V₂)
  extends semilinear_map_class F (ring_hom.id k) V V₂ :=
(map_smulG : ∀ (f : F) (g : G) (x : V), f (ρ g x) = ρ₂ g (f x))

attribute [nolint dangerous_instance] rep_hom_class.to_semilinear_map_class

export rep_hom_class (map_smulG)

namespace rep_hom_class

variables
  (F : Type*) {k G V V₂ : Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] [add_comm_monoid V₂] [module k V₂]
  {ρ : representation k G V} {ρ₂ : representation k G V₂}

-- What instances of ..._class go here?

end rep_hom_class

namespace rep_hom

section add_comm_monoid

variables
  {k G V V₂ : Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] [add_comm_monoid V₂] [module k V₂]
  {ρ : representation k G V} {ρ₂ : representation k G V₂}

instance : rep_hom_class (ρ →ᵣ ρ₂) ρ ρ₂ :=
{ coe := rep_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_add := rep_hom.map_add',
  map_smulₛₗ := rep_hom.map_smul',
  map_smulG := rep_hom.map_smulG' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly.
-/
instance : has_coe_to_fun (ρ →ᵣ ρ₂) (λ _, V → V₂) := ⟨λ f, f⟩

@[simp] lemma to_fun_eq_coe {f : ρ →ᵣ ρ₂} : f.to_fun = (f : V → V₂) := rfl

@[ext] theorem ext {f g : ρ →ᵣ ρ₂} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

/-- Copy of a `rep_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : ρ →ᵣ ρ₂) (f' : V → V₂) (h : f' = ⇑f) : ρ →ᵣ ρ₂ :=
{ to_fun := f',
  map_add' := h.symm ▸ f.map_add',
  map_smul' := h.symm ▸ f.map_smul',
  map_smulG' := h.symm ▸ f.map_smulG' }

@[simp] lemma coe_mk (f : V → V₂) (h₁ h₂ h₃) :
  ((rep_hom.mk f h₁ h₂ h₃ : ρ →ᵣ ρ₂) : V → V₂) = f := rfl

/-- Identity map as a `rep_hom` -/
def id : ρ →ᵣ ρ :=
{ to_fun := id,
  map_smulG' := by simp,
  ..linear_map.id }

lemma id_apply (x : V) :
  @id k G V _ _ _ _ ρ x = x := rfl

@[simp, norm_cast] lemma id_coe : ((rep_hom.id : ρ →ᵣ ρ) : V → V) = _root_.id := rfl

theorem is_rep_hom (f : ρ →ᵣ ρ₂) : is_rep_hom ρ ρ₂ f := ⟨f.map_add', f.map_smul', f.map_smulG'⟩

variables {f f' : ρ →ᵣ ρ₂}

theorem coe_injective : @injective (ρ →ᵣ ρ₂) (V → V₂) coe_fn :=
fun_like.coe_injective

protected lemma congr_arg {x x' : V} : x = x' → f x = f x' :=
fun_like.congr_arg f

protected lemma congr_fun (h : f = f') (x : V) : f x = f' x :=
fun_like.congr_fun h x

theorem ext_iff : f = f' ↔ ∀ x, f x = f' x :=
fun_like.ext_iff

@[simp] lemma mk_coe (f : ρ →ᵣ ρ₂) (h₁ h₂ h₃) :
  (rep_hom.mk f h₁ h₂ h₃ : ρ →ᵣ ρ₂) = f := ext $ λ _, rfl

variables (f f')

protected lemma map_add (x y : V) : f (x + y) = f x + f y := map_add f x y
protected lemma map_zero : f 0 = 0 := map_zero f
protected lemma map_smul (c : k) (x : V) : f (c • x) = c • f x := map_smul f c x
protected lemma map_smulG (g : G) (x : V) : f (ρ g x) = ρ₂ g (f x) := map_smulG f g x

@[simp] lemma map_eq_zero_iff (h : function.injective f) {x : V} : f x = 0 ↔ x = 0 :=
⟨λ w, by { apply h, simp [w], }, λ w, by { subst w, simp, }⟩


end add_comm_monoid

end rep_hom

end
