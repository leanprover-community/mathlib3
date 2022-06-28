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

lemma coe_eq_to_linear_map_coe {f : ρ →ᵣ ρ₂} : (f : V → V₂) = (f.to_linear_map : V → V₂) := rfl

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

section
theorem rep_hom_is_rep_hom (f : ρ →ᵣ ρ₂) : is_rep_hom ρ ρ₂ f := ⟨f.map_add', f.map_smul', f.map_smulG'⟩

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

-- pointwise
-- restrict scalars

@[simp] lemma map_sum {ι} {t : finset ι} {g : ι → V} :
  f (∑ i in t, g i) = (∑ i in t, f (g i)) :=
f.to_linear_map.map_sum

theorem to_linear_map_injective :
  function.injective (to_linear_map : (ρ →ᵣ ρ₂) → (V →ₗ[k] V₂)) :=
λ f g h, ext $ linear_map.congr_fun h

-- ext_ring
end

section

variables
  {V₃ : Type*} [add_comm_monoid V₃] [module k V₃]
  {ρ₃ : representation k G V₃} (f₂ : ρ₂ →ᵣ ρ₃) (f : ρ →ᵣ ρ₂)

/-- Composition of two rep_hom's is a rep_hom -/
def comp : ρ →ᵣ ρ₃ :=
{ to_fun := f₂ ∘ f,
  map_smulG' := λ g x, by rw [comp_app, comp_app, map_smulG, map_smulG],
  ..linear_map.comp f₂.to_linear_map f.to_linear_map }

infixr ` ∘ᵣ `:80 := rep_hom.comp

lemma comp_apply (x : V) : f₂.comp f x = f₂ (f x) := rfl

@[simp, norm_cast] lemma coe_comp : (f₂.comp f : V → V₃) = f₂ ∘ f := rfl

@[simp] theorem comp_id : f.comp id = f :=
rep_hom.ext $ λ x, rfl

@[simp] theorem id_comp : id.comp f = f :=
rep_hom.ext $ λ x, rfl

variables {f₂ f} {f₂' : ρ₂ →ᵣ ρ₃} {f' : ρ →ᵣ ρ₂}

theorem cancel_right (hg : function.surjective f) :
  f₂.comp f = f₂'.comp f ↔ f₂ = f₂' :=
⟨λ h, ext $ hg.forall.2 (ext_iff.1 h), λ h, h ▸ rfl⟩

theorem cancel_left (hf : function.injective f₂) :
  f₂.comp f = f₂.comp f' ↔ f = f' :=
⟨λ h, ext $ λ x, hf $ by rw [← comp_apply, h, comp_apply], λ h, h ▸ rfl⟩

end

def inverse
  (f : ρ →ᵣ ρ₂) (f' : V₂ → V) (h₁ : left_inverse f' f) (h₂ : right_inverse f' f) :
  ρ₂ →ᵣ ρ := by dsimp [left_inverse, function.right_inverse] at h₁ h₂; exact
{ to_fun := f',
  map_smulG' := λ g x, by {rw [←h₁ (ρ g (f' x)), map_smulG], simp [h₂]},
  ..linear_map.inverse f.to_linear_map f' h₁ h₂ }

end add_comm_monoid

section add_comm_group

variables
  {k G V V₂ : Type*} [comm_semiring k] [monoid G]
  [add_comm_group V] [module k V] [add_comm_group V₂] [module k V₂]
  {ρ : representation k G V} {ρ₂ : representation k G V₂}
  (f : ρ →ᵣ ρ₂)

protected lemma map_neg (x : V) : f (- x) = - f x := map_neg f x

protected lemma map_sub (x y : V) : f (x - y) = f x - f y := map_sub f x y

-- compatible_smul

end add_comm_group

end rep_hom

-- module
-- distrib_mul_action_hom

namespace is_rep_hom

section add_comm_monoid

variables
  {k G V V₂ : Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] [add_comm_monoid V₂] [module k V₂]
  {ρ : representation k G V} {ρ₂ : representation k G V₂}

/-- Convert an `is_rep_hom` predicate to a `rep_hom` -/
def mk' (f : V → V₂) (H : is_rep_hom ρ ρ₂ f) : ρ →ᵣ ρ₂ :=
{ to_fun := f, map_add' := H.1, map_smul' := H.2, map_smulG' := H.3 }

@[simp] theorem mk'_apply {f : V → V₂} (H : is_rep_hom ρ ρ₂ f) (x : V) :
  mk' f H x = f x := rfl

set_option trace.simplify.rewrite true
lemma is_rep_hom_smul (c : k) :
  is_rep_hom ρ ρ (λ (z : V), c • z) :=
begin
  refine is_rep_hom.mk (smul_add c) _ _,
  { intros _ _,
    rw [←mul_smul, mul_comm, mul_smul] },
  { intros _ _,
    rw [linear_map.map_smulₛₗ, ring_hom.id_apply] }
end

lemma is_rep_hom_smulG_one :
  is_rep_hom ρ ρ (λ (z : V), ρ 1 z) :=
begin
  refine is_rep_hom.mk _ _ _;
  { intros _ _,
    simp only [map_one, linear_map.one_apply] }
end

variables {f : V → V₂} (rh : is_rep_hom ρ ρ₂ f)

lemma map_zero : f (0 : V) = (0 : V₂) := (rh.mk' f).map_zero

end add_comm_monoid

section add_comm_group

variables
  {k G V V₂ : Type*} [comm_semiring k] [monoid G]
  [add_comm_group V] [module k V] [add_comm_group V₂] [module k V₂]
  {ρ : representation k G V} {ρ₂ : representation k G V₂}
  {f : V → V₂} (rh : is_rep_hom ρ ρ₂ f)

lemma map_neg (x : V) : f (- x) = - f x := (rh.mk' f).map_neg x

lemma map_sub (x y) : f (x - y) = f x - f y := (rh.mk' f).map_sub x y

end add_comm_group

end is_rep_hom

-- End

namespace rep_hom

section has_scalar

variables
  {k G V V₂ V₃ : Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] [add_comm_monoid V₂] [module k V₂]
  [add_comm_monoid V₃] [module k V₃]
  {ρ : representation k G V} {ρ₂ : representation k G V₂} {ρ₃ : representation k G V₃}
variables
  {k' : Type*} [monoid k'] [has_scalar k' k] [has_scalar k' V] [distrib_mul_action k' V₂]
  [is_scalar_tower k' k V] [is_scalar_tower k' k V₂] [smul_comm_class k' k V₂]

instance : has_scalar k' (ρ →ᵣ ρ₂) :=
⟨λ a f, { to_fun := a • f,
          map_add' := λ x y, by rw [pi.smul_apply,
            f.map_add, smul_add, pi.smul_apply, pi.smul_apply],
          map_smul' := λ c x, by rw [pi.smul_apply,
            f.map_smul, ring_hom.id_apply, smul_comm, pi.smul_apply],
          map_smulG' := λ g x, by rw [pi.smul_apply,
            f.map_smulG, pi.smul_apply, linear_map.map_smul_of_tower] }⟩

@[simp] lemma smul_apply (a : k) (f : ρ →ᵣ ρ₂) (x : V) : (a • f) x = a • f x := rfl

lemma coe_smul (a : k) (f : ρ →ᵣ ρ₂) : ⇑(a • f) = a • f := rfl

-- smul_comm_class

end has_scalar

section arithmetic

variables
  {k G V V₂ V₃ : Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] [add_comm_monoid V₂] [module k V₂]
  [add_comm_monoid V₃] [module k V₃]
  {ρ : representation k G V} {ρ₂ : representation k G V₂} {ρ₃ : representation k G V₃}
variables
  {W W₂ W₃ : Type*} [add_comm_group W] [module k W] [add_comm_group W₂] [module k W₂]
  [add_comm_group W₃] [module k W₃]
  {σ : representation k G W} {σ₂ : representation k G W₂} {σ₃ : representation k G W₃}

/-- The constant 0 map is a rep_hom. -/
instance : has_zero (ρ →ᵣ ρ₂) :=
⟨{ to_fun := 0, map_add' := by simp, map_smul' := by simp, map_smulG' := by simp }⟩

@[simp] lemma zero_apply (x : V) : (0 : ρ →ᵣ ρ₂) x = 0 := rfl

@[simp] theorem comp_zero (f' : ρ₂ →ᵣ ρ₃) : (f'.comp (0 : ρ →ᵣ ρ₂) : ρ →ᵣ ρ₃) = 0 :=
ext $ assume c, by rw [comp_apply, zero_apply, zero_apply, f'.map_zero]

@[simp] theorem zero_comp (f : ρ →ᵣ ρ₂) : ((0 : ρ₂ →ᵣ ρ₃).comp f : ρ →ᵣ ρ₃) = 0 :=
rfl

instance : inhabited (ρ →ᵣ ρ₂) := ⟨0⟩

@[simp] lemma default_def : (default : (ρ →ᵣ ρ₂)) = 0 := rfl

/-- The sum of two rep_homs is a rep_hom. -/
instance : has_add (ρ →ᵣ ρ₂) :=
⟨λ f g, { to_fun := f + g,
          map_add' := by simp [add_comm, add_left_comm],
          map_smul' := by simp [smul_add],
          map_smulG' := by simp [map_smulG] }⟩

@[simp] lemma add_apply (f g : ρ →ᵣ ρ₂) (x : V) : (f + g) x = f x + g x := rfl

lemma add_comp (f : ρ →ᵣ ρ₂) (g h : ρ₂ →ᵣ ρ₃) :
  ((h + g).comp f : ρ →ᵣ ρ₃) = h.comp f + g.comp f := rfl

lemma comp_add (f g : ρ →ᵣ ρ₂) (h : ρ₂ →ᵣ ρ₃) :
  (h.comp (f + g) : ρ →ᵣ ρ₃) = h.comp f + h.comp g :=
ext $ λ _, h.map_add _ _

/-- The type of rep_homs is an additive monoid. -/
instance : add_comm_monoid (ρ →ᵣ ρ₂) :=
fun_like.coe_injective.add_comm_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)

/-- The negation of a rep_hom is a rep_hom. -/
instance : has_neg (ρ →ᵣ σ₂) :=
⟨λ f, { to_fun := -f, map_add' := by simp [add_comm], map_smul' := by simp,
      map_smulG' := by simp [map_smulG] }⟩

@[simp] lemma neg_apply (f : ρ →ᵣ σ₂) (x : V) : (- f) x = - f x := rfl

@[simp] lemma neg_comp (f : ρ →ᵣ σ₂) (g : σ₂ →ᵣ σ₃) : (- g).comp f = - g.comp f := rfl

@[simp] lemma comp_neg (f : ρ →ᵣ σ₂) (g : σ₂ →ᵣ σ₃) : g.comp (- f) = - g.comp f :=
ext $ λ _, g.map_neg _




end arithmetic



end rep_hom

end
