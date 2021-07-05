/-
Copyright (c) 2021 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.basic

/-!
Closely follows module.linear_map
-/

open_locale big_operators

section

set_option old_structure_cmd true

/--
A homomorphism between representations is a linear map that commutes with the action by G.
-/
structure repre_hom
  (k : Type*) (G : Type*) (M : Type*) (M₂ : Type*)
  [semiring k] [monoid G]
  [add_comm_monoid M] [module k M] [repre k G M] [add_comm_monoid M₂] [module k M₂] [repre k G M₂]
  extends M →ₗ[k] M₂ :=
(map_smul2' : ∀ (g : G) (x : M), to_fun (g • x) = g • to_fun x)

end

infixr ` →ᵣ `:25 := repre_hom _ _
notation M ` →ᵣ[`:25 k:25 `;`:25 G:25 `] `:0 M₂:0 := repre_hom k G M M₂

/-
Copy defs and lemmas from linear_map and linear_equiv:
https://github.com/leanprover-community/mathlib/blob/461b444d065e1747f1bda60070b4b5d6a3026fb2/src/algebra/module/linear_map.lean
-/

namespace repre_hom

section add_comm_monoid

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*}
  [semiring k] [monoid G]
  [add_comm_monoid M] [module k M] [repre k G M]
  [add_comm_monoid M₂] [module k M₂] [repre k G M₂]

def of_linear_map (f : M →ₗ[k] M₂) (h : ∀ (g : G) (x : M), f (g • x) = g • f x) : M →ᵣ[k;G] M₂ := ⟨f.1, f.2, f.3, h⟩

instance : has_coe (M →ᵣ[k;G] M₂) (M →ₗ[k] M₂) := ⟨to_linear_map⟩

instance : has_coe_to_fun (M →ᵣ[k;G] M₂) := ⟨_, to_fun⟩

@[simp] lemma coe_mk (f : M → M₂) (h₁ h₂ h₃) :
  ((repre_hom.mk f h₁ h₂ h₃ : M →ᵣ[k;G] M₂) : M → M₂) = f := rfl

/-- Identity map as a `repre_hom` -/
def id : M →ᵣ[k;G] M :=
⟨id, λ _ _, rfl, λ _ _, rfl, λ _ _, rfl⟩

lemma id_apply (x : M) :
  @id k G M _ _ _ _ _ x = x := rfl

@[simp, norm_cast] lemma id_coe : ((repre_hom.id : M →ᵣ[k;G] M) : M → M) = _root_.id := by { ext x, refl }

@[simp] lemma to_fun_eq_coe (f : M →ᵣ[k;G] M₂) : f.to_fun = ⇑f := rfl

theorem coe_injective : function.injective (λ f : M →ᵣ[k;G] M₂, show M → M₂, from f) :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

@[ext] theorem ext {f g : M →ᵣ[k;G] M₂} (H : ∀ x, f x = g x) : f = g :=
coe_injective $ funext H

protected lemma congr_arg {f : M →ᵣ[k;G] M₂} : Π {x x' : M}, x = x' → f x = f x'
| _ _ rfl := rfl

/-- If two linear maps are equal, they are equal at each point. -/
protected lemma congr_fun {f g : M →ᵣ[k;G] M₂} (h : f = g) (x : M) : f x = g x := h ▸ rfl

theorem ext_iff {f g : M →ᵣ[k;G] M₂} : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl }, ext⟩

@[simp] lemma mk_coe (f : M →ᵣ[k;G] M₂) (h₁ h₂ h₃) :
  (repre_hom.mk f h₁ h₂ h₃ : M →ᵣ[k;G] M₂) = f := ext $ λ _, rfl

@[simp] lemma map_add (f : M →ᵣ[k;G] M₂) (x y : M) : f (x + y) = f x + f y := f.map_add' x y

@[simp] lemma map_smul (f : M →ᵣ[k;G] M₂) (c : k) (x : M) : f (c • x) = c • f x := f.map_smul' c x

@[simp] lemma map_smul2 (f : M →ᵣ[k;G] M₂) (g : G) (x : M) : f (g • x) = g • f x := f.map_smul2' g x

@[simp] lemma map_zero (f : M →ᵣ[k;G] M₂) : f 0 = 0 :=
f.to_linear_map.map_zero

@[simp] lemma map_eq_zero_iff (f : M →ᵣ[k;G] M₂) (h : function.injective f) {x : M} : f x = 0 ↔ x = 0 :=
⟨λ w, by { apply h, simp [w], }, λ w, by { subst w, simp, }⟩

@[simp] lemma to_linear_map_coe (f : M →ᵣ[k;G] M₂) : ⇑f.to_linear_map = f := rfl

@[simp] lemma map_sum (f : M →ᵣ[k;G] M₂) {ι} {t : finset ι} {x : ι → M} :
  f (∑ i in t, x i) = (∑ i in t, f (x i)) :=
by {rw ←to_linear_map_coe, apply f.to_linear_map.map_sum}

section

variables
  {M₃ : Type*} [add_comm_monoid M₃] [module k M₃] [repre k G M₃]
  (f : M₂ →ᵣ[k;G] M₃) (g : M →ᵣ[k;G] M₂)

/-- Composition of two repre_hom is a repre_hom -/
def comp : M →ᵣ[k;G] M₃ := ⟨f ∘ g, by simp, by simp, by simp⟩

lemma comp_apply (x : M) : f.comp g x = f (g x) := rfl

@[simp, norm_cast] lemma coe_comp : (f.comp g : M → M₃) = f ∘ g := rfl

@[simp] theorem comp_id : f.comp id = f :=
repre_hom.ext $ λ x, rfl

@[simp] theorem id_comp : id.comp f = f :=
repre_hom.ext $ λ x, rfl

variables {M₄ : Type*} [add_comm_monoid M₄] [module k M₄] [repre k G M₄]

theorem comp_assoc (e : M₃ →ᵣ[k;G] M₄) : (e.comp f).comp g = e.comp (f.comp g) :=
rfl

/- dom_restrict, etc, and algebraic structure of repre_hom from linear_algebra.basic -/

/-- 0 map as a repre_hom -/
instance : has_zero (M →ᵣ[k;G] M₂) := ⟨of_linear_map 0 (by simp)⟩

instance : inhabited (M →ᵣ[k;G] M₂) := ⟨0⟩

@[simp] lemma zero_apply (x : M) : (0 : M →ᵣ[k;G] M₂) x = 0 := rfl

@[simp] theorem comp_zero : f.comp (0 : M →ᵣ[k;G] M₂) = 0 :=
ext $ assume c, by rw [comp_apply, zero_apply, zero_apply, f.map_zero]

@[simp] theorem zero_comp : (0 : M₂ →ᵣ[k;G] M₃).comp g = 0 :=
rfl

/-- 1 is the identity repre_hom -/
instance : has_one (M →ᵣ[k;G] M) := ⟨repre_hom.id⟩

lemma one_eq_id : (1 : M →ᵣ[k;G] M) = id := rfl

@[simp] lemma one_apply (x : M) : (1 : M →ᵣ[k;G] M) x = x := rfl

lemma coe_one : ⇑(1 : M →ᵣ[k;G] M) = _root_.id := rfl

end

end add_comm_monoid

section add_comm_group

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*}
  [semiring k] [monoid G]
  [add_comm_group M] [module k M] [repre k G M]
  [add_comm_group M₂] [module k M₂] [repre k G M₂]

@[simp] lemma map_neg (f : M →ᵣ[k;G] M₂) (x : M) : f (- x) = - f x :=
f.to_linear_map.to_add_monoid_hom.map_neg x

@[simp] lemma map_sub (f : M →ᵣ[k;G] M₂) (x y : M) : f (x - y) = f x - f y :=
f.to_linear_map.to_add_monoid_hom.map_sub x y

end add_comm_group

end repre_hom

section

set_option old_structure_cmd true

structure repre_iso
  (k : Type*) (G : Type*) (M : Type*) (M₂ : Type*)
  [semiring k] [monoid G]
  [add_comm_monoid M] [module k M] [repre k G M] [add_comm_monoid M₂] [module k M₂] [repre k G M₂]
  extends M ≃ₗ[k] M₂ :=
(map_smul2' : ∀ (g : G) (x : M), to_fun (g • x) = g • to_fun x)

end

infixr ` ≃ᵣ `:25 := repre_iso _ _
notation M ` ≃ᵣ[`:25 k:25 `;`:25 G:25 `] `:0 M₂:0 := repre_iso k G M M₂

namespace repre_iso

section add_comm_monoid

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*}
  [semiring k] [monoid G]
  [add_comm_monoid M] [module k M] [repre k G M]
  [add_comm_monoid M₂] [module k M₂] [repre k G M₂]

def of_linear_equiv (f : M ≃ₗ[k] M₂) (h : ∀ (g : G) (x : M), f (g • x) = g • f x) : M ≃ᵣ[k;G] M₂ := ⟨f.1, f.2, f.3, f.4, f.5, f.6, h⟩

instance : has_coe (M ≃ᵣ[k;G] M₂) (M ≃ₗ[k] M₂) := ⟨to_linear_equiv⟩

def to_repre_hom (f : M ≃ᵣ[k;G] M₂) : M →ᵣ[k;G] M₂ := repre_hom.of_linear_map f f.7

instance : has_coe (M ≃ᵣ[k;G] M₂) (M →ᵣ[k;G] M₂) := ⟨to_repre_hom⟩

instance : has_coe_to_fun (M ≃ᵣ[k;G] M₂) := ⟨_, to_fun⟩

@[simp] lemma coe_mk {to_fun inv_fun map_add map_smul left_inv right_inv map_smul2} :
  ⇑(⟨to_fun, map_add, map_smul, inv_fun, left_inv, right_inv, map_smul2⟩ : M ≃ᵣ[k;G] M₂) = to_fun := rfl

@[simp] lemma coe_mk_to_repre_hom {to_fun inv_fun map_add map_smul left_inv right_inv map_smul2} :
  ((⟨to_fun, map_add, map_smul, inv_fun, left_inv, right_inv, map_smul2⟩ : (M ≃ᵣ[k;G] M₂)) : (M →ᵣ[k;G] M₂)) = ⟨to_fun, map_add, map_smul, map_smul2⟩ := rfl

@[simp] lemma to_linear_equiv_coe (f : M ≃ᵣ[k;G] M₂) : ⇑f.to_linear_equiv = f := rfl

def to_equiv : (M ≃ᵣ[k;G] M₂) → M ≃ M₂ := λ f, ⟨f, f.inv_fun, f.left_inv, f.right_inv⟩

lemma to_equiv_injective : function.injective (to_equiv : (M ≃ᵣ[k;G] M₂) → M ≃ M₂) :=
λ ⟨_, _, _, _, _, _, _⟩ ⟨_, _, _, _, _, _, _⟩ h, repre_iso.mk.inj_eq.mpr (equiv.mk.inj h)

@[simp] lemma to_equiv_inj {e₁ e₂ : M ≃ᵣ[k;G] M₂} : e₁.to_equiv = e₂.to_equiv ↔ e₁ = e₂ :=
to_equiv_injective.eq_iff

lemma to_repre_hom_injective : function.injective (coe : (M ≃ᵣ[k;G] M₂) → (M →ᵣ[k;G] M₂)) :=
λ e₁ e₂ H, to_equiv_injective $ equiv.ext $ repre_hom.congr_fun H

@[simp, norm_cast] lemma to_repre_hom_inj {e₁ e₂ : M ≃ᵣ[k;G] M₂} :
  (e₁ : M →ᵣ[k;G] M₂) = e₂ ↔ e₁ = e₂ :=
to_repre_hom_injective.eq_iff

@[simp] lemma to_repre_hom_eq_coe (f : M ≃ᵣ[k;G] M₂) : f.to_repre_hom = ↑f := rfl

@[simp, norm_cast] theorem coe_coe (e : M ≃ᵣ[k;G] M₂) : ⇑(e : M →ᵣ[k;G] M₂) = e := rfl

@[simp] lemma coe_to_equiv (e : M ≃ᵣ[k;G] M₂) : ⇑e.to_equiv = e := rfl

@[simp] lemma coe_to_repre_hom (e : M ≃ᵣ[k;G] M₂) : ⇑e.to_repre_hom = e := rfl

@[simp] lemma to_fun_eq_coe (e : M ≃ᵣ[k;G] M₂) : e.to_fun = e := rfl

section

variables {e e' : M ≃ᵣ[k;G] M₂}

@[ext] lemma ext (h : ∀ x, e x = e' x) : e = e' :=
to_equiv_injective (equiv.ext h)

protected lemma congr_arg : Π {x x' : M}, x = x' → e x = e x'
| _ _ rfl := rfl

protected lemma congr_fun (h : e = e') (x : M) : e x = e' x := h ▸ rfl

lemma ext_iff : e = e' ↔ ∀ x, e x = e' x :=
⟨λ h x, h ▸ rfl, ext⟩

end

/-- The identity map is a repre_iso. -/
@[refl]
def refl
  (k : Type*) (G : Type*) (M : Type*)
  [semiring k] [monoid G]
  [add_comm_monoid M] [module k M] [repre k G M] : M ≃ᵣ[k;G] M :=
{ .. repre_hom.id, .. equiv.refl M }

@[simp] lemma refl_apply (x : M) : refl k G M x = x := rfl

/-- Linear equivalences are symmetric. -/
@[symm]
def symm (e : M ≃ᵣ[k;G] M₂) : M₂ ≃ᵣ[k;G] M :=
{ map_smul2' := by
  { intros,
  simp,
  rw ←linear_equiv.symm_apply_apply e.to_linear_equiv (g • e.to_linear_equiv.symm x),
  rw [to_linear_equiv_coe, ←to_fun_eq_coe, e.map_smul2', to_fun_eq_coe, ←to_linear_equiv_coe, linear_equiv.apply_symm_apply] },
.. e.to_linear_equiv.symm }

@[simp] lemma inv_fun_eq_symm (e : M ≃ᵣ[k;G] M₂) : e.inv_fun = e.symm := rfl

variables
  {M₃ : Type*} [add_comm_monoid M₃] [module k M₃] [repre k G M₃]

/-- Linear equivalences are transitive. -/
@[trans]
def trans (f : M ≃ᵣ[k;G] M₂) (g : M₂ ≃ᵣ[k;G] M₃) : M ≃ᵣ[k;G] M₃ :=
{ .. g.to_repre_hom.comp f.to_repre_hom,
  .. f.to_equiv.trans g.to_equiv }

@[simp] theorem trans_apply (f : M ≃ᵣ[k;G] M₂) (g : M₂ ≃ᵣ[k;G] M₃) (c : M) :
  (f.trans g) c = g (f c) := rfl
@[simp] theorem apply_symm_apply (f : M ≃ᵣ[k;G] M₂) (c : M₂) : f (f.symm c) = c := f.6 c
@[simp] theorem symm_apply_apply (f : M ≃ᵣ[k;G] M₂) (b : M) : f.symm (f b) = b := f.5 b
@[simp] lemma symm_trans_apply (f : M ≃ᵣ[k;G] M₂) (g : M₂ ≃ᵣ[k;G] M₃) (c : M₃) : (f.trans g).symm c = f.symm (g.symm c) := rfl

@[simp] lemma trans_refl (f : M ≃ᵣ[k;G] M₂) : f.trans (refl k G M₂) = f := to_equiv_injective f.to_equiv.trans_refl
@[simp] lemma refl_trans (f : M ≃ᵣ[k;G] M₂) : (refl k G M).trans f = f := to_equiv_injective f.to_equiv.refl_trans

lemma symm_apply_eq (f : M ≃ᵣ[k;G] M₂) {x y} : f.symm x = y ↔ x = f y := f.to_equiv.symm_apply_eq
lemma eq_symm_apply (f : M ≃ᵣ[k;G] M₂) {x y} : y = f.symm x ↔ f y = x := f.to_equiv.eq_symm_apply

@[simp] lemma refl_symm : (refl k G M).symm = refl k G M := rfl

@[simp] lemma trans_symm (f : M ≃ᵣ[k;G] M₂) :
  f.trans f.symm = repre_iso.refl k G M :=
by { ext x, simp }

@[simp] lemma symm_trans (f : M ≃ᵣ[k;G] M₂) :
  f.symm.trans f = repre_iso.refl k G M₂ :=
by { ext x, simp }

@[simp, norm_cast] lemma refl_to_repre_hom :
  (repre_iso.refl k G M : M →ᵣ[k;G] M) = repre_hom.id :=
rfl

@[simp, norm_cast]
lemma comp_coe (f : M ≃ᵣ[k;G] M₂) (g : M₂ ≃ᵣ[k;G] M₃) : (g : M₂ →ᵣ[k;G] M₃).comp (f : M →ᵣ[k;G] M₂) = (f.trans g : M →ᵣ[k;G] M₃) :=
rfl

@[simp] lemma mk_coe (e : M ≃ᵣ[k;G] M₂) (h₁ h₂ f h₃ h₄ h₅) :
  (repre_iso.mk e h₁ h₂ f h₃ h₄ h₅ : M ≃ᵣ[k;G] M₂) = e := ext $ λ _, rfl

@[simp] theorem map_add (e : M ≃ᵣ[k;G] M₂) (a b : M) : e (a + b) = e a + e b := e.map_add' a b
@[simp] theorem map_zero (e : M ≃ᵣ[k;G] M₂) : e 0 = 0 := e.to_repre_hom.map_zero
@[simp] theorem map_smul (e : M ≃ᵣ[k;G] M₂) (c : k) (x : M) : e (c • x) = c • e x := e.map_smul' c x
@[simp] theorem map_smul2 (e : M ≃ᵣ[k;G] M₂) (g : G) (x : M) : e (g • x) = g • e x := e.map_smul2' g x

@[simp] lemma map_sum (e : M ≃ᵣ[k;G] M₂) {ι} {s : finset ι} (u : ι → M) : e (∑ i in s, u i) = ∑ i in s, e (u i) :=
e.to_repre_hom.map_sum

@[simp] theorem map_eq_zero_iff (e : M ≃ᵣ[k;G] M₂) {x : M} : e x = 0 ↔ x = 0 :=
e.to_linear_equiv.map_eq_zero_iff
theorem map_ne_zero_iff (e : M ≃ᵣ[k;G] M₂) {x : M} : e x ≠ 0 ↔ x ≠ 0 :=
e.to_linear_equiv.map_ne_zero_iff

@[simp] theorem symm_symm (e : M ≃ᵣ[k;G] M₂) : e.symm.symm = e := by { cases e, refl }

lemma symm_bijective : function.bijective (symm : (M ≃ᵣ[k;G] M₂) → (M₂ ≃ᵣ[k;G] M)) :=
equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩

@[simp] lemma mk_coe' (e : M ≃ᵣ[k;G] M₂) (f h₁ h₂ h₃ h₄ h₅) :
  (repre_iso.mk f h₁ h₂ ⇑e h₃ h₄ h₅ : M₂ ≃ᵣ[k;G] M) = e.symm :=
symm_bijective.injective $ ext $ λ x, rfl

@[simp] theorem symm_mk (e : M ≃ᵣ[k;G] M₂) (f h₁ h₂ h₃ h₄ h₅) :
  (⟨e, h₁, h₂, f, h₃, h₄, h₅⟩ : M ≃ᵣ[k;G] M₂).symm =
  { to_fun := f, inv_fun := e,
    ..(⟨e, h₁, h₂, f, h₃, h₄, h₅⟩ : M ≃ᵣ[k;G] M₂).symm } := rfl

protected lemma bijective (e : M ≃ᵣ[k;G] M₂) : function.bijective e := e.to_equiv.bijective
protected lemma injective (e : M ≃ᵣ[k;G] M₂) : function.injective e := e.to_equiv.injective
protected lemma surjective (e : M ≃ᵣ[k;G] M₂) : function.surjective e := e.to_equiv.surjective
protected lemma image_eq_preimage (e : M ≃ᵣ[k;G] M₂) (s : set M) : e '' s = e.symm ⁻¹' s :=
e.to_equiv.image_eq_preimage s

end add_comm_monoid

-- section add_comm_group

-- variables
--   {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*}
--   [semiring k] [monoid G]
--   [add_comm_group M] [module k M] [repre k G M]
--   [add_comm_group M₂] [module k M₂] [repre k G M₂]

-- end add_comm_group

end repre_iso

/-
TODO : Show repre_hom and repre_iso give hom and iso between the monoid_hom algebras
-/