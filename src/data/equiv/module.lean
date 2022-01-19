/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
import algebra.module.linear_map

/-!
# (Semi)linear equivalences

In this file we define

* `linear_equiv σ M M₂`, `M ≃ₛₗ[σ] M₂`: an invertible semilinear map. Here, `σ` is a `ring_hom`
  from `R` to `R₂` and an `e : M ≃ₛₗ[σ] M₂` satisfies `e (c • x) = (σ c) • (e x)`. The plain
  linear version, with `σ` being `ring_hom.id R`, is denoted by `M ≃ₗ[R] M₂`, and the
  star-linear version (with `σ` begin `star_ring_aut`) is denoted by `M ≃ₗ⋆[R] M₂`.

## Implementation notes

To ensure that composition works smoothly for semilinear equivalences, we use the typeclasses
`ring_hom_comp_triple`, `ring_hom_inv_pair` and `ring_hom_surjective` from
`algebra/ring/comp_typeclasses`.

The group structure on automorphisms, `linear_equiv.automorphism_group`, is provided elsewhere.

## TODO

* Parts of this file have not yet been generalized to semilinear maps

## Tags

linear equiv, linear equivalences, linear isomorphism, linear isomorphic
-/

open function
open_locale big_operators

universes u u' v w x y z
variables {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variables {k : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variables {N₁ : Type*} {N₂ : Type*} {N₃ : Type*} {N₄ : Type*} {ι : Type*}

section
set_option old_structure_cmd true

/-- A linear equivalence is an invertible linear map. -/
@[nolint has_inhabited_instance]
structure linear_equiv {R : Type*} {S : Type*} [semiring R] [semiring S] (σ : R →+* S)
  {σ' : S →+* R} [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ]
  (M : Type*) (M₂ : Type*)
  [add_comm_monoid M] [add_comm_monoid M₂] [module R M] [module S M₂]
  extends linear_map σ M M₂, M ≃+ M₂
end

attribute [nolint doc_blame] linear_equiv.to_linear_map
attribute [nolint doc_blame] linear_equiv.to_add_equiv

notation M ` ≃ₛₗ[`:50 σ `] ` M₂ := linear_equiv σ M M₂
notation M ` ≃ₗ[`:50 R `] ` M₂ := linear_equiv (ring_hom.id R) M M₂
notation M ` ≃ₗ⋆[`:50 R `] ` M₂ := linear_equiv (@star_ring_aut R _ _ : R →+* R) M M₂

namespace linear_equiv

section add_comm_monoid

variables {M₄ : Type*}
variables [semiring R] [semiring S]

section
variables [add_comm_monoid M] [add_comm_monoid M₁] [add_comm_monoid M₂]
variables [module R M] [module S M₂] {σ : R →+* S} {σ' : S →+* R}
variables [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ]

include R

include σ'
instance : has_coe (M ≃ₛₗ[σ] M₂) (M →ₛₗ[σ] M₂) := ⟨to_linear_map⟩
-- see Note [function coercion]
instance : has_coe_to_fun (M ≃ₛₗ[σ] M₂) (λ _, M → M₂) := ⟨to_fun⟩

@[simp] lemma coe_mk {to_fun inv_fun map_add map_smul left_inv right_inv } :
  ⇑(⟨to_fun, map_add, map_smul, inv_fun, left_inv, right_inv⟩ : M ≃ₛₗ[σ] M₂) = to_fun :=
rfl

-- This exists for compatibility, previously `≃ₗ[R]` extended `≃` instead of `≃+`.
@[nolint doc_blame]
def to_equiv : (M ≃ₛₗ[σ] M₂) → M ≃ M₂ := λ f, f.to_add_equiv.to_equiv

lemma to_equiv_injective : function.injective (to_equiv : (M ≃ₛₗ[σ] M₂) → M ≃ M₂) :=
λ ⟨_, _, _, _, _, _⟩ ⟨_, _, _, _, _, _⟩ h, linear_equiv.mk.inj_eq.mpr (equiv.mk.inj h)

@[simp] lemma to_equiv_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : e₁.to_equiv = e₂.to_equiv ↔ e₁ = e₂ :=
to_equiv_injective.eq_iff

lemma to_linear_map_injective :
  function.injective (coe : (M ≃ₛₗ[σ] M₂) → (M →ₛₗ[σ] M₂)) :=
λ e₁ e₂ H, to_equiv_injective $ equiv.ext $ linear_map.congr_fun H

@[simp, norm_cast] lemma to_linear_map_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} :
  (e₁ : M →ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂ :=
to_linear_map_injective.eq_iff

end

section
variables [semiring R₁] [semiring R₂] [semiring R₃]
variables [add_comm_monoid M] [add_comm_monoid M₁] [add_comm_monoid M₂]
variables [add_comm_monoid M₃] [add_comm_monoid M₄]
variables [add_comm_monoid N₁] [add_comm_monoid N₂]
variables {module_M : module R M} {module_S_M₂ : module S M₂} {σ : R →+* S} {σ' : S →+* R}
variables {re₁ : ring_hom_inv_pair σ σ'} {re₂ : ring_hom_inv_pair σ' σ}
variables (e e' : M ≃ₛₗ[σ] M₂)

lemma to_linear_map_eq_coe : e.to_linear_map = (e : M →ₛₗ[σ] M₂) := rfl

@[simp, norm_cast] theorem coe_coe : ⇑(e : M →ₛₗ[σ] M₂) = e := rfl

@[simp] lemma coe_to_equiv : ⇑e.to_equiv = e := rfl

@[simp] lemma coe_to_linear_map : ⇑e.to_linear_map = e := rfl

@[simp] lemma to_fun_eq_coe : e.to_fun = e := rfl

section
variables {e e'}
@[ext] lemma ext (h : ∀ x, e x = e' x) : e = e' :=
to_equiv_injective (equiv.ext h)

protected lemma congr_arg : Π {x x' : M}, x = x' → e x = e x'
| _ _ rfl := rfl

protected lemma congr_fun (h : e = e') (x : M) : e x = e' x := h ▸ rfl

lemma ext_iff : e = e' ↔ ∀ x, e x = e' x :=
⟨λ h x, h ▸ rfl, ext⟩

end

section
variables (M R)

/-- The identity map is a linear equivalence. -/
@[refl]
def refl [module R M] : M ≃ₗ[R] M := { .. linear_map.id, .. equiv.refl M }

end

@[simp] lemma refl_apply [module R M] (x : M) : refl R M x = x := rfl

include module_M module_S_M₂ re₁ re₂
/-- Linear equivalences are symmetric. -/
@[symm]
def symm (e : M ≃ₛₗ[σ] M₂) : M₂ ≃ₛₗ[σ'] M :=
{ to_fun := e.to_linear_map.inverse e.inv_fun e.left_inv e.right_inv,
  inv_fun := e.to_equiv.symm.inv_fun,
  map_smul' := λ r x, by simp,
  .. e.to_linear_map.inverse e.inv_fun e.left_inv e.right_inv,
  .. e.to_equiv.symm }
omit module_M module_S_M₂ re₁ re₂

/-- See Note [custom simps projection] -/
def simps.symm_apply {R : Type*} {S : Type*} [semiring R] [semiring S] {σ : R →+* S}
  {σ' : S →+* R} [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ]
  {M : Type*} {M₂ : Type*} [add_comm_monoid M] [add_comm_monoid M₂] [module R M] [module S M₂]
  (e : M ≃ₛₗ[σ] M₂) : M₂ → M := e.symm

initialize_simps_projections linear_equiv (to_fun → apply, inv_fun → symm_apply)

include σ'
@[simp] lemma inv_fun_eq_symm : e.inv_fun = e.symm := rfl
omit σ'

variables {module_M₁ : module R₁ M₁} {module_M₂ : module R₂ M₂} {module_M₃ : module R₃ M₃}
variables {module_N₁ : module R₁ N₁} {module_N₂ : module R₁ N₂}
variables {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}
variables {σ₂₁ : R₂ →+* R₁} {σ₃₂ : R₃ →+* R₂} {σ₃₁ : R₃ →+* R₁}
variables [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃]
variables [ring_hom_comp_triple σ₃₂ σ₂₁ σ₃₁]
variables {re₁₂ : ring_hom_inv_pair σ₁₂ σ₂₁} {re₂₃ : ring_hom_inv_pair σ₂₃ σ₃₂}
variables [ring_hom_inv_pair σ₁₃ σ₃₁] {re₂₁ : ring_hom_inv_pair σ₂₁ σ₁₂}
variables {re₃₂ : ring_hom_inv_pair σ₃₂ σ₂₃} [ring_hom_inv_pair σ₃₁ σ₁₃]
variables (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃)

include σ₃₁
/-- Linear equivalences are transitive. -/
-- Note: The linter thinks the `ring_hom_comp_triple` argument is doubled -- it is not.
@[trans, nolint unused_arguments]
def trans : M₁ ≃ₛₗ[σ₁₃] M₃ :=
{ .. e₂₃.to_linear_map.comp e₁₂.to_linear_map,
  .. e₁₂.to_equiv.trans e₂₃.to_equiv }
omit σ₃₁

infixl ` ≪≫ₗ `:80 := @linear_equiv.trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (ring_hom.id _) (ring_hom.id _) (ring_hom.id _)
  (ring_hom.id _) (ring_hom.id _) (ring_hom.id _)
  ring_hom_comp_triple.ids ring_hom_comp_triple.ids
  ring_hom_inv_pair.ids ring_hom_inv_pair.ids ring_hom_inv_pair.ids
  ring_hom_inv_pair.ids ring_hom_inv_pair.ids ring_hom_inv_pair.ids

variables {e₁₂} {e₂₃}

@[simp] lemma coe_to_add_equiv : ⇑(e.to_add_equiv) = e := rfl

/-- The two paths coercion can take to an `add_monoid_hom` are equivalent -/
lemma to_add_monoid_hom_commutes :
  e.to_linear_map.to_add_monoid_hom = e.to_add_equiv.to_add_monoid_hom :=
rfl

include σ₃₁
@[simp] theorem trans_apply (c : M₁) :
  (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃) c = e₂₃ (e₁₂ c) := rfl
omit σ₃₁

include σ'
@[simp] theorem apply_symm_apply (c : M₂) : e (e.symm c) = c := e.right_inv c
@[simp] theorem symm_apply_apply (b : M) : e.symm (e b) = b := e.left_inv b
omit σ'

include σ₃₁ σ₂₁ σ₃₂
@[simp] lemma symm_trans_apply
  (c : M₃) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm c = e₁₂.symm (e₂₃.symm c) := rfl
omit σ₃₁ σ₂₁ σ₃₂

@[simp] lemma trans_refl : e.trans (refl S M₂) = e := to_equiv_injective e.to_equiv.trans_refl
@[simp] lemma refl_trans : (refl R M).trans e = e := to_equiv_injective e.to_equiv.refl_trans

include σ'
lemma symm_apply_eq {x y} : e.symm x = y ↔ x = e y := e.to_equiv.symm_apply_eq

lemma eq_symm_apply {x y} : y = e.symm x ↔ e y = x := e.to_equiv.eq_symm_apply
omit σ'

@[simp] lemma refl_symm [module R M] : (refl R M).symm = linear_equiv.refl R M := rfl

@[simp] lemma trans_symm [module R M] [module R M₂] (f : M ≃ₗ[R] M₂) :
  f.trans f.symm = linear_equiv.refl R M :=
by { ext x, simp }

@[simp] lemma symm_trans [module R M] [module R M₂] (f : M ≃ₗ[R] M₂) :
  f.symm.trans f = linear_equiv.refl R M₂ :=
by { ext x, simp }

@[simp, norm_cast] lemma refl_to_linear_map [module R M] :
  (linear_equiv.refl R M : M →ₗ[R] M) = linear_map.id :=
rfl

@[simp, norm_cast]
lemma comp_coe [module R M] [module R M₂] [module R M₃] (f :  M ≃ₗ[R] M₂)
  (f' :  M₂ ≃ₗ[R] M₃) : (f' : M₂ →ₗ[R] M₃).comp (f : M →ₗ[R] M₂) = (f.trans f' : M ≃ₗ[R] M₃) :=
rfl

@[simp] lemma mk_coe (h₁ h₂ f h₃ h₄) :
  (linear_equiv.mk e h₁ h₂ f h₃ h₄ : M ≃ₛₗ[σ] M₂) = e := ext $ λ _, rfl

@[simp] theorem map_add (a b : M) : e (a + b) = e a + e b := e.map_add' a b
@[simp] theorem map_zero : e 0 = 0 := e.to_linear_map.map_zero
@[simp] theorem map_smulₛₗ (c : R) (x : M) : e (c • x) = (σ c) • e x := e.map_smul' c x

include module_N₁ module_N₂
theorem map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) :
  e (c • x) = c • e x := map_smulₛₗ _ _ _
omit module_N₁ module_N₂

@[simp] lemma map_sum {s : finset ι} (u : ι → M) : e (∑ i in s, u i) = ∑ i in s, e (u i) :=
e.to_linear_map.map_sum

@[simp] theorem map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0 :=
e.to_add_equiv.map_eq_zero_iff
theorem map_ne_zero_iff {x : M} : e x ≠ 0 ↔ x ≠ 0 :=
e.to_add_equiv.map_ne_zero_iff

include module_M module_S_M₂ re₁ re₂
@[simp] theorem symm_symm (e : M ≃ₛₗ[σ] M₂): e.symm.symm = e :=
by { cases e, refl }
omit module_M module_S_M₂ re₁ re₂

lemma symm_bijective [module R M] [module S M₂] [ring_hom_inv_pair σ' σ]
  [ring_hom_inv_pair σ σ'] : function.bijective (symm : (M ≃ₛₗ[σ] M₂) → (M₂ ≃ₛₗ[σ'] M)) :=
equiv.bijective ⟨(symm : (M ≃ₛₗ[σ] M₂) →
  (M₂ ≃ₛₗ[σ'] M)), (symm : (M₂ ≃ₛₗ[σ'] M) → (M ≃ₛₗ[σ] M₂)), symm_symm, symm_symm⟩

@[simp] lemma mk_coe' (f h₁ h₂ h₃ h₄) : (linear_equiv.mk f h₁ h₂ ⇑e h₃ h₄ :
  M₂ ≃ₛₗ[σ'] M) = e.symm :=
symm_bijective.injective $ ext $ λ x, rfl

include σ'
@[simp] theorem symm_mk (f h₁ h₂ h₃ h₄) :
  (⟨e, h₁, h₂, f, h₃, h₄⟩ : M ≃ₛₗ[σ] M₂).symm =
  { to_fun := f, inv_fun := e,
    ..(⟨e, h₁, h₂, f, h₃, h₄⟩ : M ≃ₛₗ[σ] M₂).symm } := rfl
omit σ'

@[simp] lemma coe_symm_mk [module R M] [module R M₂]
  {to_fun inv_fun map_add map_smul left_inv right_inv} :
  ⇑((⟨to_fun, map_add, map_smul, inv_fun, left_inv, right_inv⟩ : M ≃ₗ[R] M₂).symm) = inv_fun :=
rfl

protected lemma bijective : function.bijective e := e.to_equiv.bijective
protected lemma injective : function.injective e := e.to_equiv.injective
protected lemma surjective : function.surjective e := e.to_equiv.surjective

include σ'
protected lemma image_eq_preimage (s : set M) : e '' s = e.symm ⁻¹' s :=
e.to_equiv.image_eq_preimage s
omit σ'

end

variables [semiring R₁] [semiring R₂] [semiring R₃]
variables [add_comm_monoid M] [add_comm_monoid M₁] [add_comm_monoid M₂]

/-- An involutive linear map is a linear equivalence. -/
def of_involutive {σ σ' : R →+* R} [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ]
  {module_M : module R M} (f : M →ₛₗ[σ] M) (hf : involutive f) :
  M ≃ₛₗ[σ] M :=
{ .. f, .. hf.to_equiv f }

@[simp] lemma coe_of_involutive {σ σ' : R →+* R} [ring_hom_inv_pair σ σ']
  [ring_hom_inv_pair σ' σ] {module_M : module R M} (f : M →ₛₗ[σ] M) (hf : involutive f) :
  ⇑(of_involutive f hf) = f :=
rfl

section restrict_scalars

variables (R) [module R M] [module R M₂] [module S M] [module S M₂]
  [linear_map.compatible_smul M M₂ R S]

/-- If `M` and `M₂` are both `R`-semimodules and `S`-semimodules and `R`-semimodule structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear
equivalence from `M` to `M₂` is also an `R`-linear equivalence.

See also `linear_map.restrict_scalars`. -/
@[simps]
def restrict_scalars (f : M ≃ₗ[S] M₂) : M ≃ₗ[R] M₂ :=
{ to_fun := f,
  inv_fun := f.symm,
  left_inv := f.left_inv,
  right_inv := f.right_inv,
  .. f.to_linear_map.restrict_scalars R }

lemma restrict_scalars_injective :
  function.injective (restrict_scalars R : (M ≃ₗ[S] M₂) → (M ≃ₗ[R] M₂)) :=
λ f g h, ext (linear_equiv.congr_fun h : _)

@[simp]
lemma restrict_scalars_inj (f g : M ≃ₗ[S] M₂) :
  f.restrict_scalars R = g.restrict_scalars R ↔ f = g :=
(restrict_scalars_injective R).eq_iff

end restrict_scalars

end add_comm_monoid

end linear_equiv

namespace module

/-- `g : R ≃+* S` is `R`-linear when the module structure on `S` is `module.comp_hom S g` . -/
@[simps]
def comp_hom.to_linear_equiv {R S : Type*} [semiring R] [semiring S] (g : R ≃+* S) :
  (by haveI := comp_hom S (↑g : R →+* S); exact (R ≃ₗ[R] S)) :=
by exact {
  to_fun := (g : R → S),
  inv_fun := (g.symm : S → R),
  map_smul' := g.map_mul,
  ..g }

end module

namespace distrib_mul_action

variables (R M) [semiring R] [add_comm_monoid M] [module R M]

section
variables [monoid S] [distrib_mul_action S M] [smul_comm_class S R M]

/-- Each element of the monoid defines a linear map.

This is a stronger version of `distrib_mul_action.to_add_monoid_hom`. -/
@[simps]
def to_linear_map (s : S) : M →ₗ[R] M :=
{ to_fun := has_scalar.smul s,
  map_add' := smul_add s,
  map_smul' := λ a b, smul_comm _ _ _ }

end

section
variables [group S] [distrib_mul_action S M] [smul_comm_class S R M]

/-- Each element of the group defines a linear equivalence.

This is a stronger version of `distrib_mul_action.to_add_equiv`. -/
@[simps]
def to_linear_equiv (s : S) : M ≃ₗ[R] M :=
{ ..to_add_equiv M s,
  ..to_linear_map R M s }

end

end distrib_mul_action
