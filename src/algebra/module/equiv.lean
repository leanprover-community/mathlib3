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
  star-linear version (with `σ` being `star_ring_end`) is denoted by `M ≃ₗ⋆[R] M₂`.

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
@[nolint has_nonempty_instance]
structure linear_equiv {R : Type*} {S : Type*} [semiring R] [semiring S] (σ : R →+* S)
  {σ' : S →+* R} [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ]
  (M : Type*) (M₂ : Type*)
  [add_comm_monoid M] [add_comm_monoid M₂] [module R M] [module S M₂]
  extends linear_map σ M M₂, M ≃+ M₂

attribute [nolint doc_blame] linear_equiv.to_linear_map
attribute [nolint doc_blame] linear_equiv.to_add_equiv

notation M ` ≃ₛₗ[`:50 σ `] ` M₂ := linear_equiv σ M M₂
notation M ` ≃ₗ[`:50 R `] ` M₂ := linear_equiv (ring_hom.id R) M M₂
notation M ` ≃ₗ⋆[`:50 R `] ` M₂ := linear_equiv (star_ring_end R) M M₂

/-- `semilinear_equiv_class F σ M M₂` asserts `F` is a type of bundled `σ`-semilinear equivs
`M → M₂`.

See also `linear_equiv_class F R M M₂` for the case where `σ` is the identity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. -/
class semilinear_equiv_class (F : Type*) {R S : out_param Type*} [semiring R] [semiring S]
  (σ : out_param $ R →+* S) {σ' : out_param $ S →+* R}
  [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ] (M M₂ : out_param Type*)
  [add_comm_monoid M] [add_comm_monoid M₂] [module R M] [module S M₂]
  extends add_equiv_class F M M₂ :=
(map_smulₛₗ : ∀ (f : F) (r : R) (x : M), f (r • x) = (σ r) • f x)

-- `R, S, σ, σ'` become metavars, but it's OK since they are outparams.
attribute [nolint dangerous_instance] semilinear_equiv_class.to_add_equiv_class

/-- `linear_equiv_class F R M M₂` asserts `F` is a type of bundled `R`-linear equivs `M → M₂`.
This is an abbreviation for `semilinear_equiv_class F (ring_hom.id R) M M₂`.
-/
abbreviation linear_equiv_class (F : Type*) (R M M₂ : out_param Type*)
  [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [module R M] [module R M₂] :=
semilinear_equiv_class F (ring_hom.id R) M M₂

end

namespace semilinear_equiv_class

variables (F : Type*) [semiring R] [semiring S]
variables [add_comm_monoid M] [add_comm_monoid M₁] [add_comm_monoid M₂]
variables [module R M] [module S M₂] {σ : R →+* S} {σ' : S →+* R}

-- `σ'` becomes a metavariable, but it's OK since it's an outparam
@[priority 100, nolint dangerous_instance]
instance [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ] [s : semilinear_equiv_class F σ M M₂] :
  semilinear_map_class F σ M M₂ :=
{ coe := (coe : F → M → M₂),
  coe_injective' := @fun_like.coe_injective F _ _ _,
  ..s }

end semilinear_equiv_class

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
  injective (coe : (M ≃ₛₗ[σ] M₂) → (M →ₛₗ[σ] M₂)) :=
λ e₁ e₂ H, to_equiv_injective $ equiv.ext $ linear_map.congr_fun H

@[simp, norm_cast] lemma to_linear_map_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} :
  (e₁ : M →ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂ :=
to_linear_map_injective.eq_iff

instance : semilinear_equiv_class (M ≃ₛₗ[σ] M₂) σ M M₂ :=
{ coe := linear_equiv.to_fun,
  inv := linear_equiv.inv_fun,
  coe_injective' := λ f g h₁ h₂, by { cases f, cases g, congr' },
  left_inv := linear_equiv.left_inv,
  right_inv := linear_equiv.right_inv,
  map_add := map_add',
  map_smulₛₗ := map_smul' }

lemma coe_injective :
  @injective (M ≃ₛₗ[σ] M₂) (M → M₂) coe_fn :=
fun_like.coe_injective

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
@[ext] lemma ext (h : ∀ x, e x = e' x) : e = e' := fun_like.ext _ _ h

lemma ext_iff : e = e' ↔ ∀ x, e x = e' x := fun_like.ext_iff

protected lemma congr_arg {x x'} : x = x' → e x = e x' := fun_like.congr_arg e

protected lemma congr_fun (h : e = e') (x : M) : e x = e' x := fun_like.congr_fun h x

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
  map_smul' := λ r x, by rw map_smulₛₗ,
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

@[simp] lemma coe_to_equiv_symm : ⇑e.to_equiv.symm = e.symm := rfl

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

theorem coe_trans :
  (e₁₂.trans e₂₃ : M₁ →ₛₗ[σ₁₃] M₃) = (e₂₃ : M₂ →ₛₗ[σ₂₃] M₃).comp (e₁₂ : M₁ →ₛₗ[σ₁₂] M₂) := rfl
omit σ₃₁

include σ'
@[simp] theorem apply_symm_apply (c : M₂) : e (e.symm c) = c := e.right_inv c
@[simp] theorem symm_apply_apply (b : M) : e.symm (e b) = b := e.left_inv b
omit σ'

include σ₃₁ σ₂₁ σ₃₂
@[simp] lemma trans_symm : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm = e₂₃.symm.trans e₁₂.symm :=
rfl

lemma symm_trans_apply
  (c : M₃) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm c = e₁₂.symm (e₂₃.symm c) := rfl
omit σ₃₁ σ₂₁ σ₃₂

@[simp] lemma trans_refl : e.trans (refl S M₂) = e := to_equiv_injective e.to_equiv.trans_refl
@[simp] lemma refl_trans : (refl R M).trans e = e := to_equiv_injective e.to_equiv.refl_trans

include σ'
lemma symm_apply_eq {x y} : e.symm x = y ↔ x = e y := e.to_equiv.symm_apply_eq

lemma eq_symm_apply {x y} : y = e.symm x ↔ e y = x := e.to_equiv.eq_symm_apply
omit σ'

lemma eq_comp_symm {α : Type*} (f : M₂ → α) (g : M₁ → α) :
  f = g ∘ e₁₂.symm ↔ f ∘ e₁₂ = g := e₁₂.to_equiv.eq_comp_symm f g

lemma comp_symm_eq {α : Type*} (f : M₂ → α) (g : M₁ → α) :
  g ∘ e₁₂.symm = f ↔ g = f ∘ e₁₂ := e₁₂.to_equiv.comp_symm_eq f g

lemma eq_symm_comp {α : Type*} (f : α → M₁) (g : α → M₂) :
  f = e₁₂.symm ∘ g ↔ e₁₂ ∘ f = g := e₁₂.to_equiv.eq_symm_comp f g

lemma symm_comp_eq {α : Type*} (f : α → M₁) (g : α → M₂) :
  e₁₂.symm ∘ g = f ↔ g = e₁₂ ∘ f := e₁₂.to_equiv.symm_comp_eq f g

variables [ring_hom_comp_triple σ₂₁ σ₁₃ σ₂₃] [ring_hom_comp_triple σ₃₁ σ₁₂ σ₃₂]

include module_M₃

lemma eq_comp_to_linear_map_symm (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₃] M₃) :
  f = g.comp e₁₂.symm.to_linear_map ↔ f.comp e₁₂.to_linear_map = g :=
begin
  split; intro H; ext,
  { simp [H, e₁₂.to_equiv.eq_comp_symm f g] },
  { simp [←H, ←e₁₂.to_equiv.eq_comp_symm f g] }
end

lemma comp_to_linear_map_symm_eq (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₃] M₃) :
  g.comp e₁₂.symm.to_linear_map = f ↔ g = f.comp e₁₂.to_linear_map :=
begin
  split; intro H; ext,
  { simp [←H, ←e₁₂.to_equiv.comp_symm_eq f g] },
  { simp [H, e₁₂.to_equiv.comp_symm_eq f g] }
end

lemma eq_to_linear_map_symm_comp (f : M₃ →ₛₗ[σ₃₁] M₁) (g : M₃ →ₛₗ[σ₃₂] M₂) :
  f = e₁₂.symm.to_linear_map.comp g ↔ e₁₂.to_linear_map.comp f = g :=
begin
  split; intro H; ext,
  { simp [H, e₁₂.to_equiv.eq_symm_comp f g] },
  { simp [←H, ←e₁₂.to_equiv.eq_symm_comp f g] }
end

lemma to_linear_map_symm_comp_eq (f : M₃ →ₛₗ[σ₃₁] M₁) (g : M₃ →ₛₗ[σ₃₂] M₂) :
  e₁₂.symm.to_linear_map.comp g = f ↔ g = e₁₂.to_linear_map.comp f :=
begin
  split; intro H; ext,
  { simp [←H, ←e₁₂.to_equiv.symm_comp_eq f g] },
  { simp [H, e₁₂.to_equiv.symm_comp_eq f g] }
end

omit module_M₃

@[simp] lemma refl_symm [module R M] : (refl R M).symm = linear_equiv.refl R M := rfl

include re₁₂ re₂₁ module_M₁ module_M₂
@[simp] lemma self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) :
  f.trans f.symm = linear_equiv.refl R₁ M₁ :=
by { ext x, simp }

@[simp] lemma symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) :
  f.symm.trans f = linear_equiv.refl R₂ M₂ :=
by { ext x, simp }
omit re₁₂ re₂₁ module_M₁ module_M₂

@[simp, norm_cast] lemma refl_to_linear_map [module R M] :
  (linear_equiv.refl R M : M →ₗ[R] M) = linear_map.id :=
rfl

@[simp, norm_cast]
lemma comp_coe [module R M] [module R M₂] [module R M₃] (f :  M ≃ₗ[R] M₂)
  (f' :  M₂ ≃ₗ[R] M₃) : (f' : M₂ →ₗ[R] M₃).comp (f : M →ₗ[R] M₂) = (f.trans f' : M ≃ₗ[R] M₃) :=
rfl

@[simp] lemma mk_coe (h₁ h₂ f h₃ h₄) :
  (linear_equiv.mk e h₁ h₂ f h₃ h₄ : M ≃ₛₗ[σ] M₂) = e := ext $ λ _, rfl

protected theorem map_add (a b : M) : e (a + b) = e a + e b := map_add e a b
protected theorem map_zero : e 0 = 0 := map_zero e
-- TODO: `simp` isn't picking up `map_smulₛₗ` for `linear_equiv`s without specifying `map_smulₛₗ f`
@[simp] protected theorem map_smulₛₗ (c : R) (x : M) : e (c • x) = (σ c) • e x := e.map_smul' c x

include module_N₁ module_N₂
theorem map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) :
  e (c • x) = c • e x := map_smulₛₗ e c x
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

@[simp] theorem symm_mk (f h₁ h₂ h₃ h₄) :
  (⟨e, h₁, h₂, f, h₃, h₄⟩ : M ≃ₛₗ[σ] M₂).symm =
  { to_fun := f, inv_fun := e,
    ..(⟨e, h₁, h₂, f, h₃, h₄⟩ : M ≃ₛₗ[σ] M₂).symm } := rfl

@[simp] lemma coe_symm_mk [module R M] [module R M₂]
  {to_fun inv_fun map_add map_smul left_inv right_inv} :
  ⇑((⟨to_fun, map_add, map_smul, inv_fun, left_inv, right_inv⟩ : M ≃ₗ[R] M₂).symm) = inv_fun :=
rfl

protected lemma bijective : function.bijective e := e.to_equiv.bijective
protected lemma injective : function.injective e := e.to_equiv.injective
protected lemma surjective : function.surjective e := e.to_equiv.surjective

protected lemma image_eq_preimage (s : set M) : e '' s = e.symm ⁻¹' s :=
e.to_equiv.image_eq_preimage s

protected lemma image_symm_eq_preimage (s : set M₂) : e.symm '' s = e ⁻¹' s :=
e.to_equiv.symm.image_eq_preimage s

end

/-- Interpret a `ring_equiv` `f` as an `f`-semilinear equiv. -/
@[simps]
def _root_.ring_equiv.to_semilinear_equiv (f : R ≃+* S) :
  by haveI := ring_hom_inv_pair.of_ring_equiv f;
     haveI := ring_hom_inv_pair.symm (↑f : R →+* S) (f.symm : S →+* R);
     exact (R ≃ₛₗ[(↑f : R →+* S)] S) :=
by exact
{ to_fun := f,
  map_smul' := f.map_mul,
  .. f}

variables [semiring R₁] [semiring R₂] [semiring R₃]
variables [add_comm_monoid M] [add_comm_monoid M₁] [add_comm_monoid M₂]

/-- An involutive linear map is a linear equivalence. -/
def of_involutive {σ σ' : R →+* R} [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ]
  {module_M : module R M} (f : M →ₛₗ[σ] M) (hf : involutive f) :
  M ≃ₛₗ[σ] M :=
{ .. f, .. hf.to_perm f }

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

section automorphisms
variables [module R M]

instance automorphism_group : group (M ≃ₗ[R] M) :=
{ mul := λ f g, g.trans f,
  one := linear_equiv.refl R M,
  inv := λ f, f.symm,
  mul_assoc := λ f g h, rfl,
  mul_one := λ f, ext $ λ x, rfl,
  one_mul := λ f, ext $ λ x, rfl,
  mul_left_inv := λ f, ext $ f.left_inv }

/-- Restriction from `R`-linear automorphisms of `M` to `R`-linear endomorphisms of `M`,
promoted to a monoid hom. -/
@[simps]
def automorphism_group.to_linear_map_monoid_hom : (M ≃ₗ[R] M) →* (M →ₗ[R] M) :=
{ to_fun := coe,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

/-- The tautological action by `M ≃ₗ[R] M` on `M`.

This generalizes `function.End.apply_mul_action`. -/
instance apply_distrib_mul_action : distrib_mul_action (M ≃ₗ[R] M) M :=
{ smul := ($),
  smul_zero := linear_equiv.map_zero,
  smul_add := linear_equiv.map_add,
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl }

@[simp] protected lemma smul_def (f : M ≃ₗ[R] M) (a : M) :
  f • a = f a := rfl

/-- `linear_equiv.apply_distrib_mul_action` is faithful. -/
instance apply_has_faithful_smul : has_faithful_smul (M ≃ₗ[R] M) M :=
⟨λ _ _, linear_equiv.ext⟩

instance apply_smul_comm_class : smul_comm_class R (M ≃ₗ[R] M) M :=
{ smul_comm := λ r e m, (e.map_smul r m).symm }

instance apply_smul_comm_class' : smul_comm_class (M ≃ₗ[R] M) R M :=
{ smul_comm := linear_equiv.map_smul }

end automorphisms

section of_subsingleton

variables (M M₂) [module R M] [module R M₂] [subsingleton M] [subsingleton M₂]

/-- Any two modules that are subsingletons are isomorphic. -/
@[simps] def of_subsingleton : M ≃ₗ[R] M₂ :=
{ to_fun := λ _, 0,
  inv_fun := λ _, 0,
  left_inv := λ x, subsingleton.elim _ _,
  right_inv := λ x, subsingleton.elim _ _,
  .. (0 : M →ₗ[R] M₂)}

@[simp] lemma of_subsingleton_self : of_subsingleton M M = refl R M :=
by { ext, simp }

end of_subsingleton

end add_comm_monoid

end linear_equiv

namespace add_subgroup
variables {𝕜 α β : Type*} [semiring 𝕜] [add_comm_group α] [add_comm_group β] [module 𝕜 α]
  [module 𝕜 β]

@[simp]
lemma linear_equiv_map_symm_apply (e : α ≃ₗ[𝕜] β) {L : add_subgroup α} {g : L.map (e : α →+ β)} :
  (L.equiv_map e).symm g =
    ⟨e.symm g, set_like.mem_coe.1 $ (@set.mem_image_equiv α β _ e _).1 g.2⟩ :=
L.equiv_map_symm_apply (e : α ≃+ β) _

end add_subgroup

namespace module

/-- `g : R ≃+* S` is `R`-linear when the module structure on `S` is `module.comp_hom S g` . -/
@[simps]
def comp_hom.to_linear_equiv {R S : Type*} [semiring R] [semiring S] (g : R ≃+* S) :
  (by haveI := comp_hom S (↑g : R →+* S); exact (R ≃ₗ[R] S)) :=
by exact
{ to_fun := (g : R → S),
  inv_fun := (g.symm : S → R),
  map_smul' := g.map_mul,
  ..g }

end module

namespace distrib_mul_action

variables (R M) [semiring R] [add_comm_monoid M] [module R M]
variables [group S] [distrib_mul_action S M] [smul_comm_class S R M]

/-- Each element of the group defines a linear equivalence.

This is a stronger version of `distrib_mul_action.to_add_equiv`. -/
@[simps]
def to_linear_equiv (s : S) : M ≃ₗ[R] M :=
{ ..to_add_equiv M s,
  ..to_linear_map R M s }

/-- Each element of the group defines a module automorphism.

This is a stronger version of `distrib_mul_action.to_add_aut`. -/
@[simps]
def to_module_aut : S →* M ≃ₗ[R] M :=
{ to_fun := to_linear_equiv R M,
  map_one' := linear_equiv.ext $ one_smul _,
  map_mul' := λ a b, linear_equiv.ext $ mul_smul _ _ }

end distrib_mul_action

namespace add_equiv

section add_comm_monoid

variables [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [module R M] [module R M₂]

variable (e : M ≃+ M₂)

/-- An additive equivalence whose underlying function preserves `smul` is a linear equivalence. -/
def to_linear_equiv (h : ∀ (c : R) x, e (c • x) = c • e x) : M ≃ₗ[R] M₂ :=
{ map_smul' := h, .. e, }

@[simp] lemma coe_to_linear_equiv (h : ∀ (c : R) x, e (c • x) = c • e x) :
  ⇑(e.to_linear_equiv h) = e :=
rfl

@[simp] lemma coe_to_linear_equiv_symm (h : ∀ (c : R) x, e (c • x) = c • e x) :
  ⇑(e.to_linear_equiv h).symm = e.symm :=
rfl

/-- An additive equivalence between commutative additive monoids is a linear equivalence between
ℕ-modules -/
def to_nat_linear_equiv  : M ≃ₗ[ℕ] M₂ :=
e.to_linear_equiv $ λ c a, by { erw e.to_add_monoid_hom.map_nsmul, refl }

@[simp] lemma coe_to_nat_linear_equiv :
  ⇑(e.to_nat_linear_equiv) = e := rfl

@[simp] lemma to_nat_linear_equiv_to_add_equiv :
  e.to_nat_linear_equiv.to_add_equiv = e := by { ext, refl }

@[simp] lemma _root_.linear_equiv.to_add_equiv_to_nat_linear_equiv
  (e : M ≃ₗ[ℕ] M₂) : e.to_add_equiv.to_nat_linear_equiv = e := fun_like.coe_injective rfl

@[simp] lemma to_nat_linear_equiv_symm :
  (e.to_nat_linear_equiv).symm = e.symm.to_nat_linear_equiv := rfl

@[simp] lemma to_nat_linear_equiv_refl :
  ((add_equiv.refl M).to_nat_linear_equiv) = linear_equiv.refl ℕ M := rfl

@[simp] lemma to_nat_linear_equiv_trans (e₂ : M₂ ≃+ M₃) :
  (e.to_nat_linear_equiv).trans (e₂.to_nat_linear_equiv) = (e.trans e₂).to_nat_linear_equiv := rfl

end add_comm_monoid

section add_comm_group

variables [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]

variable (e : M ≃+ M₂)

/-- An additive equivalence between commutative additive groups is a linear
equivalence between ℤ-modules -/
def to_int_linear_equiv : M ≃ₗ[ℤ] M₂ :=
e.to_linear_equiv $ λ c a, e.to_add_monoid_hom.map_zsmul a c

@[simp] lemma coe_to_int_linear_equiv :
  ⇑(e.to_int_linear_equiv) = e := rfl

@[simp] lemma to_int_linear_equiv_to_add_equiv :
  e.to_int_linear_equiv.to_add_equiv = e := by { ext, refl }

@[simp] lemma _root_.linear_equiv.to_add_equiv_to_int_linear_equiv
  (e : M ≃ₗ[ℤ] M₂) : e.to_add_equiv.to_int_linear_equiv = e := fun_like.coe_injective rfl

@[simp] lemma to_int_linear_equiv_symm :
  (e.to_int_linear_equiv).symm = e.symm.to_int_linear_equiv := rfl

@[simp] lemma to_int_linear_equiv_refl :
  ((add_equiv.refl M).to_int_linear_equiv) = linear_equiv.refl ℤ M := rfl

@[simp] lemma to_int_linear_equiv_trans (e₂ : M₂ ≃+ M₃)  :
  (e.to_int_linear_equiv).trans (e₂.to_int_linear_equiv) = (e.trans e₂).to_int_linear_equiv :=
rfl

end add_comm_group

end add_equiv
