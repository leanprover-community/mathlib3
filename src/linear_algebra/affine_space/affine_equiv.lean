/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import linear_algebra.affine_space.basic

/-!
# Affine equivalences

In this file we define `affine_equiv k P₁ P₂` (notation: `P₁ ≃ᵃ[k] P₂`) to be the type of affine
equivalences between `P₁` and `P₂, i.e., equivalences such that both forward and inverse maps are
affine maps.

We define the following equivalences:

* `affine_equiv.refl k P`: the identity map as an `affine_equiv`;

* `e.symm`: the inverse map of an `affine_equiv` as an `affine_equiv`;

* `e.trans e'`: composition of two `affine_equiv`s; note that the order follows `mathlib`'s
  `category_theory` convention (apply `e`, then `e'`), not the convention used in function
  composition and compositions of bundled morphisms.

## Tags

affine space, affine equivalence
-/

open function set

/-- An affine equivalence is an equivalence between affine spaces such that both forward
and inverse maps are affine.

We define it using an `equiv` for the map and a `linear_equiv` for the linear part in order
to allow affine equivalences with good definitional equalities. -/
@[nolint has_inhabited_instance]
structure affine_equiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [ring k]
  [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁]
  [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] extends P₁ ≃ P₂ :=
(linear : V₁ ≃ₗ[k] V₂)
(map_vadd' : ∀ (p : P₁) (v : V₁), to_equiv (v +ᵥ p) = linear v +ᵥ to_equiv p)

notation P₁ ` ≃ᵃ[`:25 k:25 `] `:0 P₂:0 := affine_equiv k P₁ P₂

instance (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*)
  [ring k]
  [add_comm_group V1] [module k V1] [affine_space V1 P1]
  [add_comm_group V2] [module k V2] [affine_space V2 P2] :
  has_coe_to_fun (P1 ≃ᵃ[k] P2) :=
⟨_, λ e, e.to_fun⟩

variables {k V₁ V₂ V₃ V₄ P₁ P₂ P₃ P₄ : Type*} [ring k]
  [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁]
  [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂]
  [add_comm_group V₃] [semimodule k V₃] [add_torsor V₃ P₃]
  [add_comm_group V₄] [semimodule k V₄] [add_torsor V₄ P₄]

namespace linear_equiv

/-- Interpret a linear equivalence between modules as an affine equivalence. -/
def to_affine_equiv (e : V₁ ≃ₗ[k] V₂) : V₁ ≃ᵃ[k] V₂ :=
{ to_equiv := e.to_equiv,
  linear := e,
  map_vadd' := λ p v, e.map_add v p }

@[simp] lemma coe_to_affine_equiv (e : V₁ ≃ₗ[k] V₂) : ⇑e.to_affine_equiv = e := rfl

end linear_equiv

namespace affine_equiv

variables (k P₁)

include V₁

/-- Identity map as an `affine_equiv`. -/
@[refl] def refl : P₁ ≃ᵃ[k] P₁ :=
{ to_equiv := equiv.refl P₁,
  linear := linear_equiv.refl k V₁,
  map_vadd' := λ _ _, rfl }

@[simp] lemma coe_refl : ⇑(refl k P₁) = id := rfl

lemma refl_apply (x : P₁) : refl k P₁ x = x := rfl

@[simp] lemma to_equiv_refl : (refl k P₁).to_equiv = equiv.refl P₁ := rfl

@[simp] lemma linear_refl : (refl k P₁).linear = linear_equiv.refl k V₁ := rfl

variables {k P₁}

include V₂

@[simp] lemma map_vadd (e : P₁ ≃ᵃ[k] P₂) (p : P₁) (v : V₁) : e (v +ᵥ p) = e.linear v +ᵥ e p :=
e.map_vadd' p v

@[simp] lemma coe_to_equiv (e : P₁ ≃ᵃ[k] P₂) : ⇑e.to_equiv = e := rfl

/-- Reinterpret an `affine_equiv` as an `affine_map`. -/
def to_affine_map (e : P₁ ≃ᵃ[k] P₂) : P₁ →ᵃ[k] P₂ := { to_fun := e, .. e }

@[simp] lemma coe_to_affine_map (e : P₁ ≃ᵃ[k] P₂) :
  (e.to_affine_map : P₁ → P₂) = (e : P₁ → P₂) := 
rfl

@[simp] lemma to_affine_map_mk (f : P₁ ≃ P₂) (f' : V₁ ≃ₗ[k] V₂) (h) :
  to_affine_map (mk f f' h) = ⟨f, f', h⟩ :=
rfl

@[simp] lemma linear_to_affine_map (e : P₁ ≃ᵃ[k] P₂) : e.to_affine_map.linear = e.linear := rfl

lemma injective_to_affine_map : injective (to_affine_map : (P₁ ≃ᵃ[k] P₂) → (P₁ →ᵃ[k] P₂)) :=
begin
  rintros ⟨e, el, h⟩ ⟨e', el', h'⟩ H,
  simp only [to_affine_map_mk, equiv.coe_inj, linear_equiv.to_linear_map_inj] at H,
  congr,
  exacts [H.1, H.2]
end

@[simp] lemma to_affine_map_inj {e e' : P₁ ≃ᵃ[k] P₂} :
  e.to_affine_map = e'.to_affine_map ↔ e = e' :=
injective_to_affine_map.eq_iff

@[ext] lemma ext {e e' : P₁ ≃ᵃ[k] P₂} (h : ∀ x, e x = e' x) : e = e' :=
injective_to_affine_map $ affine_map.ext h

lemma injective_coe_fn : injective (λ (e : P₁ ≃ᵃ[k] P₂) (x : P₁), e x) :=
λ e e' H, ext $ congr_fun H

@[simp, norm_cast] lemma coe_fn_inj {e e' : P₁ ≃ᵃ[k] P₂} : ⇑e = e' ↔ e = e' :=
injective_coe_fn.eq_iff

lemma injective_to_equiv : injective (to_equiv : (P₁ ≃ᵃ[k] P₂) → (P₁ ≃ P₂)) :=
λ e e' H, ext $ equiv.ext_iff.1 H

@[simp] lemma to_equiv_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.to_equiv = e'.to_equiv ↔ e = e' :=
injective_to_equiv.eq_iff

/-- Construct an affine equivalence by verifying the relation between the map and its linear part at
one base point. Namely, this function takes an equivalence `e : P₁ ≃ P₂`, a linear equivalece
`e' : V₁ ≃ₗ[k] V₂`, and a point `p` such that for any other point `p'` we have
`e p' = e' (p' -ᵥ p) +ᵥ e p`. -/
def mk' (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p : P₁) (h : ∀ p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p) :
  P₁ ≃ᵃ[k] P₂ :=
{ to_equiv := e,
  linear := e',
  .. affine_map.mk' e (e' : V₁ →ₗ[k] V₂) p h }

@[simp] lemma coe_mk' (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h) : ⇑(mk' e e' p h) = e := rfl
@[simp] lemma to_equiv_mk' (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h) :
  (mk' e e' p h).to_equiv = e := rfl
@[simp] lemma linear_mk' (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h) :
  (mk' e e' p h).linear = e' := rfl

/-- Inverse of an affine equivalence as an affine equivalence. -/
@[symm] def symm (e : P₁ ≃ᵃ[k] P₂) : P₂ ≃ᵃ[k] P₁ :=
{ to_equiv := e.to_equiv.symm,
  linear := e.linear.symm,
  map_vadd' := λ v p, e.to_equiv.symm.apply_eq_iff_eq_symm_apply.2 $
    by simpa using (e.to_equiv.apply_symm_apply v).symm }

@[simp] lemma symm_to_equiv (e : P₁ ≃ᵃ[k] P₂) : e.to_equiv.symm = e.symm.to_equiv := rfl

@[simp] lemma symm_linear (e : P₁ ≃ᵃ[k] P₂) : e.linear.symm = e.symm.linear := rfl

protected lemma bijective (e : P₁ ≃ᵃ[k] P₂) : bijective e := e.to_equiv.bijective
protected lemma surjective (e : P₁ ≃ᵃ[k] P₂) : surjective e := e.to_equiv.surjective
protected lemma injective (e : P₁ ≃ᵃ[k] P₂) : injective e := e.to_equiv.injective

@[simp] lemma range_eq (e : P₁ ≃ᵃ[k] P₂) : range e = univ := e.surjective.range_eq

@[simp] lemma apply_symm_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₂) : e (e.symm p) = p :=
e.to_equiv.apply_symm_apply p

@[simp] lemma symm_apply_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₁) : e.symm (e p) = p :=
e.to_equiv.symm_apply_apply p

lemma apply_eq_iff_eq_symm_apply (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : e p₁ = p₂ ↔ p₁ = e.symm p₂ :=
e.to_equiv.apply_eq_iff_eq_symm_apply

@[simp] lemma apply_eq_iff_eq (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂ : P₁} : e p₁ = e p₂ ↔ p₁ = p₂ :=
e.to_equiv.apply_eq_iff_eq

omit V₂

@[simp] lemma symm_refl : (refl k P₁).symm = refl k P₁ := rfl

include V₂ V₃

/-- Composition of two `affine_equiv`alences, applied left to right. -/
@[trans] def trans (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) : P₁ ≃ᵃ[k] P₃ :=
{ to_equiv := e.to_equiv.trans e'.to_equiv,
  linear := e.linear.trans e'.linear,
  map_vadd' := λ p v, by simp only [linear_equiv.trans_apply, coe_to_equiv, (∘),
    equiv.coe_trans, map_vadd] }

@[simp] lemma coe_trans (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) : ⇑(e.trans e') = e' ∘ e := rfl

lemma trans_apply (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) (p : P₁) : e.trans e' p = e' (e p) := rfl

include V₄

lemma trans_assoc (e₁ : P₁ ≃ᵃ[k] P₂) (e₂ : P₂ ≃ᵃ[k] P₃) (e₃ : P₃ ≃ᵃ[k] P₄) :
  (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) :=
ext $ λ _, rfl

omit V₃ V₄

@[simp] lemma trans_refl (e : P₁ ≃ᵃ[k] P₂) : e.trans (refl k P₂) = e :=
ext $ λ _, rfl

@[simp] lemma refl_trans (e : P₁ ≃ᵃ[k] P₂) : (refl k P₁).trans e = e :=
ext $ λ _, rfl

@[simp] lemma trans_symm (e : P₁ ≃ᵃ[k] P₂) : e.trans e.symm = refl k P₁ :=
ext e.symm_apply_apply

@[simp] lemma symm_trans (e : P₁ ≃ᵃ[k] P₂) : e.symm.trans e = refl k P₂ :=
ext e.apply_symm_apply

omit V₂

instance : group (P₁ ≃ᵃ[k] P₁) :=
{ one := refl k P₁,
  mul := λ e e', e'.trans e,
  inv := symm,
  mul_assoc := λ e₁ e₂ e₃, trans_assoc _ _ _,
  one_mul := trans_refl,
  mul_one := refl_trans,
  mul_left_inv := trans_symm }

lemma one_def : (1 : P₁ ≃ᵃ[k] P₁) = refl k P₁ := rfl

@[simp] lemma coe_one : ⇑(1 : P₁ ≃ᵃ[k] P₁) = id := rfl

lemma mul_def (e e' : P₁ ≃ᵃ[k] P₁) : e * e' = e'.trans e := rfl

@[simp] lemma coe_mul (e e' : P₁ ≃ᵃ[k] P₁) : ⇑(e * e') = e ∘ e' := rfl

lemma inv_def (e : P₁ ≃ᵃ[k] P₁) : e⁻¹ = e.symm := rfl

variable (k)

/-- The map `v ↦ v +ᵥ b` as an affine equivalence between a module `V` and an affine space `P` with
tangent space `V`. -/
def vadd_const (b : P₁) : V₁ ≃ᵃ[k] P₁ :=
{ to_equiv := equiv.vadd_const b,
  linear := linear_equiv.refl _ _,
  map_vadd' := λ p v, (vadd_assoc _ _ _).symm }

@[simp] lemma linear_vadd_const (b : P₁) : (vadd_const k b).linear = linear_equiv.refl k V₁ := rfl

@[simp] lemma vadd_const_apply (b : P₁) (v : V₁) : vadd_const k b v = v +ᵥ b := rfl

@[simp] lemma vadd_const_symm_apply (b p : P₁) : (vadd_const k b).symm p = p -ᵥ b := rfl

variable (P₁)

/-- The map `p ↦ v +ᵥ p` as an affine automorphism of an affine space. -/
def const_vadd (v : V₁) : P₁ ≃ᵃ[k] P₁ :=
{ to_equiv := equiv.const_vadd P₁ v,
  linear := linear_equiv.refl _ _,
  map_vadd' := λ p w, vadd_comm _ _ _ _ }

@[simp] lemma linear_const_vadd (v : V₁) : (const_vadd k P₁ v).linear = linear_equiv.refl _ _ := rfl

@[simp] lemma const_vadd_apply (v : V₁) (p : P₁) : const_vadd k P₁ v p = v +ᵥ p := rfl

@[simp] lemma const_vadd_symm_apply (v : V₁) (p : P₁) : (const_vadd k P₁ v).symm p = -v +ᵥ p := rfl

end affine_equiv
