/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.algebra.hom

/-!
# Isomorphisms of `R`-algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines bundled isomorphisms of `R`-algebras.

## Main definitions

* `alg_equiv R A B`: the type of `R`-algebra isomorphisms between `A` and `B`.

## Notations

* `A ≃ₐ[R] B` : `R`-algebra equivalence from `A` to `B`.
-/

open_locale big_operators

universes u v w u₁ v₁

set_option old_structure_cmd true
/-- An equivalence of algebras is an equivalence of rings commuting with the actions of scalars. -/
structure alg_equiv (R : Type u) (A : Type v) (B : Type w)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
  extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B :=
(commutes' : ∀ r : R, to_fun (algebra_map R A r) = algebra_map R B r)

attribute [nolint doc_blame] alg_equiv.to_ring_equiv
attribute [nolint doc_blame] alg_equiv.to_equiv
attribute [nolint doc_blame] alg_equiv.to_add_equiv
attribute [nolint doc_blame] alg_equiv.to_mul_equiv

notation A ` ≃ₐ[`:50 R `] ` A' := alg_equiv R A A'

/-- `alg_equiv_class F R A B` states that `F` is a type of algebra structure preserving
  equivalences. You should extend this class when you extend `alg_equiv`. -/
class alg_equiv_class (F : Type*) (R A B : out_param Type*)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
  extends ring_equiv_class F A B :=
(commutes : ∀ (f : F) (r : R), f (algebra_map R A r) = algebra_map R B r)

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] alg_equiv_class.to_ring_equiv_class

namespace alg_equiv_class

@[priority 100] -- See note [lower instance priority]
instance to_alg_hom_class (F R A B : Type*)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
  [h : alg_equiv_class F R A B] : alg_hom_class F R A B :=
{ coe := coe_fn,
  coe_injective' := fun_like.coe_injective,
  map_zero := map_zero,
  map_one := map_one,
  .. h }

@[priority 100]
instance to_linear_equiv_class (F R A B : Type*)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
  [h : alg_equiv_class F R A B] : linear_equiv_class F R A B :=
{ map_smulₛₗ := λ f, map_smulₛₗ f,
  ..h }

instance (F R A B : Type*) [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
  [h : alg_equiv_class F R A B] : has_coe_t F (A ≃ₐ[R] B) :=
{ coe := λ f,
  { to_fun := f,
  inv_fun := equiv_like.inv f,
  commutes' := alg_hom_class.commutes f,
  .. (f : A ≃+* B) } }

end alg_equiv_class

namespace alg_equiv

variables {R : Type u} {A₁ : Type v} {A₂ : Type w} {A₃ : Type u₁}

section semiring

variables [comm_semiring R] [semiring A₁] [semiring A₂] [semiring A₃]
variables [algebra R A₁] [algebra R A₂] [algebra R A₃]
variables (e : A₁ ≃ₐ[R] A₂)

instance : alg_equiv_class (A₁ ≃ₐ[R] A₂) R A₁ A₂ :=
{ coe := to_fun,
  inv := inv_fun,
  coe_injective' := λ f g h₁ h₂, by { cases f, cases g, congr' },
  map_add := map_add',
  map_mul := map_mul',
  commutes := commutes',
  left_inv := left_inv,
  right_inv := right_inv }

/--  Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance : has_coe_to_fun (A₁ ≃ₐ[R] A₂) (λ _, A₁ → A₂) := ⟨alg_equiv.to_fun⟩

@[simp, protected] lemma coe_coe {F : Type*} [alg_equiv_class F R A₁ A₂] (f : F) :
  ⇑(f : A₁ ≃ₐ[R] A₂) = f := rfl

@[ext]
lemma ext {f g : A₁ ≃ₐ[R] A₂} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

protected lemma congr_arg {f : A₁ ≃ₐ[R] A₂} {x x' : A₁} : x = x' → f x = f x' :=
fun_like.congr_arg f

protected lemma congr_fun {f g : A₁ ≃ₐ[R] A₂} (h : f = g) (x : A₁) : f x = g x :=
fun_like.congr_fun h x

protected lemma ext_iff {f g : A₁ ≃ₐ[R] A₂} : f = g ↔ ∀ x, f x = g x := fun_like.ext_iff

lemma coe_fun_injective : @function.injective (A₁ ≃ₐ[R] A₂) (A₁ → A₂) (λ e, (e : A₁ → A₂)) :=
fun_like.coe_injective

instance has_coe_to_ring_equiv : has_coe (A₁ ≃ₐ[R] A₂) (A₁ ≃+* A₂) := ⟨alg_equiv.to_ring_equiv⟩

@[simp] lemma coe_mk {to_fun inv_fun left_inv right_inv map_mul map_add commutes} :
  ⇑(⟨to_fun, inv_fun, left_inv, right_inv, map_mul, map_add, commutes⟩ : A₁ ≃ₐ[R] A₂) = to_fun :=
rfl

@[simp] theorem mk_coe (e : A₁ ≃ₐ[R] A₂) (e' h₁ h₂ h₃ h₄ h₅) :
  (⟨e, e', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂) = e := ext $ λ _, rfl

@[simp] lemma to_fun_eq_coe (e : A₁ ≃ₐ[R] A₂) : e.to_fun = e := rfl

@[simp] lemma to_equiv_eq_coe : e.to_equiv = e := rfl

@[simp] lemma to_ring_equiv_eq_coe : e.to_ring_equiv = e := rfl

@[simp, norm_cast] lemma coe_ring_equiv : ((e : A₁ ≃+* A₂) : A₁ → A₂) = e := rfl

lemma coe_ring_equiv' : (e.to_ring_equiv : A₁ → A₂) = e := rfl

lemma coe_ring_equiv_injective : function.injective (coe : (A₁ ≃ₐ[R] A₂) → (A₁ ≃+* A₂)) :=
λ e₁ e₂ h, ext $ ring_equiv.congr_fun h

protected lemma map_add : ∀ x y, e (x + y) = e x + e y := map_add e
protected lemma map_zero : e 0 = 0 := map_zero e
protected lemma map_mul : ∀ x y, e (x * y) = (e x) * (e y) := map_mul e
protected lemma map_one : e 1 = 1 := map_one e

@[simp] lemma commutes : ∀ (r : R), e (algebra_map R A₁ r) = algebra_map R A₂ r :=
  e.commutes'

@[simp] lemma map_smul (r : R) (x : A₁) : e (r • x) = r • e x :=
by simp only [algebra.smul_def, map_mul, commutes]

lemma map_sum {ι : Type*} (f : ι → A₁) (s : finset ι) :
  e (∑ x in s, f x) = ∑ x in s, e (f x) :=
e.to_add_equiv.map_sum f s

lemma map_finsupp_sum {α : Type*} [has_zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A₁) :
  e (f.sum g) = f.sum (λ i b, e (g i b)) :=
e.map_sum _ _

/-- Interpret an algebra equivalence as an algebra homomorphism.

This definition is included for symmetry with the other `to_*_hom` projections.
The `simp` normal form is to use the coercion of the `alg_hom_class.has_coe_t` instance. -/
def to_alg_hom : A₁ →ₐ[R] A₂ :=
{ map_one' := e.map_one, map_zero' := e.map_zero, ..e }

@[simp] lemma to_alg_hom_eq_coe : e.to_alg_hom = e := rfl

@[simp, norm_cast] lemma coe_alg_hom : ((e : A₁ →ₐ[R] A₂) : A₁ → A₂) = e :=
rfl

lemma coe_alg_hom_injective : function.injective (coe : (A₁ ≃ₐ[R] A₂) → (A₁ →ₐ[R] A₂)) :=
λ e₁ e₂ h, ext $ alg_hom.congr_fun h

/-- The two paths coercion can take to a `ring_hom` are equivalent -/
lemma coe_ring_hom_commutes : ((e : A₁ →ₐ[R] A₂) : A₁ →+* A₂) = ((e : A₁ ≃+* A₂) : A₁ →+* A₂) :=
rfl

protected lemma map_pow : ∀ (x : A₁) (n : ℕ), e (x ^ n) = (e x) ^ n := map_pow _
protected lemma injective : function.injective e := equiv_like.injective e
protected lemma surjective : function.surjective e := equiv_like.surjective e
protected lemma bijective : function.bijective e := equiv_like.bijective e

/-- Algebra equivalences are reflexive. -/
@[refl] def refl : A₁ ≃ₐ[R] A₁ := {commutes' := λ r, rfl, ..(1 : A₁ ≃+* A₁)}

instance : inhabited (A₁ ≃ₐ[R] A₁) := ⟨refl⟩

@[simp] lemma refl_to_alg_hom : ↑(refl : A₁ ≃ₐ[R] A₁) = alg_hom.id R A₁ := rfl

@[simp] lemma coe_refl : ⇑(refl : A₁ ≃ₐ[R] A₁) = id := rfl

/-- Algebra equivalences are symmetric. -/
@[symm]
def symm (e : A₁ ≃ₐ[R] A₂) : A₂ ≃ₐ[R] A₁ :=
{ commutes' := λ r, by { rw ←e.to_ring_equiv.symm_apply_apply (algebra_map R A₁ r), congr,
                         change _ = e _, rw e.commutes, },
  ..e.to_ring_equiv.symm, }

/-- See Note [custom simps projection] -/
def simps.symm_apply (e : A₁ ≃ₐ[R] A₂) : A₂ → A₁ := e.symm

initialize_simps_projections alg_equiv (to_fun → apply, inv_fun → symm_apply)

@[simp] lemma coe_apply_coe_coe_symm_apply {F : Type*} [alg_equiv_class F R A₁ A₂]
  (f : F) (x : A₂) : f ((f : A₁ ≃ₐ[R] A₂).symm x) = x := equiv_like.right_inv f x

@[simp] lemma coe_coe_symm_apply_coe_apply {F : Type*} [alg_equiv_class F R A₁ A₂]
  (f : F) (x : A₁) : (f : A₁ ≃ₐ[R] A₂).symm (f x) = x := equiv_like.left_inv f x

@[simp] lemma inv_fun_eq_symm {e : A₁ ≃ₐ[R] A₂} : e.inv_fun = e.symm := rfl

@[simp] lemma symm_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.symm = e :=
by { ext, refl, }

lemma symm_bijective : function.bijective (symm : (A₁ ≃ₐ[R] A₂) → (A₂ ≃ₐ[R] A₁)) :=
equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩

@[simp] lemma mk_coe' (e : A₁ ≃ₐ[R] A₂) (f h₁ h₂ h₃ h₄ h₅) :
  (⟨f, e, h₁, h₂, h₃, h₄, h₅⟩ : A₂ ≃ₐ[R] A₁) = e.symm :=
symm_bijective.injective $ ext $ λ x, rfl

@[simp] theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅) :
  (⟨f, f', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂).symm =
  { to_fun := f', inv_fun := f,
    ..(⟨f, f', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂).symm } := rfl

@[simp] theorem refl_symm : (alg_equiv.refl : A₁ ≃ₐ[R] A₁).symm = alg_equiv.refl := rfl

--this should be a simp lemma but causes a lint timeout
lemma to_ring_equiv_symm (f : A₁ ≃ₐ[R] A₁) : (f : A₁ ≃+* A₁).symm = f.symm := rfl

@[simp] lemma symm_to_ring_equiv : (e.symm : A₂ ≃+* A₁) = (e : A₁ ≃+* A₂).symm := rfl

/-- Algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : A₁ ≃ₐ[R] A₃ :=
{ commutes' := λ r, show e₂.to_fun (e₁.to_fun _) = _, by rw [e₁.commutes', e₂.commutes'],
  ..(e₁.to_ring_equiv.trans e₂.to_ring_equiv), }

@[simp] lemma apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e (e.symm x) = x :=
  e.to_equiv.apply_symm_apply

@[simp] lemma symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e.symm (e x) = x :=
  e.to_equiv.symm_apply_apply

@[simp] lemma symm_trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₃) :
  (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) := rfl

@[simp] lemma coe_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
  ⇑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

@[simp] lemma trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₁) :
  (e₁.trans e₂) x = e₂ (e₁ x) := rfl

@[simp] lemma comp_symm (e : A₁ ≃ₐ[R] A₂) :
  alg_hom.comp (e : A₁ →ₐ[R] A₂) ↑e.symm = alg_hom.id R A₂ :=
by { ext, simp }

@[simp] lemma symm_comp (e : A₁ ≃ₐ[R] A₂) :
  alg_hom.comp ↑e.symm (e : A₁ →ₐ[R] A₂) = alg_hom.id R A₁ :=
by { ext, simp }

theorem left_inverse_symm (e : A₁ ≃ₐ[R] A₂) : function.left_inverse e.symm e := e.left_inv

theorem right_inverse_symm (e : A₁ ≃ₐ[R] A₂) : function.right_inverse e.symm e := e.right_inv

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`. -/
def arrow_congr {A₁' A₂' : Type*} [semiring A₁'] [semiring A₂'] [algebra R A₁'] [algebra R A₂']
  (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') : (A₁ →ₐ[R] A₂) ≃ (A₁' →ₐ[R] A₂') :=
{ to_fun := λ f, (e₂.to_alg_hom.comp f).comp e₁.symm.to_alg_hom,
  inv_fun := λ f, (e₂.symm.to_alg_hom.comp f).comp e₁.to_alg_hom,
  left_inv := λ f, by { simp only [alg_hom.comp_assoc, to_alg_hom_eq_coe, symm_comp],
    simp only [←alg_hom.comp_assoc, symm_comp, alg_hom.id_comp, alg_hom.comp_id] },
  right_inv := λ f, by { simp only [alg_hom.comp_assoc, to_alg_hom_eq_coe, comp_symm],
    simp only [←alg_hom.comp_assoc, comp_symm, alg_hom.id_comp, alg_hom.comp_id] } }

lemma arrow_congr_comp {A₁' A₂' A₃' : Type*} [semiring A₁'] [semiring A₂'] [semiring A₃']
  [algebra R A₁'] [algebra R A₂'] [algebra R A₃'] (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂')
  (e₃ : A₃ ≃ₐ[R] A₃') (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₃) :
  arrow_congr e₁ e₃ (g.comp f) = (arrow_congr e₂ e₃ g).comp (arrow_congr e₁ e₂ f) :=
by { ext, simp only [arrow_congr, equiv.coe_fn_mk, alg_hom.comp_apply],
  congr, exact (e₂.symm_apply_apply _).symm }

@[simp] lemma arrow_congr_refl :
  arrow_congr alg_equiv.refl alg_equiv.refl = equiv.refl (A₁ →ₐ[R] A₂) :=
by { ext, refl }

@[simp] lemma arrow_congr_trans {A₁' A₂' A₃' : Type*} [semiring A₁'] [semiring A₂'] [semiring A₃']
  [algebra R A₁'] [algebra R A₂'] [algebra R A₃'] (e₁ : A₁ ≃ₐ[R] A₂) (e₁' : A₁' ≃ₐ[R] A₂')
  (e₂ : A₂ ≃ₐ[R] A₃) (e₂' : A₂' ≃ₐ[R] A₃') :
  arrow_congr (e₁.trans e₂) (e₁'.trans e₂') = (arrow_congr e₁ e₁').trans (arrow_congr e₂ e₂') :=
by { ext, refl }

@[simp] lemma arrow_congr_symm {A₁' A₂' : Type*} [semiring A₁'] [semiring A₂']
  [algebra R A₁'] [algebra R A₂'] (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') :
  (arrow_congr e₁ e₂).symm = arrow_congr e₁.symm e₂.symm :=
by { ext, refl }

/-- If an algebra morphism has an inverse, it is a algebra isomorphism. -/
def of_alg_hom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ : f.comp g = alg_hom.id R A₂)
  (h₂ : g.comp f = alg_hom.id R A₁) : A₁ ≃ₐ[R] A₂ :=
{ to_fun    := f,
  inv_fun   := g,
  left_inv  := alg_hom.ext_iff.1 h₂,
  right_inv := alg_hom.ext_iff.1 h₁,
  ..f }

lemma coe_alg_hom_of_alg_hom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
  ↑(of_alg_hom f g h₁ h₂) = f := alg_hom.ext $ λ _, rfl

@[simp]
lemma of_alg_hom_coe_alg_hom (f : A₁ ≃ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
  of_alg_hom ↑f g h₁ h₂ = f := ext $ λ _, rfl

lemma of_alg_hom_symm (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
  (of_alg_hom f g h₁ h₂).symm = of_alg_hom g f h₂ h₁ := rfl

/-- Promotes a bijective algebra homomorphism to an algebra equivalence. -/
noncomputable def of_bijective (f : A₁ →ₐ[R] A₂) (hf : function.bijective f) : A₁ ≃ₐ[R] A₂ :=
{ .. ring_equiv.of_bijective (f : A₁ →+* A₂) hf, .. f }

@[simp] lemma coe_of_bijective {f : A₁ →ₐ[R] A₂} {hf : function.bijective f} :
  (alg_equiv.of_bijective f hf : A₁ → A₂) = f := rfl

lemma of_bijective_apply {f : A₁ →ₐ[R] A₂} {hf : function.bijective f} (a : A₁) :
  (alg_equiv.of_bijective f hf) a = f a := rfl

/-- Forgetting the multiplicative structures, an equivalence of algebras is a linear equivalence. -/
@[simps apply] def to_linear_equiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ₗ[R] A₂ :=
{ to_fun    := e,
  map_smul' := e.map_smul,
  inv_fun   := e.symm,
  .. e }

@[simp] lemma to_linear_equiv_refl :
  (alg_equiv.refl : A₁ ≃ₐ[R] A₁).to_linear_equiv = linear_equiv.refl R A₁ := rfl

@[simp] lemma to_linear_equiv_symm (e : A₁ ≃ₐ[R] A₂) :
  e.to_linear_equiv.symm = e.symm.to_linear_equiv := rfl

@[simp] lemma to_linear_equiv_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
  (e₁.trans e₂).to_linear_equiv = e₁.to_linear_equiv.trans e₂.to_linear_equiv := rfl

theorem to_linear_equiv_injective : function.injective (to_linear_equiv : _ → (A₁ ≃ₗ[R] A₂)) :=
λ e₁ e₂ h, ext $ linear_equiv.congr_fun h

/-- Interpret an algebra equivalence as a linear map. -/
def to_linear_map : A₁ →ₗ[R] A₂ :=
e.to_alg_hom.to_linear_map

@[simp] lemma to_alg_hom_to_linear_map :
  (e : A₁ →ₐ[R] A₂).to_linear_map = e.to_linear_map := rfl

@[simp] lemma to_linear_equiv_to_linear_map :
  e.to_linear_equiv.to_linear_map = e.to_linear_map := rfl

@[simp] lemma to_linear_map_apply (x : A₁) : e.to_linear_map x = e x := rfl

theorem to_linear_map_injective : function.injective (to_linear_map : _ → (A₁ →ₗ[R] A₂)) :=
λ e₁ e₂ h, ext $ linear_map.congr_fun h

@[simp] lemma trans_to_linear_map (f : A₁ ≃ₐ[R] A₂) (g : A₂ ≃ₐ[R] A₃) :
  (f.trans g).to_linear_map = g.to_linear_map.comp f.to_linear_map := rfl

section of_linear_equiv

variables (l : A₁ ≃ₗ[R] A₂)
  (map_mul : ∀ x y : A₁, l (x * y) = l x * l y)
  (commutes : ∀ r : R, l (algebra_map R A₁ r) = algebra_map R A₂ r)

/--
Upgrade a linear equivalence to an algebra equivalence,
given that it distributes over multiplication and action of scalars.
-/
@[simps apply]
def of_linear_equiv : A₁ ≃ₐ[R] A₂ :=
{ to_fun := l,
  inv_fun := l.symm,
  map_mul' := map_mul,
  commutes' := commutes,
  ..l }

@[simp]
lemma of_linear_equiv_symm :
  (of_linear_equiv l map_mul commutes).symm = of_linear_equiv l.symm
    ((of_linear_equiv l map_mul commutes).symm.map_mul)
    ((of_linear_equiv l map_mul commutes).symm.commutes) :=
rfl

@[simp] lemma of_linear_equiv_to_linear_equiv (map_mul) (commutes) :
  of_linear_equiv e.to_linear_equiv map_mul commutes = e :=
by { ext, refl }

@[simp] lemma to_linear_equiv_of_linear_equiv :
  to_linear_equiv (of_linear_equiv l map_mul commutes) = l :=
by { ext, refl }

end of_linear_equiv

section of_ring_equiv

/-- Promotes a linear ring_equiv to an alg_equiv. -/
@[simps]
def of_ring_equiv {f : A₁ ≃+* A₂}
  (hf : ∀ x, f (algebra_map R A₁ x) = algebra_map R A₂ x) : A₁ ≃ₐ[R] A₂ :=
{ to_fun := f,
  inv_fun := f.symm,
  commutes' := hf,
  .. f }

end of_ring_equiv

@[simps mul one {attrs := []}] instance aut : group (A₁ ≃ₐ[R] A₁) :=
{ mul := λ ϕ ψ, ψ.trans ϕ,
  mul_assoc := λ ϕ ψ χ, rfl,
  one := refl,
  one_mul := λ ϕ, ext $ λ x, rfl,
  mul_one := λ ϕ, ext $ λ x, rfl,
  inv := symm,
  mul_left_inv := λ ϕ, ext $ symm_apply_apply ϕ }

@[simp] lemma one_apply (x : A₁) : (1 : A₁ ≃ₐ[R] A₁) x = x := rfl

@[simp] lemma mul_apply (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

/-- An algebra isomorphism induces a group isomorphism between automorphism groups -/
@[simps apply]
def aut_congr (ϕ : A₁ ≃ₐ[R] A₂) : (A₁ ≃ₐ[R] A₁) ≃* (A₂ ≃ₐ[R] A₂) :=
{ to_fun := λ ψ, ϕ.symm.trans (ψ.trans ϕ),
  inv_fun := λ ψ, ϕ.trans (ψ.trans ϕ.symm),
  left_inv := λ ψ, by { ext, simp_rw [trans_apply, symm_apply_apply] },
  right_inv := λ ψ, by { ext, simp_rw [trans_apply, apply_symm_apply] },
  map_mul' := λ ψ χ, by { ext, simp only [mul_apply, trans_apply, symm_apply_apply] } }

@[simp] lemma aut_congr_refl : aut_congr (alg_equiv.refl) = mul_equiv.refl (A₁ ≃ₐ[R] A₁) :=
by { ext, refl }

@[simp] lemma aut_congr_symm (ϕ : A₁ ≃ₐ[R] A₂) : (aut_congr ϕ).symm = aut_congr ϕ.symm := rfl

@[simp] lemma aut_congr_trans (ϕ : A₁ ≃ₐ[R] A₂) (ψ : A₂ ≃ₐ[R] A₃) :
  (aut_congr ϕ).trans (aut_congr ψ) = aut_congr (ϕ.trans ψ) := rfl

/-- The tautological action by `A₁ ≃ₐ[R] A₁` on `A₁`.

This generalizes `function.End.apply_mul_action`. -/
instance apply_mul_semiring_action : mul_semiring_action (A₁ ≃ₐ[R] A₁) A₁ :=
{ smul := ($),
  smul_zero := alg_equiv.map_zero,
  smul_add := alg_equiv.map_add,
  smul_one := alg_equiv.map_one,
  smul_mul := alg_equiv.map_mul,
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl }

@[simp] protected lemma smul_def (f : A₁ ≃ₐ[R] A₁) (a : A₁) : f • a = f a := rfl

instance apply_has_faithful_smul : has_faithful_smul (A₁ ≃ₐ[R] A₁) A₁ :=
⟨λ _ _, alg_equiv.ext⟩

instance apply_smul_comm_class : smul_comm_class R (A₁ ≃ₐ[R] A₁) A₁ :=
{ smul_comm := λ r e a, (e.map_smul r a).symm }

instance apply_smul_comm_class' : smul_comm_class (A₁ ≃ₐ[R] A₁) R A₁ :=
{ smul_comm := λ e r a, (e.map_smul r a) }

@[simp] lemma algebra_map_eq_apply (e : A₁ ≃ₐ[R] A₂) {y : R} {x : A₁} :
  (algebra_map R A₂ y = e x) ↔ (algebra_map R A₁ y = x) :=
⟨λ h, by simpa using e.symm.to_alg_hom.algebra_map_eq_apply h,
 λ h, e.to_alg_hom.algebra_map_eq_apply h⟩

end semiring

section comm_semiring

variables [comm_semiring R] [comm_semiring A₁] [comm_semiring A₂]
variables [algebra R A₁] [algebra R A₂] (e : A₁ ≃ₐ[R] A₂)

lemma map_prod {ι : Type*} (f : ι → A₁) (s : finset ι) :
  e (∏ x in s, f x) = ∏ x in s, e (f x) :=
map_prod _ f s

lemma map_finsupp_prod {α : Type*} [has_zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A₁) :
  e (f.prod g) = f.prod (λ i a, e (g i a)) :=
map_finsupp_prod _ f g

end comm_semiring

section ring

variables [comm_semiring R] [ring A₁] [ring A₂]
variables [algebra R A₁] [algebra R A₂] (e : A₁ ≃ₐ[R] A₂)

protected lemma map_neg (x) : e (-x) = -e x := map_neg e x
protected lemma map_sub (x y) : e (x - y) = e x - e y := map_sub e x y

end ring

end alg_equiv

namespace mul_semiring_action

variables {M G : Type*} (R A : Type*) [comm_semiring R] [semiring A] [algebra R A]

section
variables [group G] [mul_semiring_action G A] [smul_comm_class G R A]

/-- Each element of the group defines a algebra equivalence.

This is a stronger version of `mul_semiring_action.to_ring_equiv` and
`distrib_mul_action.to_linear_equiv`. -/
@[simps]
def to_alg_equiv (g : G) : A ≃ₐ[R] A :=
{ .. mul_semiring_action.to_ring_equiv _ _ g,
  .. mul_semiring_action.to_alg_hom R A g }

theorem to_alg_equiv_injective [has_faithful_smul G A] :
  function.injective (mul_semiring_action.to_alg_equiv R A : G → A ≃ₐ[R] A) :=
λ m₁ m₂ h, eq_of_smul_eq_smul $ λ r, alg_equiv.ext_iff.1 h r

end

end mul_semiring_action
