/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/
import algebra.star.self_adjoint
import algebra.module.equiv
import algebra.hom.non_unital_alg
import linear_algebra.prod

/-!
# The star operation, bundled as a star-linear equiv

We define `star_linear_equiv`, which is the star operation bundled as a star-linear map.
It is defined on a star algebra `A` over the base ring `R`.

This file also provides some lemmas that need `algebra.module.basic` imported to prove.

## TODO

- Define `star_linear_equiv` for noncommutative `R`. We only the commutative case for now since,
  in the noncommutative case, the ring hom needs to reverse the order of multiplication. This
  requires a ring hom of type `R →+* Rᵐᵒᵖ`, which is very undesirable in the commutative case.
  One way out would be to define a new typeclass `is_op R S` and have an instance `is_op R R`
  for commutative `R`.
- Also note that such a definition involving `Rᵐᵒᵖ` or `is_op R S` would require adding
  the appropriate `ring_hom_inv_pair` instances to be able to define the semilinear
  equivalence.
-/

section smul_lemmas
variables {R M : Type*}

@[simp] lemma star_int_cast_smul [ring R] [add_comm_group M] [module R M] [star_add_monoid M]
  (n : ℤ) (x : M) : star ((n : R) • x) = (n : R) • star x :=
map_int_cast_smul (star_add_equiv : M ≃+ M) R R n x

@[simp] lemma star_nat_cast_smul [semiring R] [add_comm_monoid M] [module R M] [star_add_monoid M]
  (n : ℕ) (x : M) : star ((n : R) • x) = (n : R) • star x :=
map_nat_cast_smul (star_add_equiv : M ≃+ M) R R n x

@[simp] lemma star_inv_int_cast_smul [division_ring R] [add_comm_group M] [module R M]
  [star_add_monoid M] (n : ℤ) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
map_inv_int_cast_smul (star_add_equiv : M ≃+ M) R R n x

@[simp] lemma star_inv_nat_cast_smul [division_ring R] [add_comm_group M] [module R M]
  [star_add_monoid M] (n : ℕ) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
map_inv_nat_cast_smul (star_add_equiv : M ≃+ M) R R n x

@[simp] lemma star_rat_cast_smul [division_ring R] [add_comm_group M] [module R M]
  [star_add_monoid M] (n : ℚ) (x : M) : star ((n : R) • x) = (n : R) • star x :=
map_rat_cast_smul (star_add_equiv : M ≃+ M) _ _ _ x

@[simp] lemma star_rat_smul {R : Type*} [add_comm_group R] [star_add_monoid R] [module ℚ R]
  (x : R) (n : ℚ) : star (n • x) = n • star x :=
map_rat_smul (star_add_equiv : R ≃+ R) _ _

end smul_lemmas

section star_linear_equiv

/-- If `A` is a module over a commutative `R` with compatible actions,
then `star` is a semilinear equivalence. -/
@[simps]
def star_linear_equiv (R : Type*) {A : Type*}
  [comm_ring R] [star_ring R] [semiring A] [star_ring A] [module R A] [star_module R A]  :
    A ≃ₗ⋆[R] A :=
{ to_fun := star,
  map_smul' := star_smul,
  .. star_add_equiv }

variables (R : Type*) (A : Type*)
  [semiring R] [star_semigroup R] [has_trivial_star R]
  [add_comm_group A] [module R A] [star_add_monoid A] [star_module R A]

/-- The self-adjoint elements of a star module, as a submodule. -/
def self_adjoint.submodule : submodule R A :=
{ smul_mem' := self_adjoint.smul_mem,
  ..self_adjoint A }

/-- The skew-adjoint elements of a star module, as a submodule. -/
def skew_adjoint.submodule : submodule R A :=
{ smul_mem' := skew_adjoint.smul_mem,
  ..skew_adjoint A }

variables {A} [invertible (2 : R)]

/-- The self-adjoint part of an element of a star module, as a linear map. -/
@[simps] def self_adjoint_part : A →ₗ[R] self_adjoint A :=
{ to_fun := λ x, ⟨(⅟2 : R) • (x + star x),
  by simp only [self_adjoint.mem_iff, star_smul, add_comm,
                  star_add_monoid.star_add, star_inv', star_bit0,
                  star_one, star_star, star_inv_of (2 : R), star_trivial]⟩,
  map_add' := λ x y, by { ext, simp [add_add_add_comm] },
  map_smul' := λ r x, by { ext, simp [←mul_smul,
          show ⅟ 2 * r = r * ⅟ 2, from commute.inv_of_left (commute.one_left r).bit0_left] } }

/-- The skew-adjoint part of an element of a star module, as a linear map. -/
@[simps] def skew_adjoint_part : A →ₗ[R] skew_adjoint A :=
{ to_fun := λ x, ⟨(⅟2 : R) • (x - star x),
    by simp only [skew_adjoint.mem_iff, star_smul, star_sub, star_star, star_trivial, ←smul_neg,
                  neg_sub]⟩,
  map_add' := λ x y, by { ext, simp only [sub_add, ←smul_add, sub_sub_eq_add_sub, star_add,
                                          add_subgroup.coe_mk, add_subgroup.coe_add] },
  map_smul' := λ r x, by { ext, simp [←mul_smul, ←smul_sub,
            show r * ⅟ 2 = ⅟ 2 * r, from commute.inv_of_right (commute.one_right r).bit0_right] } }

lemma star_module.self_adjoint_part_add_skew_adjoint_part (x : A) :
  (self_adjoint_part R x : A) + skew_adjoint_part R x = x :=
by simp only [smul_sub, self_adjoint_part_apply_coe, smul_add, skew_adjoint_part_apply_coe,
              add_add_sub_cancel, inv_of_two_smul_add_inv_of_two_smul]

variables (A)

/-- The decomposition of elements of a star module into their self- and skew-adjoint parts,
as a linear equivalence. -/
@[simps] def star_module.decompose_prod_adjoint : A ≃ₗ[R] self_adjoint A × skew_adjoint A :=
linear_equiv.of_linear
  ((self_adjoint_part R).prod (skew_adjoint_part R))
  ((self_adjoint.submodule R A).subtype.coprod (skew_adjoint.submodule R A).subtype)
  (by ext; simp)
  (linear_map.ext $ star_module.self_adjoint_part_add_skew_adjoint_part R)

end star_linear_equiv

section star_hom
set_option old_structure_cmd true

/-- `star_alg_hom_class F R A B` states that `F` is a type of `R`-algebra homomorphisms that
preserve the star operation.  -/
class star_alg_hom_class (F : Type*) (R A B : out_param $ Type*)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B]
  extends alg_hom_class F R A B, star_hom_class F A B

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] star_alg_hom_class.to_star_hom_class

/-- `star_alg_equiv_class F R A B` states that `F` is a type of `R`-algebra equivalence that
preserve the star operation.  -/
class star_alg_equiv_class (F : Type*) (R A B : out_param $ Type*)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B]
  extends alg_equiv_class F R A B :=
(map_star : ∀ (f : F) r, f (star r) = star (f r))

/-- `star_alg_hom_class F R A B` states that `F` is a type of `R`-algebra homomorphisms that
preserve the star operation.  -/
class non_unital_star_alg_hom_class (F : Type*) (R A B : out_param $ Type*)
  [monoid R] [non_unital_non_assoc_semiring A] [non_unital_non_assoc_semiring B]
  [distrib_mul_action R A] [distrib_mul_action R B] [has_star A] [has_star B]
  extends non_unital_alg_hom_class F R A B, star_hom_class F A B

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] non_unital_star_alg_hom_class.to_star_hom_class

@[priority 100] -- See note [lower instance priority]
instance star_alg_hom_class.to_non_unital_star_alg_hom_class (F R A B : Type*) [comm_semiring R]
  [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B]
  [star_alg_hom_class F R A B] : non_unital_star_alg_hom_class F R A B :=
{ map_smul := map_smul,
  ..‹star_alg_hom_class F R A B› }

@[priority 100] -- See note [lower instance priority]
instance star_alg_equiv_class.to_star_alg_hom_class (F R A B : Type*)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B]
  [star_alg_equiv_class F R A B] : star_alg_hom_class F R A B :=
{ coe := coe_fn,
  coe_injective' := fun_like.coe_injective,
  map_one := map_one,
  map_zero := map_zero,
  ..‹star_alg_equiv_class F R A B› }

/-- A star algebra homomorphism is an algebra homomorphism that preserves the star operation.  -/
structure non_unital_star_alg_hom (R A B : Type*)
  [monoid R] [non_unital_non_assoc_semiring A] [non_unital_non_assoc_semiring B]
  [distrib_mul_action R A] [distrib_mul_action R B] [has_star A] [has_star B]
  extends A →ₙₐ[R] B :=
(map_star' : ∀ (a : A), to_fun (star a) = star (to_fun a))

notation A ` →ₙₐ⋆[`:25 R `] ` B := non_unital_star_alg_hom R A B

namespace non_unital_star_alg_hom
variables {R A B C D : Type*} [comm_semiring R]
  [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B]
  [semiring C] [semiring D] [algebra R C] [algebra R D] [has_star C] [has_star D]

instance : non_unital_star_alg_hom_class (A →ₙₐ⋆[R] B) R A B :=
{ coe := to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_mul := λ f, f.map_mul',
  map_add := λ f, f.map_add',
  map_zero := λ f, f.map_zero',
  map_star := λ f, f.map_star',
  map_smul := λ f, f.map_smul' }

/-- see Note [function coercion] -/
instance : has_coe_to_fun (A →ₙₐ⋆[R] B) (λ _, A → B) := ⟨to_fun⟩

@[simp] lemma to_fun_eq_coe (f : A →ₙₐ⋆[R] B) : f.to_fun = ⇑f := rfl

initialize_simps_projections non_unital_star_alg_hom (to_fun → apply)

instance coe_non_unital_alg_hom : has_coe (A →ₙₐ⋆[R] B) (A →ₙₐ[R] B) :=
⟨non_unital_star_alg_hom.to_non_unital_alg_hom⟩

@[simp] lemma to_non_unital_alg_hom_eq_coe (f : A →ₙₐ⋆[R] B)  : f.to_non_unital_alg_hom = f := rfl

@[simp, norm_cast] lemma coe_fn_coe_non_unital_alg_hom (f : A →ₙₐ⋆[R] B) :
  ((f : A →ₙₐ[R] B) : A → B) = f := rfl

@[ext]
theorem ext {φ₁ φ₂ : A →ₙₐ⋆[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ := fun_like.ext _ _ H

section
variables (R A)
protected def id : A →ₙₐ⋆[R] A :=
{ map_star' := λ x, by { simp only [non_unital_alg_hom.to_fun_eq_coe, non_unital_alg_hom.coe_id,
                                    id.def], },
  ..non_unital_alg_hom.id R A }

@[simp] lemma coe_id : ⇑(non_unital_star_alg_hom.id R A) = id := rfl

lemma id_apply (x : A) : non_unital_star_alg_hom.id R A x = x := rfl
end

instance : has_one (A →ₙₐ⋆[R] A) :=
⟨{  map_star' := λ x, by simp only [non_unital_alg_hom.to_fun_eq_coe, non_unital_alg_hom.coe_one,
                                    id.def],
    ..(1 : A →ₙₐ[R] A) }⟩

@[simp] lemma coe_one : ((1 : A →ₙₐ⋆[R] A) : A → A) = id := rfl

/-- Composition of non-unital star algebra homomorphisms. -/
def comp (φ₁ : B →ₙₐ⋆[R] C) (φ₂ : A →ₙₐ⋆[R] B) : A →ₙₐ⋆[R] C :=
{ map_star' := λ x, by simp only [map_star, to_non_unital_alg_hom_eq_coe,
                                  non_unital_alg_hom.to_fun_eq_coe, non_unital_alg_hom.coe_comp,
                                  coe_fn_coe_non_unital_alg_hom, function.comp_app],
  .. φ₁.to_non_unital_alg_hom.comp ↑φ₂ }

@[simp] lemma coe_comp (φ₁ : B →ₙₐ⋆[R] C) (φ₂ : A →ₙₐ⋆[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ := rfl

lemma comp_apply (φ₁ : B →ₙₐ⋆[R] C) (φ₂ : A →ₙₐ⋆[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) := rfl

@[simp] theorem comp_id (φ : A →ₙₐ⋆[R] B) : φ.comp (non_unital_star_alg_hom.id R A) = φ :=
ext $ λ x, rfl

@[simp] theorem id_comp (φ : A →ₙₐ⋆[R] B) : (non_unital_star_alg_hom.id R B).comp φ = φ :=
ext $ λ x, rfl

theorem comp_assoc (φ₁ : C →ₙₐ⋆[R] D) (φ₂ : B →ₙₐ⋆[R] C) (φ₃ : A →ₙₐ⋆[R] B) :
  (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
ext $ λ x, rfl

end non_unital_star_alg_hom


/-- A star algebra homomorphism is an algebra homomorphism that preserves the star operation.  -/
structure star_alg_hom (R A B : Type*)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B]
  extends A →ₐ[R] B :=
(map_star' : ∀ (a : A), to_fun (star a) = star (to_fun a))

notation A ` →ₐ⋆[`:25 R `] ` B := star_alg_hom R A B

namespace star_alg_hom
variables {R A B C D : Type*}
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B]
  [semiring C] [algebra R C] [has_star C] [semiring D] [algebra R D] [has_star D]

instance : star_alg_hom_class (A →ₐ⋆[R] B) R A B :=
{ coe := to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_mul := λ f, f.map_mul',
  map_one := λ f, f.map_one',
  map_add := λ f, f.map_add',
  map_zero := λ f, f.map_zero',
  map_star := λ f, f.map_star',
  commutes := λ f, f.commutes' }

/-- see Note [function coercion] -/
instance : has_coe_to_fun (A →ₐ⋆[R] B) (λ _, A → B) := ⟨to_fun⟩

@[simp] lemma to_fun_eq_coe (f : A →ₐ⋆[R] B) : f.to_fun = ⇑f := rfl

initialize_simps_projections star_alg_hom (to_fun → apply)

instance coe_alg_hom : has_coe (A →ₐ⋆[R] B) (A →ₐ[R] B) := ⟨star_alg_hom.to_alg_hom⟩

@[simp] lemma to_alg_hom_eq_coe (f : A →ₐ⋆[R] B)  : f.to_alg_hom = f := rfl

@[simp, norm_cast] lemma coe_fn_coe_alg_hom (f : A →ₐ⋆[R] B) :
  ((f : A →ₐ[R] B) : A → B) = f := rfl

instance coe_non_unital_star_alg_hom : has_coe (A →ₐ⋆[R] B) (A →ₙₐ⋆[R] B) :=
⟨λ f, { map_smul' := map_smul f, ..f }⟩

@[simp, norm_cast] lemma coe_fn_coe_non_unital_star_alg_hom (f : A →ₐ⋆[R] B) :
  ((f : A →ₙₐ⋆[R] B) : A → B) = f := rfl

@[ext]
theorem ext {φ₁ φ₂ : A →ₐ⋆[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ := fun_like.ext _ _ H

section
variables (R A)
protected def id : A →ₐ⋆[R] A :=
{ map_star' := λ x, by simp only [alg_hom.to_fun_eq_coe, alg_hom.coe_id, id.def],
  ..alg_hom.id R A }

@[simp] lemma coe_id : ⇑(star_alg_hom.id R A) = id := rfl

@[simp] lemma id_to_star_alg_hom : (star_alg_hom.id R A : A →ₐ[R] A) = alg_hom.id _ _ := rfl
end

lemma id_apply (x : A) : star_alg_hom.id R A x = x := rfl

/-- Composition of star algebra homomorphisms. -/
def comp (φ₁ : B →ₐ⋆[R] C) (φ₂ : A →ₐ⋆[R] B) : A →ₐ⋆[R] C :=
{ map_star' := λ x, by simp only [map_star, to_alg_hom_eq_coe, alg_hom.to_fun_eq_coe,
                                  alg_hom.coe_comp, coe_fn_coe_alg_hom, function.comp_app],
  .. φ₁.to_alg_hom.comp ↑φ₂ }

@[simp] lemma coe_comp (φ₁ : B →ₐ⋆[R] C) (φ₂ : A →ₐ⋆[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ := rfl

lemma comp_apply (φ₁ : B →ₐ⋆[R] C) (φ₂ : A →ₐ⋆[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) := rfl

@[simp] theorem comp_id (φ : A →ₐ⋆[R] B) : φ.comp (star_alg_hom.id R A) = φ :=
ext $ λ x, rfl

@[simp] theorem id_comp (φ : A →ₐ⋆[R] B) : (star_alg_hom.id R B).comp φ = φ :=
ext $ λ x, rfl

theorem comp_assoc (φ₁ : C →ₐ⋆[R] D) (φ₂ : B →ₐ⋆[R] C) (φ₃ : A →ₐ⋆[R] B) :
  (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
ext $ λ x, rfl

end star_alg_hom

structure star_alg_equiv (R A B : Type*)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B]
  extends A ≃ₐ[R] B :=
(map_star' : ∀ (a : A), to_fun (star a) = star (to_fun a))

notation A ` ≃ₐ⋆[`:25 R `] ` B := star_alg_equiv R A B

namespace star_alg_equiv
variables {R A B C : Type*}
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B]
  [semiring C] [algebra R C] [has_star C]

instance : star_alg_equiv_class (A ≃ₐ⋆[R] B) R A B :=
{ coe := to_fun,
  inv := inv_fun,
  coe_injective' := λ e f h₁ h₂, by cases e; cases f; congr',
  left_inv := star_alg_equiv.left_inv,
  right_inv := star_alg_equiv.right_inv,
  map_mul := λ f, f.map_mul',
  map_add := λ f, f.map_add',
  map_star := λ f, f.map_star',
  commutes := λ f, f.commutes' }

/-- see Note [function coercion] -/
instance : has_coe_to_fun (A ≃ₐ⋆[R] B) (λ _, A → B) := ⟨to_fun⟩

@[simp] lemma to_fun_eq_coe (f : A ≃ₐ⋆[R] B) : f.to_fun = ⇑f := rfl

instance has_coe_to_alg_equiv : has_coe (A ≃ₐ⋆[R] B) (A ≃ₐ[R] B) := ⟨star_alg_equiv.to_alg_equiv⟩

@[simp] lemma to_alg_equiv_eq_coe (e : A ≃ₐ⋆[R] B): e.to_alg_equiv = e := rfl

@[simp, norm_cast] lemma coe_alg_equiv (e : A ≃ₐ⋆[R] B) : ((e : A ≃ₐ[R] B) : A → B) = e := rfl

instance has_coe_to_star_alg_hom : has_coe (A ≃ₐ⋆[R] B) (A →ₐ⋆[R] B) :=
⟨λ e, { to_fun := e.to_fun,
        map_one' := map_one e,
        map_mul' := map_mul e,
        map_zero' := map_zero e,
        map_add' := map_add e,
        commutes' := star_alg_hom_class.commutes e,
        map_star' := map_star e }⟩

@[simp, norm_cast] lemma coe_star_alg_hom (e : A ≃ₐ⋆[R] B) : ((e : A →ₐ⋆[R] B) : A → B) = e := rfl

@[ext] lemma ext {f g : A ≃ₐ⋆[R] B} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- The identity as a star algebra equivalence. -/
@[refl] def refl : A ≃ₐ⋆[R] A :=
{ commutes' := λ r, rfl,
  map_star' := λ r, by simp only [alg_equiv.to_fun_eq_coe, alg_equiv.one_apply],
  ..(1 : A ≃ₐ[R] A)}

@[simp] lemma coe_refl : ⇑(refl : A ≃ₐ⋆[R] A) = id := rfl

/-- The inverse of a star algebra equivalence. -/
@[symm] def symm (e : A ≃ₐ⋆[R] B) : B ≃ₐ⋆[R] A :=
{ map_star' := λ r,
  begin
    have h₁ : ∀ a, a = e (e.inv_fun a) := λ _, (e.right_inv _).symm,
    have h₂ : ∀ x, x = e.inv_fun (e x) := λ _, (e.left_inv _).symm,
    rw [h₁ r, ←map_star],
    change e.inv_fun (e (star (e.inv_fun r))) = star (e.inv_fun (e (e.inv_fun r))),
    rw [←h₁ r, ←h₂]
  end,
  ..e.to_alg_equiv.symm }

/-- See Note [custom simps projection] -/
def simps.symm_apply (e : A ≃ₐ⋆[R] B) : B → A := e.symm

initialize_simps_projections star_alg_equiv (to_fun → apply, inv_fun → symm_apply)

@[simp] lemma symm_symm (e : A ≃ₐ⋆[R] B) : e.symm.symm = e := by { ext, refl }

@[simp] lemma refl_symm : (star_alg_equiv.refl : A ≃ₐ⋆[R] A).symm = star_alg_equiv.refl := rfl

lemma symm_bijective : function.bijective (symm : (A ≃ₐ⋆[R] B) → (B ≃ₐ⋆[R] A)) :=
equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩

theorem left_inverse_symm (e : A ≃ₐ⋆[R] B) : function.left_inverse e.symm e := e.left_inv
theorem right_inverse_symm (e : A ≃ₐ⋆[R] B) : function.right_inverse e.symm e := e.right_inv

/-- Composition of star algebra equivalences. -/
@[trans] def trans (e₁ : A ≃ₐ⋆[R] B) (e₂ : B ≃ₐ⋆[R] C) : A ≃ₐ⋆[R] C :=
{ map_star' := λ a, by simp only [map_star, to_alg_equiv_eq_coe, alg_equiv.to_fun_eq_coe,
                                  alg_equiv.trans_apply, coe_alg_equiv],
  ..(e₁.to_alg_equiv.trans e₂.to_alg_equiv), }

@[simp] lemma apply_symm_apply (e : A ≃ₐ⋆[R] B) : ∀ x, e (e.symm x) = x :=
  e.to_alg_equiv.apply_symm_apply

@[simp] lemma symm_apply_apply (e : A ≃ₐ⋆[R] B) : ∀ x, e.symm (e x) = x :=
  e.to_alg_equiv.symm_apply_apply

@[simp] lemma symm_trans_apply (e₁ : A ≃ₐ⋆[R] B) (e₂ : B ≃ₐ⋆[R] C) (x : C) :
  (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) := rfl

@[simp] lemma coe_trans (e₁ : A ≃ₐ⋆[R] B) (e₂ : B ≃ₐ⋆[R] C) :
  ⇑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

@[simp] lemma trans_apply (e₁ : A ≃ₐ⋆[R] B) (e₂ : B ≃ₐ⋆[R] C) (x : A) :
  (e₁.trans e₂) x = e₂ (e₁ x) := rfl

@[simp] lemma comp_symm (e : A ≃ₐ⋆[R] B) :
  star_alg_hom.comp (e : A →ₐ⋆[R] B) ↑e.symm = star_alg_hom.id R B :=
by { ext, simp }

@[simp] lemma symm_comp (e : A ≃ₐ⋆[R] B) :
  star_alg_hom.comp ↑e.symm (e : A →ₐ⋆[R] B) = star_alg_hom.id R A :=
by { ext, simp }

/-- If a star algebra morphism has an inverse, it is a algebra isomorphism. -/
def of_star_alg_hom (f : A →ₐ⋆[R] B) (g : B →ₐ⋆[R] A) (h₁ : f.comp g = star_alg_hom.id R B)
  (h₂ : g.comp f = star_alg_hom.id R A) : A ≃ₐ⋆[R] B :=
{ to_fun    := f,
  inv_fun   := g,
  left_inv  := fun_like.ext_iff.1 h₂,
  right_inv := fun_like.ext_iff.1 h₁,
  ..f }

lemma coe_star_alg_hom_of_star_alg_hom (f : A →ₐ⋆[R] B) (g : B →ₐ⋆[R] A) (h₁ h₂) :
  ↑(of_star_alg_hom f g h₁ h₂) = f := star_alg_hom.ext $ λ _, rfl

@[simp]
lemma of_star_alg_hom_coe_star_alg_hom (f : A ≃ₐ⋆[R] B) (g : B →ₐ⋆[R] A) (h₁ h₂) :
  of_star_alg_hom ↑f g h₁ h₂ = f := ext $ λ _, rfl

lemma of_star_alg_hom_symm (f : A →ₐ⋆[R] B) (g : B →ₐ⋆[R] A) (h₁ h₂) :
  (of_star_alg_hom f g h₁ h₂).symm = of_star_alg_hom g f h₂ h₁ := rfl

/-- Promotes a bijective star algebra homomorphism to a star algebra equivalence. -/
noncomputable def of_bijective (f : A →ₐ⋆[R] B) (hf : function.bijective f) : A ≃ₐ⋆[R] B :=
{ .. ring_equiv.of_bijective (f : A →+* B) hf, .. f }

@[simp] lemma coe_of_bijective {f : A →ₐ⋆[R] B} {hf : function.bijective f} :
  (star_alg_equiv.of_bijective f hf : A → B) = f := rfl

lemma of_bijective_apply {f : A →ₐ⋆[R] B} {hf : function.bijective f} (a : A) :
  (star_alg_equiv.of_bijective f hf) a = f a := rfl

@[simps mul one {attrs := []}] instance aut : group (A ≃ₐ⋆[R] A) :=
{ mul := λ ϕ ψ, ψ.trans ϕ,
  mul_assoc := λ ϕ ψ χ, rfl,
  one := refl,
  one_mul := λ ϕ, ext $ λ x, rfl,
  mul_one := λ ϕ, ext $ λ x, rfl,
  inv := symm,
  mul_left_inv := λ ϕ, ext $ symm_apply_apply ϕ }

@[simp] lemma one_apply (x : A) : (1 : A ≃ₐ⋆[R] A) x = x := rfl

@[simp] lemma mul_apply (e₁ e₂ : A ≃ₐ⋆[R] A) (x : A) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

end star_alg_equiv

end star_hom
