/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel, Eric Wieser
-/
import linear_algebra.orientation
import algebra.order.smul
import data.complex.basic
import data.fin.vec_notation
import field_theory.tower
import algebra.char_p.invertible

/-!
# Complex number as a vector space over `ℝ`

This file contains the following instances:
* Any `•`-structure (`has_smul`, `mul_action`, `distrib_mul_action`, `module`, `algebra`) on
  `ℝ` imbues a corresponding structure on `ℂ`. This includes the statement that `ℂ` is an `ℝ`
  algebra.
* any complex vector space is a real vector space;
* any finite dimensional complex vector space is a finite dimensional real vector space;
* the space of `ℝ`-linear maps from a real vector space to a complex vector space is a complex
  vector space.

It also defines bundled versions of four standard maps (respectively, the real part, the imaginary
part, the embedding of `ℝ` in `ℂ`, and the complex conjugate):

* `complex.re_lm` (`ℝ`-linear map);
* `complex.im_lm` (`ℝ`-linear map);
* `complex.of_real_am` (`ℝ`-algebra (homo)morphism);
* `complex.conj_ae` (`ℝ`-algebra equivalence).

It also provides a universal property of the complex numbers `complex.lift`, which constructs a
`ℂ →ₐ[ℝ] A` into any `ℝ`-algebra `A` given a square root of `-1`.

In addition, this file provides a decomposition into `real_part` and `imaginary_part` for any
element of a `star_module` over `ℂ`.

## Notation

* `ℜ` and `ℑ` for the `real_part` and `imaginary_part`, respectively, in the locale
  `complex_star_module`.
-/

namespace complex

open_locale complex_conjugate

variables {R : Type*} {S : Type*}

section

variables [has_smul R ℝ]

/- The useless `0` multiplication in `smul` is to make sure that
`restrict_scalars.module ℝ ℂ ℂ = complex.module` definitionally. -/
instance : has_smul R ℂ :=
{ smul := λ r x, ⟨r • x.re - 0 * x.im, r • x.im + 0 * x.re⟩ }

lemma smul_re (r : R) (z : ℂ) : (r • z).re = r • z.re := by simp [(•)]
lemma smul_im (r : R) (z : ℂ) : (r • z).im = r • z.im := by simp [(•)]

@[simp] lemma real_smul {x : ℝ} {z : ℂ} : x • z = x * z := rfl

end

instance [has_smul R ℝ] [has_smul S ℝ] [smul_comm_class R S ℝ] : smul_comm_class R S ℂ :=
{ smul_comm := λ r s x, by ext; simp [smul_re, smul_im, smul_comm] }

instance [has_smul R S] [has_smul R ℝ] [has_smul S ℝ] [is_scalar_tower R S ℝ] :
  is_scalar_tower R S ℂ :=
{ smul_assoc := λ r s x, by ext; simp [smul_re, smul_im, smul_assoc] }

instance [has_smul R ℝ] [has_smul Rᵐᵒᵖ ℝ] [is_central_scalar R ℝ] :
  is_central_scalar R ℂ :=
{ op_smul_eq_smul := λ r x, by ext; simp [smul_re, smul_im, op_smul_eq_smul] }

instance [monoid R] [mul_action R ℝ] : mul_action R ℂ :=
{ one_smul := λ x, by ext; simp [smul_re, smul_im, one_smul],
  mul_smul := λ r s x, by ext; simp [smul_re, smul_im, mul_smul] }

instance [distrib_smul R ℝ] : distrib_smul R ℂ :=
{ smul_add := λ r x y, by ext; simp [smul_re, smul_im, smul_add],
  smul_zero := λ r, by ext; simp [smul_re, smul_im, smul_zero] }

instance [semiring R] [distrib_mul_action R ℝ] : distrib_mul_action R ℂ :=
{ ..complex.distrib_smul }

instance [semiring R] [module R ℝ] : module R ℂ :=
{ add_smul := λ r s x, by ext; simp [smul_re, smul_im, add_smul],
  zero_smul := λ r, by ext; simp [smul_re, smul_im, zero_smul] }

instance [comm_semiring R] [algebra R ℝ] : algebra R ℂ :=
{ smul := (•),
  smul_def' := λ r x, by ext; simp [smul_re, smul_im, algebra.smul_def],
  commutes' := λ r ⟨xr, xi⟩, by ext; simp [smul_re, smul_im, algebra.commutes],
  ..complex.of_real.comp (algebra_map R ℝ) }

instance : star_module ℝ ℂ :=
⟨λ r x, by simp only [star_def, star_trivial, real_smul, map_mul, conj_of_real]⟩

@[simp] lemma coe_algebra_map : (algebra_map ℝ ℂ : ℝ → ℂ) = coe := rfl

section
variables {A : Type*} [semiring A] [algebra ℝ A]

/-- We need this lemma since `complex.coe_algebra_map` diverts the simp-normal form away from
`alg_hom.commutes`. -/
@[simp] lemma _root_.alg_hom.map_coe_real_complex (f : ℂ →ₐ[ℝ] A) (x : ℝ) :
  f x = algebra_map ℝ A x :=
f.commutes x

/-- Two `ℝ`-algebra homomorphisms from ℂ are equal if they agree on `complex.I`. -/
@[ext]
lemma alg_hom_ext ⦃f g : ℂ →ₐ[ℝ] A⦄ (h : f I = g I) : f = g :=
begin
  ext ⟨x, y⟩,
  simp only [mk_eq_add_mul_I, alg_hom.map_add, alg_hom.map_coe_real_complex, alg_hom.map_mul, h]
end

end

section
open_locale complex_order

protected lemma ordered_smul : ordered_smul ℝ ℂ :=
ordered_smul.mk' $ λ a b r hab hr, ⟨by simp [hr, hab.1.le], by simp [hab.2]⟩

localized "attribute [instance] complex.ordered_smul" in complex_order

end

open submodule finite_dimensional

/-- `ℂ` has a basis over `ℝ` given by `1` and `I`. -/
noncomputable def basis_one_I : basis (fin 2) ℝ ℂ :=
basis.of_equiv_fun
{ to_fun := λ z, ![z.re, z.im],
  inv_fun := λ c, c 0 + c 1 • I,
  left_inv := λ z, by simp,
  right_inv := λ c, by { ext i, fin_cases i; simp },
  map_add' := λ z z', by simp,
  -- why does `simp` not know how to apply `smul_cons`, which is a `@[simp]` lemma, here?
  map_smul' := λ c z, by simp [matrix.smul_cons c z.re, matrix.smul_cons c z.im] }

@[simp] lemma coe_basis_one_I_repr (z : ℂ) : ⇑(basis_one_I.repr z) = ![z.re, z.im] := rfl

@[simp] lemma coe_basis_one_I : ⇑basis_one_I = ![1, I] :=
funext $ λ i, basis.apply_eq_iff.mpr $ finsupp.ext $ λ j,
by fin_cases i; fin_cases j;
    simp only [coe_basis_one_I_repr, finsupp.single_eq_of_ne, matrix.cons_val_zero,
      matrix.cons_val_one, matrix.head_cons, fin.one_eq_zero_iff, ne.def, not_false_iff, I_re,
      nat.succ_succ_ne_one, one_im, I_im, one_re, finsupp.single_eq_same, fin.zero_eq_one_iff]

instance : finite_dimensional ℝ ℂ := of_fintype_basis basis_one_I

@[simp] lemma finrank_real_complex : finite_dimensional.finrank ℝ ℂ = 2 :=
by rw [finrank_eq_card_basis basis_one_I, fintype.card_fin]

@[simp] lemma dim_real_complex : module.rank ℝ ℂ = 2 :=
by simp [← finrank_eq_dim, finrank_real_complex]

lemma {u} dim_real_complex' : cardinal.lift.{u} (module.rank ℝ ℂ) = 2 :=
by simp [← finrank_eq_dim, finrank_real_complex, bit0]

/-- `fact` version of the dimension of `ℂ` over `ℝ`, locally useful in the definition of the
circle. -/
lemma finrank_real_complex_fact : fact (finrank ℝ ℂ = 2) := ⟨finrank_real_complex⟩

/-- The standard orientation on `ℂ`. -/
protected noncomputable def orientation : orientation ℝ ℂ (fin 2) := complex.basis_one_I.orientation

end complex

/- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
@[priority 900]
instance module.complex_to_real (E : Type*) [add_comm_group E] [module ℂ E] : module ℝ E :=
restrict_scalars.module ℝ ℂ E

instance module.real_complex_tower (E : Type*) [add_comm_group E] [module ℂ E] :
  is_scalar_tower ℝ ℂ E :=
restrict_scalars.is_scalar_tower ℝ ℂ E

@[simp, norm_cast] lemma complex.coe_smul {E : Type*} [add_comm_group E] [module ℂ E]
  (x : ℝ) (y : E) :
  (x : ℂ) • y = x • y :=
rfl

/-- The scalar action of `ℝ` on a `ℂ`-module `E` induced by `module.complex_to_real` commutes with
another scalar action of `M` on `E` whenever the action of `ℂ` commutes with the action of `M`. -/
@[priority 900]
instance smul_comm_class.complex_to_real {M E : Type*}
  [add_comm_group E] [module ℂ E] [has_smul M E] [smul_comm_class ℂ M E] : smul_comm_class ℝ M E :=
{ smul_comm := λ r _ _, (smul_comm (r : ℂ) _ _ : _) }

@[priority 100]
instance finite_dimensional.complex_to_real (E : Type*) [add_comm_group E] [module ℂ E]
  [finite_dimensional ℂ E] : finite_dimensional ℝ E :=
finite_dimensional.trans ℝ ℂ E

lemma dim_real_of_complex (E : Type*) [add_comm_group E] [module ℂ E] :
  module.rank ℝ E = 2 * module.rank ℂ E :=
cardinal.lift_inj.1 $
  by { rw [← dim_mul_dim' ℝ ℂ E, complex.dim_real_complex], simp [bit0] }

lemma finrank_real_of_complex (E : Type*) [add_comm_group E] [module ℂ E] :
  finite_dimensional.finrank ℝ E = 2 * finite_dimensional.finrank ℂ E :=
by rw [← finite_dimensional.finrank_mul_finrank ℝ ℂ E, complex.finrank_real_complex]

@[priority 900]
instance star_module.complex_to_real {E : Type*} [add_comm_group E] [has_star E] [module ℂ E]
  [star_module ℂ E] : star_module ℝ E :=
⟨λ r a, by rw [←smul_one_smul ℂ r a, star_smul, star_smul, star_one, smul_one_smul]⟩

namespace complex

open_locale complex_conjugate

/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def re_lm : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.re,
  map_add' := add_re,
  map_smul' := by simp, }

@[simp] lemma re_lm_coe : ⇑re_lm = re := rfl

/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def im_lm : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.im,
  map_add' := add_im,
  map_smul' := by simp, }

@[simp] lemma im_lm_coe : ⇑im_lm = im := rfl

/-- `ℝ`-algebra morphism version of the canonical embedding of `ℝ` in `ℂ`. -/
def of_real_am : ℝ →ₐ[ℝ] ℂ := algebra.of_id ℝ ℂ

@[simp] lemma of_real_am_coe : ⇑of_real_am = coe := rfl

/-- `ℝ`-algebra isomorphism version of the complex conjugation function from `ℂ` to `ℂ` -/
def conj_ae : ℂ ≃ₐ[ℝ] ℂ :=
{ inv_fun := conj,
  left_inv := star_star,
  right_inv := star_star,
  commutes' := conj_of_real,
  .. conj }

@[simp] lemma conj_ae_coe : ⇑conj_ae = conj := rfl

/-- The matrix representation of `conj_ae`. -/
@[simp] lemma to_matrix_conj_ae :
  linear_map.to_matrix basis_one_I basis_one_I conj_ae.to_linear_map = !![1, 0; 0, -1] :=
begin
  ext i j,
  simp [linear_map.to_matrix_apply],
  fin_cases i; fin_cases j; simp
end

/-- The identity and the complex conjugation are the only two `ℝ`-algebra homomorphisms of `ℂ`. -/
lemma real_alg_hom_eq_id_or_conj (f : ℂ →ₐ[ℝ] ℂ) : f = alg_hom.id ℝ ℂ ∨ f = conj_ae :=
begin
  refine (eq_or_eq_neg_of_sq_eq_sq (f I) I $ by rw [← map_pow, I_sq, map_neg, map_one]).imp _ _;
    refine λ h, alg_hom_ext _,
  exacts [h, conj_I.symm ▸ h],
end

/-- The natural `add_equiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps apply symm_apply_re symm_apply_im { simp_rhs := tt }]
def equiv_real_prod_add_hom : ℂ ≃+ ℝ × ℝ :=
{ map_add' := by simp, .. equiv_real_prod }

/-- The natural `linear_equiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps apply symm_apply_re symm_apply_im { simp_rhs := tt }]
def equiv_real_prod_lm : ℂ ≃ₗ[ℝ] ℝ × ℝ :=
{ map_smul' := by simp [equiv_real_prod_add_hom], .. equiv_real_prod_add_hom }

section lift

variables {A : Type*} [ring A] [algebra ℝ A]

/-- There is an alg_hom from `ℂ` to any `ℝ`-algebra with an element that squares to `-1`.

See `complex.lift` for this as an equiv. -/
def lift_aux (I' : A) (hf : I' * I' = -1) : ℂ →ₐ[ℝ] A :=
alg_hom.of_linear_map
  ((algebra.of_id ℝ A).to_linear_map.comp re_lm + (linear_map.to_span_singleton _ _ I').comp im_lm)
  (show algebra_map ℝ A 1 + (0 : ℝ) • I' = 1,
    by rw [ring_hom.map_one, zero_smul, add_zero])
  (λ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩, show algebra_map ℝ A (x₁ * x₂ - y₁ * y₂) + (x₁ * y₂ + y₁ * x₂) • I'
                          = (algebra_map ℝ A x₁ + y₁ • I') * (algebra_map ℝ A x₂ + y₂ • I'),
    begin
      rw [add_mul, mul_add, mul_add, add_comm _ (y₁ • I' * y₂ • I'), add_add_add_comm],
      congr' 1, -- equate "real" and "imaginary" parts
      { rw [smul_mul_smul, hf, smul_neg, ←algebra.algebra_map_eq_smul_one, ←sub_eq_add_neg,
          ←ring_hom.map_mul, ←ring_hom.map_sub], },
      { rw [algebra.smul_def, algebra.smul_def, algebra.smul_def, ←algebra.right_comm _ x₂,
          ←mul_assoc, ←add_mul, ←ring_hom.map_mul, ←ring_hom.map_mul, ←ring_hom.map_add] }
    end)

@[simp]
lemma lift_aux_apply (I' : A) (hI') (z : ℂ) :
 lift_aux I' hI' z = algebra_map ℝ A z.re + z.im • I' := rfl

lemma lift_aux_apply_I (I' : A) (hI') : lift_aux I' hI' I = I' := by simp

/-- A universal property of the complex numbers, providing a unique `ℂ →ₐ[ℝ] A` for every element
of `A` which squares to `-1`.

This can be used to embed the complex numbers in the `quaternion`s.

This isomorphism is named to match the very similar `zsqrtd.lift`. -/
@[simps {simp_rhs := tt}]
def lift : {I' : A // I' * I' = -1} ≃ (ℂ →ₐ[ℝ] A) :=
{ to_fun := λ I', lift_aux I' I'.prop,
  inv_fun := λ F, ⟨F I, by rw [←F.map_mul, I_mul_I, alg_hom.map_neg, alg_hom.map_one]⟩,
  left_inv := λ I', subtype.ext $ lift_aux_apply_I I' I'.prop,
  right_inv := λ F, alg_hom_ext $ lift_aux_apply_I _ _, }

/- When applied to `complex.I` itself, `lift` is the identity. -/
@[simp]
lemma lift_aux_I : lift_aux I I_mul_I = alg_hom.id ℝ ℂ :=
alg_hom_ext $ lift_aux_apply_I _ _

/- When applied to `-complex.I`, `lift` is conjugation, `conj`. -/
@[simp]
lemma lift_aux_neg_I : lift_aux (-I) ((neg_mul_neg _ _).trans I_mul_I) = conj_ae :=
alg_hom_ext $ (lift_aux_apply_I _ _).trans conj_I.symm

end lift

end complex

section real_imaginary_part

open complex

variables {A : Type*} [add_comm_group A] [module ℂ A] [star_add_monoid A] [star_module ℂ A]

/-- Create a `self_adjoint` element from a `skew_adjoint` element by multiplying by the scalar
`-complex.I`. -/
@[simps] def skew_adjoint.neg_I_smul : skew_adjoint A →ₗ[ℝ] self_adjoint A :=
{ to_fun := λ a, ⟨-I • a, by simp only [self_adjoint.mem_iff, neg_smul, star_neg, star_smul,
    star_def, conj_I, skew_adjoint.star_coe_eq, neg_smul_neg]⟩,
  map_add' := λ a b, by { ext, simp only [add_subgroup.coe_add, smul_add, add_mem_class.mk_add_mk]},
  map_smul' := λ a b, by { ext, simp only [neg_smul, skew_adjoint.coe_smul, add_subgroup.coe_mk,
    ring_hom.id_apply, self_adjoint.coe_smul, smul_neg, neg_inj], rw smul_comm, } }

lemma skew_adjoint.I_smul_neg_I (a : skew_adjoint A) :
  I • (skew_adjoint.neg_I_smul a : A) = a :=
by simp only [smul_smul, skew_adjoint.neg_I_smul_apply_coe, neg_smul, smul_neg, I_mul_I, one_smul,
  neg_neg]

/-- The real part `ℜ a` of an element `a` of a star module over `ℂ`, as a linear map. This is just
`self_adjoint_part ℝ`, but we provide it as a separate definition in order to link it with lemmas
concerning the `imaginary_part`, which doesn't exist in star modules over other rings. -/
noncomputable def real_part : A →ₗ[ℝ] self_adjoint A := self_adjoint_part ℝ

/-- The imaginary part `ℑ a` of an element `a` of a star module over `ℂ`, as a linear map into the
self adjoint elements. In a general star module, we have a decomposition into the `self_adjoint`
and `skew_adjoint` parts, but in a star module over `ℂ` we have
`real_part_add_I_smul_imaginary_part`, which allows us to decompose into a linear combination of
`self_adjoint`s. -/
noncomputable
def imaginary_part : A →ₗ[ℝ] self_adjoint A := skew_adjoint.neg_I_smul.comp (skew_adjoint_part ℝ)

localized "notation `ℜ` := real_part" in complex_star_module
localized "notation `ℑ` := imaginary_part" in complex_star_module

@[simp] lemma real_part_apply_coe (a : A) :
  (ℜ a : A) = (2 : ℝ)⁻¹ • (a + star a) :=
by { unfold real_part, simp only [self_adjoint_part_apply_coe, inv_of_eq_inv]}

@[simp] lemma imaginary_part_apply_coe (a : A) :
  (ℑ a : A) = -I • (2 : ℝ)⁻¹ • (a - star a) :=
begin
  unfold imaginary_part,
  simp only [linear_map.coe_comp, skew_adjoint.neg_I_smul_apply_coe, skew_adjoint_part_apply_coe,
    inv_of_eq_inv],
end

/-- The standard decomposition of `ℜ a + complex.I • ℑ a = a` of an element of a star module over
`ℂ` into a linear combination of self adjoint elements. -/
lemma real_part_add_I_smul_imaginary_part (a : A) : (ℜ a + I • ℑ a : A) = a :=
by simpa only [smul_smul, real_part_apply_coe, imaginary_part_apply_coe, neg_smul, I_mul_I,
  one_smul, neg_sub, add_add_sub_cancel, smul_sub, smul_add, neg_sub_neg, inv_of_eq_inv]
  using inv_of_two_smul_add_inv_of_two_smul ℝ a

@[simp] lemma real_part_I_smul (a : A) : ℜ (I • a) = - ℑ a :=
by { ext, simp [smul_comm I, smul_sub, sub_eq_add_neg, add_comm] }

@[simp] lemma imaginary_part_I_smul (a : A) : ℑ (I • a) = ℜ a :=
by { ext, simp [smul_comm I, smul_smul I] }

lemma real_part_smul (z : ℂ) (a : A) : ℜ (z • a) = z.re • ℜ a - z.im • ℑ a :=
by { nth_rewrite 0 ←re_add_im z, simp [-re_add_im, add_smul, ←smul_smul, sub_eq_add_neg] }

lemma imaginary_part_smul (z : ℂ) (a : A) : ℑ (z • a) = z.re • ℑ a + z.im • ℜ a :=
by { nth_rewrite 0 ←re_add_im z, simp [-re_add_im, add_smul, ←smul_smul] }

end real_imaginary_part
