/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.quadratic_form.isometry
import linear_algebra.tensor_product

/-! # Quadratic form on tensor product

## Main definitions

* `quadratic_form.tmul Q₁ Q₂`: the quadratic form constructed elementwise on a tensor product

## Main results

* `quadratic_form.equivalent.prod`, `quadratic_form.equivalent.pi`: quadratic forms are equivalent
  if their components are equivalent
-- * `quadratic_form.nonneg_prod_iff`, `quadratic_form.nonneg_pi_iff`: quadratic forms are positive-
--   semidefinite if and only if their components are positive-semidefinite.
-- * `quadratic_form.pos_def_prod_iff`, `quadratic_form.pos_def_pi_iff`: quadratic forms are positive-
--   definite if and only if their components are positive-definite.
-/

universes u v w
variables {ι : Type*} {R : Type*} {M₁ M₂ N₁ N₂ : Type*} {Mᵢ Nᵢ : ι → Type*}
variables [comm_semiring R]
variables [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid N₁] [add_comm_monoid N₂]
variables [module R M₁] [module R M₂] [module R N₁] [module R N₂]
variables [Π i, add_comm_monoid (Mᵢ i)] [Π i, add_comm_monoid (Nᵢ i)]
variables [Π i, module R (Mᵢ i)] [Π i, module R (Nᵢ i)]

open_locale tensor_product

def bilin_form.tmul (B₁ : bilin_form R M₁) (B₂ : bilin_form R M₂) : bilin_form R (M₁ ⊗[R] M₂) :=
linear_map.to_bilin $ begin
  refine (tensor_product.lift.equiv R (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₂) R).symm _,
  refine _ ∘ₗ (tensor_product.tensor_tensor_tensor_comm R _ _ _ _).to_linear_map,
  refine (tensor_product.lid R R).to_linear_map ∘ₗ _,
  exact tensor_product.map (tensor_product.lift B₁.to_lin) (tensor_product.lift B₂.to_lin),
end

lemma bilin_form.tmul_tmul (B₁ : bilin_form R M₁) (B₂ : bilin_form R M₂)
  (m₁ m₁' : M₁) (m₂ m₂' : M₂) :
  B₁.tmul B₂ (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂') = B₁ m₁ m₁' * B₂ m₂ m₂' :=
(tensor_product.lift.tmul _ _).trans $
  congr_arg2 (*) (tensor_product.lift.tmul _ _) (tensor_product.lift.tmul _ _)

namespace quadratic_form

#check tensor_product.map_bilinear

def to_linear_tensor_product (Q : quadratic_form R M₁) : M₁ →ₗ[R] (R ⊗[R] R) :=
{ to_fun := λ x, Q x ⊗ₜ 1,
  map_add' := λ x y, begin
    obtain ⟨c, hc⟩ := Q.exists_companion,
    simp_rw [hc, tensor_product.add_tmul],
  end,
  map_smul' := _ }

#check free_add_monoid.map

/-- Construct a quadratic form on a tensor product of two modules from the quadratic form on each module.
-/
def tmul (Q₁ : quadratic_form R M₁) (Q₂ : quadratic_form R M₂) : quadratic_form R (M₁ ⊗[R] M₂) :=
{ to_fun := λ x, begin
    refine add_con.lift_on x _ _,
    exact free_add_monoid.lift (λ m : _ × _, Q₁ m.1 * Q₂ m.2),
    intros a b h,
    induction h,
    case of : a' b' hab' {
      induction hab',
      { simp_rw [free_add_monoid.lift_eval_of, map_zero, zero_mul, _root_.map_zero], },
      { simp_rw [free_add_monoid.lift_eval_of, map_zero, mul_zero, _root_.map_zero], },
      { simp_rw [map_add, free_add_monoid.lift_eval_of, free_add_monoid.lift_eval_of],
        rw[map_zero, mul_zero, _root_.map_zero], },
    },
    case refl { refl },
    case symm : a' b' h' ih { exact ih.symm },
    case trans : a' b' c' hab' hbc' ihab ihbc { exact ihab.trans ihbc },
    case add : a' b' c' d' hab' hcd' ihab ihcd { rw [map_add, map_add, ihab, ihcd] },
  end,
  to_fun_smul := sorry,
  exists_companion' := sorry }

#check quadratic_form.add

end quadratic_form
