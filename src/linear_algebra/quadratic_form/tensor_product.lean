/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.bilinear_form.tensor_product
import linear_algebra.quadratic_form.isometry

/-! # Quadratic form on tensor product

## Main definitions

* `quadratic_form.tmul Q₁ Q₂`: the quadratic form constructed elementwise on a tensor product

-/

universes u v w
variables {R : Type*} {M₁ M₂ : Type*}
variables [comm_semiring R]
variables [add_comm_monoid M₁] [add_comm_monoid M₂]
variables [module R M₁] [module R M₂]

open_locale tensor_product

variables (R M₁)

def quadratic_form.equiv_subtype :
  quadratic_form R M₁ ≃ subtype { f : M₁ → R |
    (∀ (a : R) (x : M₁), f (a • x) = a * a * f x) ∧
    (∃ B : bilin_form R M₁, ∀ x y, f (x + y) = f x + f y + B x y) } :=
{ to_fun := λ Q, ⟨Q, Q.to_fun_smul, Q.exists_companion⟩,
  inv_fun := λ s, ⟨s, s.prop.1, s.prop.2⟩,
  left_inv := λ Q, by cases Q; refl,
  right_inv := λ S, by cases S; refl, }

def bilin_form.equiv_subtype :
  bilin_form R M₁ ≃ subtype { f : M₁ → M₁ → R |
    (∀ (x y z : M₁), f (x + y) z = f x z + f y z) ∧
    (∀ (a : R) (x y : M₁), f (a • x) y = a * (f x y)) ∧
    (∀ (x y z : M₁), f x (y + z) = f x y + f x z) ∧
    (∀ (a : R) (x y : M₁), f x (a • y) = a * (f x y)) } :=
{ to_fun := λ Q, ⟨Q.1, Q.2, Q.3, Q.4, Q.5⟩,
  inv_fun := λ s, ⟨s, s.prop.1, s.prop.2.1, s.prop.2.2.1, s.prop.2.2.2⟩,
  left_inv := λ Q, by cases Q; refl,
  right_inv := λ S, by cases S; refl, }

instance [fintype R] [fintype M₁] [decidable_eq R] [decidable_eq M₁] :
  fintype (bilin_form R M₁) :=
@fintype.of_equiv _ _ (subtype.fintype _) (bilin_form.equiv_subtype R M₁).symm

instance [fintype R] [fintype M₁] [decidable_eq R] [decidable_eq M₁] :
  fintype (quadratic_form R M₁) :=
@fintype.of_equiv _ _ (subtype.fintype _) (quadratic_form.equiv_subtype R M₁).symm

#eval (@finset.univ (fin 3 → fin 3)).val

namespace quadratic_form

#check tensor_product.map_bilinear

variables (R M₁)



-- def to_linear_tensor_product (Q : quadratic_form R M₁) : M₁ →ₗ[R] (R ⊗[R] R) :=
-- { to_fun := λ x, Q x ⊗ₜ 1,
--   map_add' := λ x y, begin
--     obtain ⟨c, hc⟩ := Q.exists_companion,
--     simp_rw [hc, tensor_product.add_tmul],
--   end,
--   map_smul' := _ }

-- #check free_add_monoid.map

-- /-- Construct a quadratic form on a tensor product of two modules from the quadratic form on each module.
-- -/
-- def tmul (Q₁ : quadratic_form R M₁) (Q₂ : quadratic_form R M₂) : quadratic_form R (M₁ ⊗[R] M₂) :=
-- { to_fun := λ x, begin
--     sorry
--     -- refine add_con.lift_on x _ _,
--     -- exact free_add_monoid.lift (λ m : _ × _, Q₁ m.1 * Q₂ m.2),
--     -- intros a b h,
--     -- induction h,
--     -- case of : a' b' hab' {
--     --   induction hab',
--     --   { simp_rw [free_add_monoid.lift_eval_of, map_zero, zero_mul, _root_.map_zero], },
--     --   { simp_rw [free_add_monoid.lift_eval_of, map_zero, mul_zero, _root_.map_zero], },
--     --   { simp_rw [map_add, free_add_monoid.lift_eval_of, free_add_monoid.lift_eval_of],
--     --     rw[map_zero, mul_zero, _root_.map_zero], },
--     -- },
--     -- case refl { refl },
--     -- case symm : a' b' h' ih { exact ih.symm },
--     -- case trans : a' b' c' hab' hbc' ihab ihbc { exact ihab.trans ihbc },
--     -- case add : a' b' c' d' hab' hcd' ihab ihcd { rw [map_add, map_add, ihab, ihcd] },
--   end,
--   to_fun_smul := sorry,
--   exists_companion' := begin
--     obtain ⟨B₁, hB₁⟩ := Q₁.exists_companion,
--     obtain ⟨B₂, hB₂⟩ := Q₂.exists_companion,
--     refine ⟨B₁.tmul B₂, λ x y, _⟩,
--     induction x using tensor_product.induction_on,
--     sorry
--   end }

-- @[simp] lemma tmul_tmul (Q₁ : quadratic_form R M₁) (Q₂ : quadratic_form R M₂)
--   (m₁ m₁' : M₁) (m₂ m₂' : M₂) :
--   Q₁.tmul Q₂ (m₁ ⊗ₜ m₂) = Q₁ m₁ * Q₂ m₂ :=
-- #check quadratic_form.add

end quadratic_form
