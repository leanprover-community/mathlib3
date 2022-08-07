/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import ring_theory.tensor_product

/-!
# The characteristice predicate of tensor product

## Main definitions

- `is_tensor_product`: A predicate on `f : M₁ →ₗ[R] M₂ →ₗ[R] M` expressing that `f` realizes `M` as
  the tensor product of `M₁ ⊗[R] M₂`. This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be
  bijective.
- `is_base_change`: A predicate on an `R`-algebra `S` and a map `f : M →ₗ[R] N` with `N` being a
  `S`-module, expressing that `f` realizes `N` as the base change of `M` along `R → S`.

## Main results
- `tensor_product.is_base_change`: `S ⊗[R] M` is the base change of `M` along `R → S`.

-/

universes u v₁ v₂ v₃ v₄

open_locale tensor_product

open tensor_product

section is_tensor_product

variables {R : Type*} [comm_ring R]
variables {M₁ M₂ M M' : Type*}
variables [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M] [add_comm_monoid M']
variables [module R M₁] [module R M₂] [module R M] [module R M']
variable (f : M₁ →ₗ[R] M₂ →ₗ[R] M)
variables {N₁ N₂ N : Type*} [add_comm_monoid N₁] [add_comm_monoid N₂] [add_comm_monoid N]
variables [module R N₁] [module R N₂] [module R N]
variable {g : N₁ →ₗ[R] N₂ →ₗ[R] N}

/--
Given a bilinear map `f : M₁ →ₗ[R] M₂ →ₗ[R] M`, `is_tensor_product f` means that
`M` is the tensor product of `M₁` and `M₂` via `f`.
This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be bijective.
-/
def is_tensor_product : Prop := function.bijective (tensor_product.lift f)

variables (R M N) {f}

lemma tensor_product.is_tensor_product : is_tensor_product (tensor_product.mk R M N) :=
begin
  delta is_tensor_product,
  convert_to function.bijective linear_map.id using 2,
  { apply tensor_product.ext', simp },
  { exact function.bijective_id }
end

variables {R M N}

/-- If `M` is the tensor product of `M₁` and `M₂`, it is linearly equivalent to `M₁ ⊗[R] M₂`. -/
@[simps apply] noncomputable
def is_tensor_product.equiv (h : is_tensor_product f) : M₁ ⊗[R] M₂ ≃ₗ[R] M :=
linear_equiv.of_bijective _ h.1 h.2

@[simp] lemma is_tensor_product.equiv_to_linear_map (h : is_tensor_product f) :
  h.equiv.to_linear_map = tensor_product.lift f := rfl

@[simp] lemma is_tensor_product.equiv_symm_apply (h : is_tensor_product f) (x₁ : M₁) (x₂ : M₂) :
  h.equiv.symm (f x₁ x₂) = x₁ ⊗ₜ x₂ :=
begin
  apply h.equiv.injective,
  refine (h.equiv.apply_symm_apply _).trans _,
  simp
end

/-- If `M` is the tensor product of `M₁` and `M₂`, we may lift a bilinear map `M₁ →ₗ[R] M₂ →ₗ[R] M'`
to a `M →ₗ[R] M'`. -/
noncomputable
def is_tensor_product.lift (h : is_tensor_product f) (f' : M₁ →ₗ[R] M₂ →ₗ[R] M') : M →ₗ[R] M' :=
(tensor_product.lift f').comp h.equiv.symm.to_linear_map

lemma is_tensor_product.lift_eq (h : is_tensor_product f) (f' : M₁ →ₗ[R] M₂ →ₗ[R] M')
  (x₁ : M₁) (x₂ : M₂) : h.lift f' (f x₁ x₂) = f' x₁ x₂ :=
begin
  delta is_tensor_product.lift,
  simp,
end

/-- The tensor product of a pair of linear maps between modules. -/
noncomputable
def is_tensor_product.map (hf : is_tensor_product f) (hg : is_tensor_product g)
  (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) : M →ₗ[R] N :=
hg.equiv.to_linear_map.comp ((tensor_product.map i₁ i₂).comp hf.equiv.symm.to_linear_map)

lemma is_tensor_product.map_eq (hf : is_tensor_product f) (hg : is_tensor_product g)
  (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) (x₁ : M₁) (x₂ : M₂) :
    hf.map hg i₁ i₂ (f x₁ x₂) = g (i₁ x₁) (i₂ x₂) :=
begin
  delta is_tensor_product.map,
  simp
end

lemma is_tensor_product.induction_on (h : is_tensor_product f) {C : M → Prop}
  (m : M) (h0 : C 0) (htmul : ∀ x y, C (f x y)) (hadd : ∀ x y, C x → C y → C (x + y)) : C m :=
begin
  rw ← h.equiv.right_inv m,
  generalize : h.equiv.inv_fun m = y,
  change C (tensor_product.lift f y),
  induction y using tensor_product.induction_on,
  { rwa map_zero },
  { rw tensor_product.lift.tmul, apply htmul },
  { rw map_add, apply hadd; assumption }
end

end is_tensor_product

section is_base_change

variables {R M N : Type*} (S : Type*) [add_comm_monoid M] [add_comm_monoid N] [comm_ring R]
variables [comm_ring S] [algebra R S] [module R M] [module R N] [module S N] [is_scalar_tower R S N]
variables (f : M →ₗ[R] N)

include f

/-- Given an `R`-algebra `S` and an `R`-module `M`, an `S`-module `N` together with a map
`f : M →ₗ[R] N` is the base change of `M` to `S` if the map `S × M → N, (s, m) ↦ s • f m` is the
tensor product. -/
def is_base_change : Prop := is_tensor_product
(((algebra.of_id S $ module.End S (M →ₗ[R] N)).to_linear_map.flip f).restrict_scalars R)

variables {S f} (h : is_base_change S f)
variables {P Q : Type*} [add_comm_monoid P] [module R P]
variables[add_comm_monoid Q] [module R Q] [module S Q] [is_scalar_tower R S Q]

/-- Suppose `f : M →ₗ[R] N` is the base change of `M` along `R → S`. Then any `R`-linear map from
`M` to an `S`-module factors thorugh `f`. -/
noncomputable
def is_base_change.lift (g : M →ₗ[R] Q) : N →ₗ[S] Q :=
{ map_smul' := λ r x, begin
    let F := ((algebra.of_id S $ module.End S (M →ₗ[R] Q))
      .to_linear_map.flip g).restrict_scalars R,
    have hF : ∀ (s : S) (m : M), h.lift F (s • f m) = s • g m := h.lift_eq F,
    change h.lift F (r • x) = r • h.lift F x,
    apply h.induction_on x,
    { rw [smul_zero, map_zero, smul_zero] },
    { intros s m,
      change h.lift F (r • s • f m) = r • h.lift F (s • f m),
      rw [← mul_smul, hF, hF, mul_smul] },
    { intros x₁ x₂ e₁ e₂, rw [map_add, smul_add, map_add, smul_add, e₁, e₂] }
  end,
  ..(h.lift (((algebra.of_id S $ module.End S (M →ₗ[R] Q))
    .to_linear_map.flip g).restrict_scalars R)) }

lemma is_base_change.lift_eq (g : M →ₗ[R] Q) (x : M) : h.lift g (f x) = g x :=
begin
  have hF : ∀ (s : S) (m : M), h.lift g (s • f m) = s • g m := h.lift_eq _,
  convert hF 1 x; rw one_smul,
end

lemma is_base_change.lift_comp (g : M →ₗ[R] Q) : ((h.lift g).restrict_scalars R).comp f = g :=
linear_map.ext (h.lift_eq g)

variables (R M N S)

omit f

lemma tensor_product.is_base_change : is_base_change S (tensor_product.mk R S M 1) :=
begin
  delta is_base_change,
  convert tensor_product.is_tensor_product R S M using 1,
  ext s x,
  change s • 1 ⊗ₜ x = s ⊗ₜ x,
  rw tensor_product.smul_tmul',
  congr' 1,
  exact mul_one _,
end

variables {R M N S}

/-- The base change of `M` along `R → S` is linearly equivalent to `S ⊗[R] M`. -/
noncomputable
def is_base_change.equiv : S ⊗[R] M ≃ₗ[R] N := h.equiv

lemma is_base_change.equiv_tmul (s : S) (m : M) : h.equiv (s ⊗ₜ m) = s • (f m) :=
tensor_product.lift.tmul s m

lemma is_base_change.equiv_symm_apply (m : M) : h.equiv.symm (f m) = 1 ⊗ₜ m :=
by rw [h.equiv.symm_apply_eq, h.equiv_tmul, one_smul]

end is_base_change
