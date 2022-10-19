/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import ring_theory.tensor_product
import algebra.module.ulift
import logic.equiv.transfer_instance

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

variables {R : Type*} {M : Type v₁} {N : Type v₂} (S : Type v₃)
variables [add_comm_monoid M] [add_comm_monoid N] [comm_ring R]
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
variables [add_comm_monoid Q] [module S Q]

section

variables [module R Q] [is_scalar_tower R S Q]

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

end
include h

@[elab_as_eliminator]
lemma is_base_change.induction_on (x : N) (P : N → Prop)
  (h₁ : P 0)
  (h₂ : ∀ m : M, P (f m))
  (h₃ : ∀ (s : S) n, P n → P (s • n))
  (h₄ : ∀ n₁ n₂, P n₁ → P n₂ → P (n₁ + n₂)) : P x :=
h.induction_on x h₁ (λ s y, h₃ _ _ (h₂ _)) h₄

lemma is_base_change.alg_hom_ext (g₁ g₂ : N →ₗ[S] Q) (e : ∀ x, g₁ (f x) = g₂ (f x)) :
  g₁ = g₂ :=
begin
  ext x,
  apply h.induction_on x,
  { rw [map_zero, map_zero] },
  { assumption },
  { intros s n e', rw [g₁.map_smul, g₂.map_smul, e'] },
  { intros x y e₁ e₂, rw [map_add, map_add, e₁, e₂] }
end

lemma is_base_change.alg_hom_ext' [module R Q] [is_scalar_tower R S Q] (g₁ g₂ : N →ₗ[S] Q)
  (e : (g₁.restrict_scalars R).comp f = (g₂.restrict_scalars R).comp f) :
  g₁ = g₂ :=
h.alg_hom_ext g₁ g₂ (linear_map.congr_fun e)

variables (R M N S)

omit h f

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


variable (f)

lemma is_base_change.of_lift_unique
  (h : ∀ (Q : Type (max v₁ v₂ v₃)) [add_comm_monoid Q], by exactI ∀ [module R Q] [module S Q],
    by exactI ∀ [is_scalar_tower R S Q], by exactI ∀ (g : M →ₗ[R] Q),
      ∃! (g' : N →ₗ[S] Q), (g'.restrict_scalars R).comp f = g) : is_base_change S f :=
begin
  delta is_base_change is_tensor_product,
  obtain ⟨g, hg, hg'⟩  := h (ulift.{v₂} $ S ⊗[R] M)
    (ulift.module_equiv.symm.to_linear_map.comp $ tensor_product.mk R S M 1),
  let f' : S ⊗[R] M →ₗ[R] N := _, change function.bijective f',
  let f'' : S ⊗[R] M →ₗ[S] N,
  { refine { map_smul' := λ r x, _, ..f' },
    apply tensor_product.induction_on x,
    { simp only [map_zero, smul_zero, linear_map.to_fun_eq_coe] },
    { intros x y,
      simp only [algebra.of_id_apply, algebra.id.smul_eq_mul,
        alg_hom.to_linear_map_apply, linear_map.mul_apply, tensor_product.lift.tmul',
        linear_map.smul_apply, ring_hom.id_apply, module.algebra_map_End_apply, f',
        _root_.map_mul, tensor_product.smul_tmul', linear_map.coe_restrict_scalars_eq_coe,
        linear_map.flip_apply] },
    { intros x y hx hy, dsimp at hx hy ⊢, simp only [hx, hy, smul_add, map_add] } },
  change function.bijective f'',
  split,
  { apply function.has_left_inverse.injective,
    refine ⟨ulift.module_equiv.to_linear_map.comp g, λ x, _⟩,
    apply tensor_product.induction_on x,
    { simp only [map_zero] },
    { intros x y,
      have := (congr_arg (λ a, x • a) (linear_map.congr_fun hg y)).trans
        (ulift.module_equiv.symm.map_smul x _).symm,
      apply (ulift.module_equiv : ulift.{v₂} (S ⊗ M) ≃ₗ[S] S ⊗ M)
        .to_equiv.apply_eq_iff_eq_symm_apply.mpr,
      any_goals { apply_instance },
      simpa only [algebra.of_id_apply, smul_tmul', algebra.id.smul_eq_mul, lift.tmul',
        linear_map.coe_restrict_scalars_eq_coe, linear_map.flip_apply, alg_hom.to_linear_map_apply,
        module.algebra_map_End_apply, linear_map.smul_apply, linear_map.coe_mk,
        linear_map.map_smulₛₗ, mk_apply, mul_one] using this },
    { intros x y hx hy, simp only [map_add, hx, hy] } },
  { apply function.has_right_inverse.surjective,
    refine ⟨ulift.module_equiv.to_linear_map.comp g, λ x, _⟩,
    obtain ⟨g', hg₁, hg₂⟩ := h (ulift.{max v₁ v₃} N) (ulift.module_equiv.symm.to_linear_map.comp f),
    have : g' = ulift.module_equiv.symm.to_linear_map := by { refine (hg₂ _ _).symm, refl },
    subst this,
    apply (ulift.module_equiv : ulift.{max v₁ v₃} N ≃ₗ[S] N).symm.injective,
    simp_rw [← linear_equiv.coe_to_linear_map, ← linear_map.comp_apply],
    congr' 1,
    apply hg₂,
    ext y,
    have := linear_map.congr_fun hg y,
    dsimp [ulift.module_equiv] at this ⊢,
    rw this,
    simp only [lift.tmul, linear_map.coe_restrict_scalars_eq_coe, linear_map.flip_apply,
      alg_hom.to_linear_map_apply, _root_.map_one, linear_map.one_apply] }
end

variable {f}

lemma is_base_change.iff_lift_unique :
  is_base_change S f ↔
    ∀ (Q : Type (max v₁ v₂ v₃)) [add_comm_monoid Q], by exactI ∀ [module R Q] [module S Q],
    by exactI ∀ [is_scalar_tower R S Q], by exactI ∀ (g : M →ₗ[R] Q),
      ∃! (g' : N →ₗ[S] Q), (g'.restrict_scalars R).comp f = g :=
⟨λ h, by { introsI,
  exact ⟨h.lift g, h.lift_comp g, λ g' e, h.alg_hom_ext' _ _ (e.trans (h.lift_comp g).symm)⟩ },
  is_base_change.of_lift_unique f⟩

lemma is_base_change.of_equiv (e : M ≃ₗ[R] N) : is_base_change R e.to_linear_map :=
begin
  apply is_base_change.of_lift_unique,
  introsI Q I₁ I₂ I₃ I₄ g,
  have : I₂ = I₃,
  { ext r q,
    rw [← one_smul R q, smul_smul, ← smul_assoc, smul_eq_mul, mul_one] },
  unfreezingI { cases this },
  refine ⟨g.comp e.symm.to_linear_map, by { ext, simp }, _⟩,
  rintros y (rfl : _ = _),
  ext,
  simp,
end

variables {T O : Type*} [comm_ring T] [algebra R T] [algebra S T] [is_scalar_tower R S T]
variables [add_comm_monoid O] [module R O] [module S O] [module T O] [is_scalar_tower S T O]
variables [is_scalar_tower R S O] [is_scalar_tower R T O]

lemma is_base_change.comp {f : M →ₗ[R] N} (hf : is_base_change S f) {g : N →ₗ[S] O}
  (hg : is_base_change T g) : is_base_change T ((g.restrict_scalars R).comp f) :=
begin
  apply is_base_change.of_lift_unique,
  introsI Q _ _ _ _ i,
  letI := module.comp_hom Q (algebra_map S T),
  haveI : is_scalar_tower S T Q := ⟨λ x y z, by { rw [algebra.smul_def, mul_smul], refl }⟩,
  haveI : is_scalar_tower R S Q,
  { refine ⟨λ x y z, _⟩,
    change (is_scalar_tower.to_alg_hom R S T) (x • y) • z = x • (algebra_map S T y • z),
    rw [alg_hom.map_smul, smul_assoc],
    refl },
  refine ⟨hg.lift (hf.lift i), by { ext, simp [is_base_change.lift_eq] }, _⟩,
  rintros g' (e : _ = _),
  refine hg.alg_hom_ext' _ _ (hf.alg_hom_ext' _ _ _),
  rw [is_base_change.lift_comp, is_base_change.lift_comp, ← e],
  ext,
  refl
end

variables {R' S' : Type*} [comm_ring R'] [comm_ring S']
variables [algebra R R'] [algebra S S'] [algebra R' S'] [algebra R S']
variables [is_scalar_tower R R' S'] [is_scalar_tower R S S']

lemma is_base_change.symm
  (h : is_base_change S (is_scalar_tower.to_alg_hom R R' S').to_linear_map) :
  is_base_change R' (is_scalar_tower.to_alg_hom R S S').to_linear_map :=
begin
  letI := (algebra.tensor_product.include_right : R' →ₐ[R] S ⊗ R').to_ring_hom.to_algebra,
  let e : R' ⊗[R] S ≃ₗ[R'] S',
  { refine { map_smul' := _, ..((tensor_product.comm R R' S).trans $ h.equiv.restrict_scalars R) },
    intros r x,
    change
      h.equiv (tensor_product.comm R R' S (r • x)) = r • h.equiv (tensor_product.comm R R' S x),
    apply tensor_product.induction_on x,
    { simp only [smul_zero, map_zero] },
    { intros x y,
      simp [smul_tmul', algebra.smul_def, ring_hom.algebra_map_to_algebra, h.equiv_tmul],
      ring },
    { intros x y hx hy, simp only [map_add, smul_add, hx, hy] } },
  have : (is_scalar_tower.to_alg_hom R S S').to_linear_map
    = (e.to_linear_map.restrict_scalars R).comp (tensor_product.mk R R' S 1),
  { ext, simp [e, h.equiv_tmul, algebra.smul_def] },
  rw this,
  exact (tensor_product.is_base_change R S R').comp (is_base_change.of_equiv e),
end

variables (R S R' S')

lemma is_base_change.comm :
  is_base_change S (is_scalar_tower.to_alg_hom R R' S').to_linear_map ↔
    is_base_change R' (is_scalar_tower.to_alg_hom R S S').to_linear_map :=
⟨is_base_change.symm, is_base_change.symm⟩

end is_base_change
