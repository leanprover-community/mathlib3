/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import ring_theory.tensor_product
import algebra.module.ulift

/-!
# The characteristice predicate of tensor product

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

- `is_tensor_product`: A predicate on `f : M₁ →ₗ[R] M₂ →ₗ[R] M` expressing that `f` realizes `M` as
  the tensor product of `M₁ ⊗[R] M₂`. This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be
  bijective.
- `is_base_change`: A predicate on an `R`-algebra `S` and a map `f : M →ₗ[R] N` with `N` being a
  `S`-module, expressing that `f` realizes `N` as the base change of `M` along `R → S`.
- `algebra.is_pushout`: A predicate on the following diagram of scalar towers
  ```
    R  →  S
    ↓     ↓
    R' →  S'
  ```
    asserting that is a pushout diagram (i.e. `S' = S ⊗[R] R'`)

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
linear_equiv.of_bijective _ h

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
def is_base_change.equiv : S ⊗[R] M ≃ₗ[S] N :=
{ map_smul' := λ r x, begin
    change h.equiv (r • x) = r • h.equiv x,
    apply tensor_product.induction_on x,
    { rw [smul_zero, map_zero, smul_zero] },
    { intros x y, simp [smul_tmul', algebra.of_id_apply] },
    { intros x y hx hy, rw [map_add, smul_add, map_add, smul_add, hx, hy] },
  end,
  ..h.equiv }

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
  obtain ⟨g, hg, -⟩ := h (ulift.{v₂} $ S ⊗[R] M)
    (ulift.module_equiv.symm.to_linear_map.comp $ tensor_product.mk R S M 1),
  let f' : S ⊗[R] M →ₗ[R] N := _, change function.bijective f',
  let f'' : S ⊗[R] M →ₗ[S] N,
  { refine { to_fun := f', map_smul' := λ s x, 
      tensor_product.induction_on x _ (λ s' y, smul_assoc s s' _) (λ x y hx hy, _), .. f' },
    { rw [map_zero, smul_zero, map_zero, smul_zero] },
    { rw [smul_add, map_add, map_add, smul_add, hx, hy] } },
  simp_rw [fun_like.ext_iff, linear_map.comp_apply, linear_map.restrict_scalars_apply] at hg,
  let fe : S ⊗[R] M ≃ₗ[S] N :=
    linear_equiv.of_linear f'' (ulift.module_equiv.to_linear_map.comp g) _ _,
  { exact fe.bijective },
  { rw ← (linear_map.cancel_left (ulift.module_equiv : ulift.{max v₁ v₃} N ≃ₗ[S] N).symm.injective),
    refine (h (ulift.{max v₁ v₃} N) $ ulift.module_equiv.symm.to_linear_map.comp f).unique _ rfl,
    { apply_instance },
    ext x,
    simp only [linear_map.comp_apply, linear_map.restrict_scalars_apply, hg],
    apply one_smul },
  { ext x, change (g $ (1 : S) • f x).down = _, rw [one_smul, hg], refl },
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

open is_scalar_tower (to_alg_hom)

variables (R S R' S')

/--
A type-class stating that the following diagram of scalar towers
R  →  S
↓     ↓
R' →  S'
is a pushout diagram (i.e. `S' = S ⊗[R] R'`)
-/
@[mk_iff]
class algebra.is_pushout : Prop :=
(out : is_base_change S (to_alg_hom R R' S').to_linear_map)

variables {R S R' S'}

lemma algebra.is_pushout.symm
  (h : algebra.is_pushout R S R' S') :
  algebra.is_pushout R R' S S' :=
begin
  letI := (algebra.tensor_product.include_right : R' →ₐ[R] S ⊗ R').to_ring_hom.to_algebra,
  let e : R' ⊗[R] S ≃ₗ[R'] S',
  { refine { map_smul' := _, ..(tensor_product.comm R R' S).trans $ h.1.equiv.restrict_scalars R },
    intros r x,
    change
      h.1.equiv (tensor_product.comm R R' S (r • x)) = r • h.1.equiv (tensor_product.comm R R' S x),
    apply tensor_product.induction_on x,
    { simp only [smul_zero, map_zero] },
    { intros x y,
      simp [smul_tmul', algebra.smul_def, ring_hom.algebra_map_to_algebra, h.1.equiv_tmul],
      ring },
    { intros x y hx hy, simp only [map_add, smul_add, hx, hy] } },
  have : (to_alg_hom R S S').to_linear_map
    = (e.to_linear_map.restrict_scalars R).comp (tensor_product.mk R R' S 1),
  { ext, simp [e, h.1.equiv_tmul, algebra.smul_def] },
  constructor,
  rw this,
  exact (tensor_product.is_base_change R S R').comp (is_base_change.of_equiv e),
end

variables (R S R' S')

lemma algebra.is_pushout.comm :
  algebra.is_pushout R S R' S' ↔ algebra.is_pushout R R' S S' :=
⟨algebra.is_pushout.symm, algebra.is_pushout.symm⟩

variables {R S R'}

local attribute [instance] algebra.tensor_product.right_algebra

instance tensor_product.is_pushout {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
  [algebra R S] [algebra R T] :
  algebra.is_pushout R S T (tensor_product R S T) :=
⟨tensor_product.is_base_change R T S⟩

instance tensor_product.is_pushout' {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
  [algebra R S] [algebra R T] :
  algebra.is_pushout R T S (tensor_product R S T) :=
algebra.is_pushout.symm infer_instance

/--
If `S' = S ⊗[R] R'`, then any pair of `R`-algebra homomorphisms `f : S → A` and `g : R' → A`
such that `f x` and `g y` commutes for all `x, y` descends to a (unique) homomoprhism `S' → A`.
-/
@[simps apply (lemmas_only)] noncomputable
def algebra.pushout_desc [H : algebra.is_pushout R S R' S']
  {A : Type*} [semiring A] [algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A)
    (hf : ∀ x y, f x * g y = g y * f x) : S' →ₐ[R] A :=
begin
  letI := module.comp_hom A f.to_ring_hom,
  haveI : is_scalar_tower R S A :=
  { smul_assoc := λ r s a, show f (r • s) * a = r • (f s * a), by rw [f.map_smul, smul_mul_assoc] },
  haveI : is_scalar_tower S A A :=
  { smul_assoc := λ r a b, mul_assoc _ _ _ },
  have : ∀ x, H.out.lift g.to_linear_map (algebra_map R' S' x) = g x := H.out.lift_eq _,
  refine alg_hom.of_linear_map ((H.out.lift g.to_linear_map).restrict_scalars R) _ _,
  { dsimp only [linear_map.restrict_scalars_apply],
    rw [← (algebra_map R' S').map_one, this, g.map_one] },
  { intros x y,
    apply H.out.induction_on x,
    { rw [zero_mul, map_zero, zero_mul] },
    rotate,
    { intros s s' e, dsimp only [linear_map.restrict_scalars_apply] at e ⊢,
      rw [linear_map.map_smul, smul_mul_assoc, linear_map.map_smul, e, smul_mul_assoc] },
    { intros s s' e₁ e₂, dsimp only [linear_map.restrict_scalars_apply] at e₁ e₂ ⊢,
      rw [add_mul, map_add, map_add, add_mul, e₁, e₂] },
    intro x, dsimp, rw this, apply H.out.induction_on y,
    { rw [mul_zero, map_zero, mul_zero] },
    { intro y, dsimp, rw [← _root_.map_mul, this, this, _root_.map_mul] },
    { intros s s' e,
      rw [mul_comm, smul_mul_assoc, linear_map.map_smul, linear_map.map_smul, mul_comm, e],
      change f s * (g x * _) = g x * (f s * _),
      rw [← mul_assoc, ← mul_assoc, hf] },
    { intros s s' e₁ e₂, rw [mul_add, map_add, map_add, mul_add, e₁, e₂] }, }
end

@[simp]
lemma algebra.pushout_desc_left [H : algebra.is_pushout R S R' S']
  {A : Type*} [semiring A] [algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) (x : S) :
  algebra.pushout_desc S' f g H (algebra_map S S' x) = f x :=
begin
  rw [algebra.pushout_desc_apply, algebra.algebra_map_eq_smul_one, linear_map.map_smul,
    ← algebra.pushout_desc_apply S' f g H, _root_.map_one],
  exact mul_one (f x)
end

lemma algebra.lift_alg_hom_comp_left [H : algebra.is_pushout R S R' S']
  {A : Type*} [semiring A] [algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) :
  (algebra.pushout_desc S' f g H).comp (to_alg_hom R S S') = f :=
alg_hom.ext (λ x, (algebra.pushout_desc_left S' f g H x : _))

@[simp]
lemma algebra.pushout_desc_right [H : algebra.is_pushout R S R' S']
  {A : Type*} [semiring A] [algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) (x : R') :
  algebra.pushout_desc S' f g H (algebra_map R' S' x) = g x :=
begin
  apply_with @@is_base_change.lift_eq { instances := ff },
end

lemma algebra.lift_alg_hom_comp_right [H : algebra.is_pushout R S R' S']
  {A : Type*} [semiring A] [algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) :
  (algebra.pushout_desc S' f g H).comp (to_alg_hom R R' S') = g :=
alg_hom.ext (λ x, (algebra.pushout_desc_right S' f g H x : _))

@[ext]
lemma algebra.is_pushout.alg_hom_ext [H : algebra.is_pushout R S R' S']
  {A : Type*} [semiring A] [algebra R A] {f g : S' →ₐ[R] A}
  (h₁ : f.comp (to_alg_hom R R' S') = g.comp (to_alg_hom R R' S'))
  (h₂ : f.comp (to_alg_hom R S S') = g.comp (to_alg_hom R S S')) : f = g :=
begin
  ext x,
  apply H.1.induction_on x,
  { simp only [map_zero] },
  { exact alg_hom.congr_fun h₁ },
  { intros s s' e, rw [algebra.smul_def, f.map_mul, g.map_mul, e],
    congr' 1, exact (alg_hom.congr_fun h₂ s : _) },
  { intros s₁ s₂ e₁ e₂, rw [map_add, map_add, e₁, e₂] }
end

end is_base_change
