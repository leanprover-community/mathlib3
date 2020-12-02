/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Wieser
-/

import linear_algebra.tensor_product
import linear_algebra.multilinear

/-! # Tensor product of multlinear maps

This file provides a single definition, `multilinear_map.of_tmul`.begin
-/

open_locale tensor_product

namespace sum.elim

instance {ι₁ ι₂ : Type*}
  {M : ι₁ → Type*} [∀ i, add_comm_monoid (M i)]
  {N : ι₂ → Type*} [∀ i, add_comm_monoid (N i)]
  (i : ι₁ ⊕ ι₂)
  : add_comm_monoid (i.elim M N) := by cases i; dsimp; apply_instance

instance {ι₁ ι₂ : Type*} [decidable_eq ι₁] [decidable_eq ι₂]
  (R : Type*) [semiring R]
  {M : ι₁ → Type*} [∀ i, add_comm_monoid (M i)] [∀ i, semimodule R (M i)]
  {N : ι₂ → Type*} [∀ i, add_comm_monoid (N i)] [∀ i, semimodule R (N i)]
  (i : ι₁ ⊕ ι₂)
  : semimodule R (i.elim M N) := by cases i; dsimp; apply_instance


end sum.elim

-- gh-5178
namespace function

/-- Dependent version of update_comp_eq_of_injective -/
lemma update_comp_eq_of_injective' {α β : Sort*} {γ : β → Sort*} [decidable_eq α] [decidable_eq β]
  (g : Π b, γ b) {f : α → β} (hf : function.injective f) (i : α) (a : γ (f i)) :
  (λ j, function.update g (f i) a (f j)) = function.update (λ i, g (f i)) i a :=
begin
  ext j,
  by_cases h : j = i,
  { rw h, simp },
  { have : f j ≠ f i := hf.ne h,
    simp [h, this] }
end

/-- Dependent version of update_comp_eq_of_not_mem_range -/
lemma update_comp_eq_of_not_mem_range' {α β : Type*} {γ : β → Type*} [decidable_eq β]
  (g : Π b, γ b) {f : α → β} {i : β} (a : γ i) (h : i ∉ set.range f) :
  (λ j, (function.update g i a) (f j)) = (λ j, g (f j)) :=
begin
  ext p,
  have : f p ≠ i,
  { by_contradiction H,
    push_neg at H,
    rw ← H at h,
    exact h (set.mem_range_self _) },
  simp [this],
end

end function

namespace multilinear_map

universes u

section
variables  {ι₁ ι₂ : Type*} [decidable_eq ι₁] [decidable_eq ι₂]
  (R : Type*) [comm_semiring R]
  {M : ι₁ → Type u} [∀ i, add_comm_monoid (M i)] [∀ i, semimodule R (M i)]
  {N : ι₂ → Type u} [∀ i, add_comm_monoid (N i)] [∀ i, semimodule R (N i)]
  {M' : Type*} [add_comm_monoid M'] [semimodule R M']
  {N' : Type*} [add_comm_monoid N'] [semimodule R N']

def of_tmul_aux
  (a : multilinear_map R M M') (b : multilinear_map R N N') :
  multilinear_map R (sum.elim M N) (M' ⊗[R] N')
  :=
{ to_fun := λ v, a (λ i, v (sum.inl i)) ⊗ₜ b (λ i, v (sum.inr i)),
  map_add' := λ v i p q, begin
    cases i,
    {
      have : ∀ {α β : Type*} (a : α),
        (sum.inl a : α ⊕ β) ∉ set.range (@sum.inr α β) := by simp,
      iterate 3 {
        rw [function.update_comp_eq_of_injective' _ sum.injective_inl,
            function.update_comp_eq_of_not_mem_range' _ _ (this i)],},
      rw [a.map_add, tensor_product.add_tmul],
    },
    {
      have : ∀ {α β : Type*} (b : β),
        (sum.inr b : α ⊕ β) ∉ set.range (@sum.inl α β) := by simp,
      iterate 3 {
        rw [function.update_comp_eq_of_injective' _ sum.injective_inr,
            function.update_comp_eq_of_not_mem_range' _ _ (this i)],},
      rw [b.map_add, tensor_product.tmul_add],
    }
  end,
  map_smul' := λ v i c p, begin
    cases i,
    {
      have : ∀ {α β : Type*} (a : α),
        (sum.inl a : α ⊕ β) ∉ set.range (@sum.inr α β) := by simp,
      iterate 2 {
        rw [function.update_comp_eq_of_injective' _ sum.injective_inl,
            function.update_comp_eq_of_not_mem_range' _ _ (this i)],},
      rw [a.map_smul, tensor_product.smul_tmul'],
    },
    {
      have : ∀ {α β : Type*} (b : β),
        (sum.inr b : α ⊕ β) ∉ set.range (@sum.inl α β) := by simp,
      iterate 2 {
        rw [function.update_comp_eq_of_injective' _ sum.injective_inr,
            function.update_comp_eq_of_not_mem_range' _ _ (this i)]},
      rw [b.map_smul, tensor_product.tmul_smul],
    },
  end }

/-- Given a tensor product of two multilinear maps, produce a single multilinear map over the
sum of their indices into the tensor product of their codomains. -/
def of_tmul :
  multilinear_map R M M' ⊗ multilinear_map R N N' →ₗ[R]
  multilinear_map R (sum.elim M N) (M' ⊗[R] N') :=
tensor_product.lift $ linear_map.mk₂ R (of_tmul_aux R)
  (λ m₁ m₂ n, by { ext, simp [of_tmul_aux, tensor_product.add_tmul] })
  (λ c m n,   by { ext, simp [of_tmul_aux, tensor_product.smul_tmul'] })
  (λ m n₁ n₂, by { ext, simp [of_tmul_aux, tensor_product.tmul_add] })
  (λ c m n,   by { ext, simp [of_tmul_aux, tensor_product.tmul_smul] })

@[simp] lemma of_tmul_apply_tmul (a : multilinear_map R M M') (b : multilinear_map R N N') (v) :
  of_tmul R (a ⊗ₜ b) v = a (λ i, v (sum.inl i)) ⊗ₜ b (λ i, v (sum.inr i)) := rfl
end

section
variables  {ι₁ ι₂ : Type*} [decidable_eq ι₁] [decidable_eq ι₂]
  (R : Type*) [comm_semiring R]
  {M : Type u} [add_comm_monoid M] [semimodule R M]
  {M' : Type*} [add_comm_monoid M'] [semimodule R M']
  {N' : Type*} [add_comm_monoid N'] [semimodule R N']

lemma sum.elim_const {α β γ : Sort*} (a : γ) : sum.elim (λ _ : α, a) (λ _ : β, a) = λ i, a :=
funext $ λ x, by cases x; refl

set_option pp.implicit true

def of_tmul' :
  multilinear_map R (λ i : ι₁, M) M' ⊗[R] multilinear_map R (λ i : ι₂, M) N' →ₗ[R]
  multilinear_map R (λ i : ι₁ ⊕ ι₂, M) (M' ⊗[R] N') :=
  begin
    have : multilinear_map R (λ i : ι₁, M) M' ⊗ multilinear_map R (λ i : ι₂, M) N' →ₗ[R]
      multilinear_map R (sum.elim (λ i : ι₁, M) (λ i : ι₂, M)) (M' ⊗[R] N') :=
        of_tmul R,
    have h := @sum.elim_const ι₁ ι₂ _ M,
    convert this,
    { ext i, cases i; refl },
    { ext i, refl, intros, cases a'; refl,},
    { ext i, refl, intros, cases a'; refl,},
    { ext i, cases i; refl },
    { ext i, refl, intros, cases a'; refl,},
    { ext i, refl, intros, cases a'; refl,},
    { ext i, cases i; refl },
    { ext i, refl, intros, cases a'; refl,},
    { ext i, refl, intros, cases a'; refl,},
  end

@[simp] lemma of_tmul'_apply_tmul
  (a : multilinear_map R (λ i : ι₁, M) M') (b : multilinear_map R (λ i : ι₂, M) N') (v) :
  of_tmul' R (a ⊗ₜ b) v = a (λ i, v (sum.inl i)) ⊗ₜ b (λ i, v (sum.inr i)) :=
begin
  let v' : Π (i : ι₁ ⊕ ι₂), sum.elim (λ i : ι₁, M) (λ i : ι₂, M) i := by {
    convert v,
    dsimp,
    rw sum.elim_const,
  },
  -- convert of_tmul_apply_tmul R a b v',
  simp [v', of_tmul'],

end

end

end multilinear_map
