/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import data.list.big_operators.basic

/-!
# Lists in product and sigma types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic properties of `list.product` and `list.sigma`, which are list constructions
living in `prod` and `sigma` types respectively. Their definitions can be found in
[`data.list.defs`](./defs). Beware, this is not about `list.prod`, the multiplicative product.
-/

variables {α β : Type*}

namespace list

/-! ### product -/

@[simp] lemma nil_product (l : list β) : product (@nil α) l = [] := rfl

@[simp] lemma product_cons (a : α) (l₁ : list α) (l₂ : list β)
        : product (a::l₁) l₂ = map (λ b, (a, b)) l₂ ++ product l₁ l₂ := rfl

@[simp] lemma product_nil : ∀ (l : list α), product l (@nil β) = []
| []     := rfl
| (a::l) := by rw [product_cons, product_nil]; refl

@[simp] lemma mem_product {l₁ : list α} {l₂ : list β} {a : α} {b : β} :
  (a, b) ∈ product l₁ l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ :=
by simp only [product, mem_bind, mem_map, prod.ext_iff, exists_prop,
  and.left_comm, exists_and_distrib_left, exists_eq_left, exists_eq_right]

lemma length_product (l₁ : list α) (l₂ : list β) :
  length (product l₁ l₂) = length l₁ * length l₂ :=
by induction l₁ with x l₁ IH; [exact (zero_mul _).symm,
  simp only [length, product_cons, length_append, IH,
    right_distrib, one_mul, length_map, add_comm]]


/-! ### sigma -/

variable {σ : α → Type*}

@[simp] lemma nil_sigma (l : Π a, list (σ a)) : (@nil α).sigma l = [] := rfl

@[simp] lemma sigma_cons (a : α) (l₁ : list α) (l₂ : Π a, list (σ a))
        : (a::l₁).sigma l₂ = map (sigma.mk a) (l₂ a) ++ l₁.sigma l₂ := rfl

@[simp] lemma sigma_nil : ∀ (l : list α), l.sigma (λ a, @nil (σ a)) = []
| []     := rfl
| (a::l) := by rw [sigma_cons, sigma_nil]; refl

@[simp] lemma mem_sigma {l₁ : list α} {l₂ : Π a, list (σ a)} {a : α} {b : σ a} :
  sigma.mk a b ∈ l₁.sigma l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ a :=
by simp only [list.sigma, mem_bind, mem_map, exists_prop, exists_and_distrib_left,
  and.left_comm, exists_eq_left, heq_iff_eq, exists_eq_right]

lemma length_sigma (l₁ : list α) (l₂ : Π a, list (σ a)) :
  length (l₁.sigma l₂) = (l₁.map (λ a, length (l₂ a))).sum :=
by induction l₁ with x l₁ IH; [refl,
simp only [map, sigma_cons, length_append, length_map, IH, sum_cons]]

end list
