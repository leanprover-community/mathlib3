/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import logic.embedding.basic
import data.set.image

/-!
# Interactions between embeddings and sets.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

universes u v w x

section equiv

variables {α : Sort u} {β : Sort v} (f : α ≃ β)

@[simp]
lemma equiv.as_embedding_range {α β : Sort*} {p : β → Prop} (e : α ≃ subtype p) :
  set.range e.as_embedding = set_of p :=
set.ext $ λ x, ⟨λ ⟨y, h⟩, h ▸ subtype.coe_prop (e y), λ hs, ⟨e.symm ⟨x, hs⟩, by simp⟩⟩

end equiv

namespace function
namespace embedding

/-- Embedding into `with_top α`. -/
@[simps]
def coe_with_top {α} : α ↪ with_top α := { to_fun := coe, ..embedding.some}

/-- Given an embedding `f : α ↪ β` and a point outside of `set.range f`, construct an embedding
`option α ↪ β`. -/
@[simps] def option_elim {α β} (f : α ↪ β) (x : β) (h : x ∉ set.range f) :
  option α ↪ β :=
⟨option.elim x f, option.injective_iff.2 ⟨f.2, h⟩⟩

/-- Equivalence between embeddings of `option α` and a sigma type over the embeddings of `α`. -/
@[simps]
def option_embedding_equiv (α β) : (option α ↪ β) ≃ Σ f : α ↪ β, ↥(set.range f)ᶜ :=
{ to_fun := λ f, ⟨coe_option.trans f, f none, λ ⟨x, hx⟩, option.some_ne_none x $ f.injective hx⟩,
  inv_fun := λ f, f.1.option_elim f.2 f.2.2,
  left_inv := λ f, ext $ by { rintro (_|_); simp [option.coe_def] },
  right_inv := λ ⟨f, y, hy⟩, by { ext; simp [option.coe_def] } }

/-- Restrict the codomain of an embedding. -/
def cod_restrict {α β} (p : set β) (f : α ↪ β) (H : ∀ a, f a ∈ p) : α ↪ p :=
⟨λ a, ⟨f a, H a⟩, λ a b h, f.injective (@congr_arg _ _ _ _ subtype.val h)⟩

@[simp] theorem cod_restrict_apply {α β} (p) (f : α ↪ β) (H a) :
  cod_restrict p f H a = ⟨f a, H a⟩ := rfl

open set

/-- `set.image` as an embedding `set α ↪ set β`. -/
@[simps apply] protected def image {α β} (f : α ↪ β) : set α ↪ set β :=
⟨image f, f.2.image_injective⟩

end embedding
end function

namespace set

/-- The injection map is an embedding between subsets. -/
@[simps apply] def embedding_of_subset {α} (s t : set α) (h : s ⊆ t) : s ↪ t :=
⟨λ x, ⟨x.1, h x.2⟩, λ ⟨x, hx⟩ ⟨y, hy⟩ h, by { congr, injection h }⟩

end set

section subtype

variable {α : Type*}

/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` is equivalent to a sum of
subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right, when
`disjoint p q`.

See also `equiv.sum_compl`, for when `is_compl p q`.  -/
@[simps apply] def subtype_or_equiv (p q : α → Prop) [decidable_pred p] (h : disjoint p q) :
  {x // p x ∨ q x} ≃ {x // p x} ⊕ {x // q x} :=
{ to_fun := subtype_or_left_embedding p q,
  inv_fun := sum.elim
    (subtype.imp_embedding _ _ (λ x hx, (or.inl hx : p x ∨ q x)))
    (subtype.imp_embedding _ _ (λ x hx, (or.inr hx : p x ∨ q x))),
  left_inv := λ x, begin
    by_cases hx : p x,
    { rw subtype_or_left_embedding_apply_left _ hx,
      simp [subtype.ext_iff] },
    { rw subtype_or_left_embedding_apply_right _ hx,
      simp [subtype.ext_iff] },
  end,
  right_inv := λ x, begin
    cases x,
    { simp only [sum.elim_inl],
      rw subtype_or_left_embedding_apply_left,
      { simp },
      { simpa using x.prop } },
    { simp only [sum.elim_inr],
      rw subtype_or_left_embedding_apply_right,
      { simp },
      { suffices : ¬ p x,
        { simpa },
        intro hp,
        simpa using h.le_bot x ⟨hp, x.prop⟩ } }
  end }

@[simp] lemma subtype_or_equiv_symm_inl (p q : α → Prop) [decidable_pred p] (h : disjoint p q)
  (x : {x // p x}) : (subtype_or_equiv p q h).symm (sum.inl x) = ⟨x, or.inl x.prop⟩ :=
rfl

@[simp] lemma subtype_or_equiv_symm_inr (p q : α → Prop) [decidable_pred p] (h : disjoint p q)
  (x : {x // q x}) : (subtype_or_equiv p q h).symm (sum.inr x) = ⟨x, or.inr x.prop⟩ :=
rfl

end subtype
