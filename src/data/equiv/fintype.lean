/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.equiv.basic
import data.set.finite
import group_theory.perm.sign

/-! # Equivalence between fintypes

This file contains some basic results on equivalences where one or both
sides of the equivalence are `fintype`s.

# Main definitions

 - `function.embedding.to_equiv_range`: computably turn an embedding of a
   fintype into an `equiv` of the domain to its range
 - `equiv.perm.via_fintype_embedding : perm α → (α ↪ β) → perm β` extends the domain of
   a permutation, fixing everything outside the range of the embedding

# Implementation details

 - `function.embedding.to_equiv_range` uses a computable inverse, but one that has poor
   computational performance, since it operates by exhaustive search over the input `fintype`s.
-/

variables {α β : Type*} [fintype α] [decidable_eq β] (e : equiv.perm α) (f : α ↪ β)

/--
Computably turn an embedding `f : α ↪ β` into an equiv `α ≃ set.range f`,
if `α` is a `fintype`. Has poor computational performance, due to exhaustive searching in
constructed inverse. When a better inverse is known, use `equiv.of_left_inverse'` or
`equiv.of_left_inverse` instead. This is the computable version of `equiv.of_injective`.
-/
def function.embedding.to_equiv_range : α ≃ set.range f :=
⟨λ a, ⟨f a, set.mem_range_self a⟩, f.inv_of_mem_range, λ _, by simp, λ _, by simp⟩

@[simp] lemma function.embedding.to_equiv_range_apply (a : α) :
  f.to_equiv_range a = ⟨f a, set.mem_range_self a⟩ := rfl

@[simp] lemma function.embedding.to_equiv_range_symm_apply_self (a : α) :
  f.to_equiv_range.symm ⟨f a, set.mem_range_self a⟩ = a :=
by simp [equiv.symm_apply_eq]

lemma function.embedding.to_equiv_range_eq_of_injective :
  f.to_equiv_range = equiv.of_injective f f.injective :=
by { ext, simp }

/--
Extend the domain of `e : equiv.perm α`, mapping it through `f : α ↪ β`.
Everything outside of `set.range f` is kept fixed. Has poor computational performance,
due to exhaustive searching in constructed inverse due to using `function.embedding.to_equiv_range`.
When a better `α ≃ set.range f` is known, use `equiv.perm.via_set_range`.
When `[fintype α]` is not available, a noncomputable version is available as
`equiv.perm.via_embedding`.
-/
def equiv.perm.via_fintype_embedding : equiv.perm β :=
e.extend_domain f.to_equiv_range

@[simp] lemma equiv.perm.via_fintype_embedding_apply_image (a : α) :
  e.via_fintype_embedding f (f a) = f (e a) :=
begin
  rw equiv.perm.via_fintype_embedding,
  convert equiv.perm.extend_domain_apply_image e _ _
end

lemma equiv.perm.via_fintype_embedding_apply_mem_range {b : β} (h : b ∈ set.range f) :
  e.via_fintype_embedding f b = f (e (f.inv_of_mem_range ⟨b, h⟩)) :=
by simpa [equiv.perm.via_fintype_embedding, equiv.perm.extend_domain_apply_subtype, h]

lemma equiv.perm.via_fintype_embedding_apply_not_mem_range {b : β} (h : b ∉ set.range f) :
  e.via_fintype_embedding f b = b :=
by rwa [equiv.perm.via_fintype_embedding, equiv.perm.extend_domain_apply_not_subtype]

@[simp] lemma equiv.perm.via_fintype_embedding_sign [decidable_eq α] [fintype β] :
  equiv.perm.sign (e.via_fintype_embedding f) = equiv.perm.sign e :=
by simp [equiv.perm.via_fintype_embedding]

namespace equiv
variables {p q : α → Prop} [decidable_pred p] [decidable_pred q]

/-- If `e` is an equivalence between two subtypes of a fintype `α`, `e.to_compl`
is an equivalence between the complement of those subtypes.

See also `equiv.compl`, for a computable version when a term of type
`{e' : α ≃ α // ∀ x : {x // p x}, e' x = e x}` is known. -/
noncomputable def to_compl (e : {x // p x} ≃ {x // q x}) : {x // ¬ p x} ≃ {x // ¬ q x} :=
classical.choice (fintype.card_eq.mp (fintype.card_compl_eq_card_compl (fintype.card_congr e)))

/-- If `e` is an equivalence between two subtypes of a fintype `α`, `e.extend_subtype`
is a permutation of `α` acting like `e` on the subtypes and doing something arbitrary outside.

Note that when `p = q`, `equiv.perm.subtype_congr e (equiv.refl _)` can be used instead. -/
noncomputable abbreviation extend_subtype (e : {x // p x} ≃ {x // q x}) : perm α :=
subtype_congr e e.to_compl

lemma extend_subtype_apply_of_mem (e : {x // p x} ≃ {x // q x}) (x) (hx : p x) :
  e.extend_subtype x = e ⟨x, hx⟩ :=
by { dunfold extend_subtype,
     simp only [subtype_congr, equiv.trans_apply, equiv.sum_congr_apply],
     rw [sum_compl_apply_symm_of_pos _ _ hx, sum.map_inl, sum_compl_apply_inl] }

lemma extend_subtype_mem (e : {x // p x} ≃ {x // q x}) (x) (hx : p x) :
  q (e.extend_subtype x) :=
by { convert (e ⟨x, hx⟩).2,
     rw [e.extend_subtype_apply_of_mem _ hx, subtype.val_eq_coe] }

lemma extend_subtype_apply_of_not_mem (e : {x // p x} ≃ {x // q x}) (x) (hx : ¬ p x) :
  e.extend_subtype x = e.to_compl ⟨x, hx⟩ :=
by { dunfold extend_subtype,
     simp only [subtype_congr, equiv.trans_apply, equiv.sum_congr_apply],
     rw [sum_compl_apply_symm_of_neg _ _ hx, sum.map_inr, sum_compl_apply_inr] }

lemma extend_subtype_not_mem (e : {x // p x} ≃ {x // q x}) (x) (hx : ¬ p x) :
  ¬ q (e.extend_subtype x) :=
by { convert (e.to_compl ⟨x, hx⟩).2,
     rw [e.extend_subtype_apply_of_not_mem _ hx, subtype.val_eq_coe] }

end equiv
