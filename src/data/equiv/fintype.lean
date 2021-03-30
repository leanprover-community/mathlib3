/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.equiv.basic
import data.fintype.basic
import group_theory.perm.sign

/-! # Equivalence between fintypes

This file contains some basic results on equivalences where one or both
sides of the equivalence are `fintype`s.

# Main definitions

 - `function.embedding.to_equiv_range`: computably turn an embedding of a
   fintype into an `equiv` of the domain to its range
 - `equiv.perm.via_embedding : perm α → (α ↪ β) → perm β` extends the domain of
   a permutation, fixing everything outside the range of the embedding

# Implementation details

 - `function.embedding.to_equiv_range` uses a computable inverse, but one that has poor
   computational performance, since it operates by exhaustive search over the input `fintype`s.
-/

variables {α β : Type*} [fintype α] [decidable_eq β] (e : equiv.perm α) (f : α ↪ β)

/--
Computably turn an embedding `f : α ↪ β` into an equiv `α ≃ set.range f`,
if `α` is a `fintype`. Has poor computational performance, due to exhaustive searching in
constructed inverse. When a better inverse is known,
use `equiv.set.range_of_left_inverse` instead.
-/
def function.embedding.to_equiv_range : α ≃ set.range f :=
⟨λ a, ⟨f a, set.mem_range_self a⟩, f.inv_of_mem_range, λ _, by simp, λ _, by simp⟩

@[simp] lemma function.embedding.to_equiv_range_apply (a : α) :
  f.to_equiv_range a = ⟨f a, set.mem_range_self a⟩ := rfl

@[simp] lemma function.embedding.to_equiv_range_symm_apply_self (a : α) :
  f.to_equiv_range.symm ⟨f a, set.mem_range_self a⟩ = a :=
by simp [equiv.symm_apply_eq]

lemma function.embedding.to_equiv_range_eq_range :
  f.to_equiv_range = equiv.set.range f f.injective :=
by { ext, simp }

/--
Extend the domain of `e : equiv.perm α`, mapping it through `f : α ↪ β`.
Everything outside of `set.range f` is kept fixed. Has poor computational performance,
due to exhaustive searching in constructed inverse.
-/
def equiv.perm.via_embedding : equiv.perm β :=
equiv.perm.subtype_congr (equiv.perm_congr f.to_equiv_range e) (equiv.refl _)

@[simp] lemma equiv.perm.via_embedding_apply_image (a : α) :
  e.via_embedding f (f a) = f (e a) :=
by simp [equiv.perm.via_embedding]

@[simp] lemma equiv.perm.via_embedding_sign [decidable_eq α] [fintype β] :
  equiv.perm.sign (e.via_embedding f) = equiv.perm.sign e :=
by simp [equiv.perm.via_embedding]

variable {f}

lemma equiv.perm.via_embedding_apply_not_image {b : β} (h : b ∉ set.range f) :
  e.via_embedding f b = b :=
by simp [equiv.perm.via_embedding, h]
