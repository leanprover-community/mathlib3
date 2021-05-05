/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import logic.embedding
import data.set.lattice

/-!
# Equivalences on embeddings

This file shows some advanced equivalences on embeddings, useful for constructing larger
embeddings from smaller ones.
-/


open function.embedding

namespace equiv

/-- Embeddings from a sumtype are equivalent to two separate embeddings with disjoint ranges. -/
def sum_embedding_equiv_prod_embedding_disjoint {α β γ : Type*} :
((α ⊕ β) ↪ γ) ≃ {f : (α ↪ γ) × (β ↪ γ) // disjoint (set.range f.1) (set.range f.2)} :=
{ to_fun := λ f, ⟨(inl.trans f, inr.trans f),
  begin
    rintros _ ⟨⟨a, h⟩, ⟨b, rfl⟩⟩,
    simp only [trans_apply, inl_apply, inr_apply] at h,
    have : sum.inl a = sum.inr b := f.injective h,
    simp only at this,
    assumption
  end⟩,

  inv_fun := λ ⟨⟨f, g⟩, disj⟩,
    ⟨λ x, match x with
    | (sum.inl a) := f a
    | (sum.inr b) := g b
    end,
    begin
      rintros (a₁|b₁) (a₂|b₂) f_eq;
      simp only [equiv.coe_fn_symm_mk, sum.elim_inl, sum.elim_inr] at f_eq,
      { rw f.injective f_eq },
      { simp! only at f_eq, exfalso, exact disj ⟨⟨a₁, by simp⟩, ⟨b₂, by simp [f_eq]⟩⟩  },
      { simp! only at f_eq, exfalso, exact disj ⟨⟨a₂, by simp⟩, ⟨b₁, by simp [f_eq]⟩⟩  },
      { rw g.injective f_eq }
    end⟩,

  left_inv := λ f, by { dsimp only, ext, cases x; simp! },
  right_inv := λ ⟨⟨f, g⟩, _⟩, by { simp only [prod.mk.inj_iff], split; ext; simp! } }

/-- Pairs of embeddings with disjoint ranges are equivalent to a dependent sum of embeddings,
in which the second embedding cannot take values in the range of the first. -/
def prod_embedding_disjoint_equiv_sigma_embedding_restricted {α β γ : Type*} :
  {f : (α ↪ γ) × (β ↪ γ) // disjoint (set.range f.1) (set.range f.2)} ≃
  (Σ f : α ↪ γ, β ↪ (set.range f).compl) :=
{ to_fun := λ ⟨⟨f, g⟩, disj⟩, ⟨f, ⟨λ b, ⟨g b, set.disjoint_right.mp disj (⟨b, rfl⟩)⟩,
  λ _ _ eq, by { rw subtype.mk_eq_mk at eq, exact g.injective eq }⟩⟩, -- one day I'll figure out ▸

  inv_fun := λ ⟨f, g⟩, ⟨⟨f, g.trans (function.embedding.subtype _)⟩,
  begin
    dsimp only,
    have : set.range (g.trans (function.embedding.subtype (λ x, x ∈ (set.range f).compl)))
      ⊆ (set.range f).compl,
    { rintros _ ⟨t, rfl⟩, simp },
    exact set.disjoint_of_subset_right this disjoint_compl_right
  end⟩,

  right_inv := λ ⟨_,_⟩, by simp!,
  left_inv := λ ⟨⟨_,_⟩,_⟩, by { dsimp only, ext; simp! } }

/-- A simple combination of the above results, allowing us to simply combine embeddings
over a sum-type. -/
def sum_embedding_equiv_sigma_embedding_restricted {α β γ : Type*} :
  ((α ⊕ β) ↪ γ) ≃ (Σ f : α ↪ γ, β ↪ (set.range f).compl)
:= equiv.trans sum_embedding_equiv_prod_embedding_disjoint
               prod_embedding_disjoint_equiv_sigma_embedding_restricted

/-- Embeddings from a single-member type are equivalent to members of the target type. -/
def unique_embedding_equiv_result {α β : Type*} [unique α] : (α ↪ β) ≃ β :=
{ to_fun := λ f, f (default α),
  inv_fun := λ x, ⟨λ _, x, λ _ _ _, subsingleton.elim _ _⟩,
  left_inv := λ _, by { ext, simp_rw [function.embedding.coe_fn_mk], congr },
  right_inv := λ _, by simp }

end equiv
