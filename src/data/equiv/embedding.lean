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

/-- Embeddings from a sum type are equivalent to two separate embeddings with disjoint ranges. -/
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
      { simp! only at f_eq, exfalso, exact disj ⟨⟨a₁, by simp⟩, ⟨b₂, by simp [f_eq]⟩⟩ },
      { simp! only at f_eq, exfalso, exact disj ⟨⟨a₂, by simp⟩, ⟨b₁, by simp [f_eq]⟩⟩ },
      { rw g.injective f_eq }
    end⟩,
  left_inv := λ f, by { dsimp only, ext, cases x; simp! },
  right_inv := λ ⟨⟨f, g⟩, _⟩, by { simp only [prod.mk.inj_iff], split; ext; simp! } }

/-- Embeddings whose range lies within a set are equivalent to embeddings to that set.
This is `function.embedding.cod_restrict` as an equiv. -/
def cod_restrict (α : Type*) {β : Type*} (bs : set β) :
  {f : α ↪ β // ∀ a, f a ∈ bs} ≃ (α ↪ bs) :=
{ to_fun := λ f, (f : α ↪ β).cod_restrict bs f.prop,
  inv_fun := λ f, ⟨f.trans (function.embedding.subtype _), λ a, (f a).prop⟩,
  left_inv := λ x, by ext; refl,
  right_inv := λ x, by ext; refl }

/-- Pairs of embeddings with disjoint ranges are equivalent to a dependent sum of embeddings,
in which the second embedding cannot take values in the range of the first. -/
def prod_embedding_disjoint_equiv_sigma_embedding_restricted {α β γ : Type*} :
  {f : (α ↪ γ) × (β ↪ γ) // disjoint (set.range f.1) (set.range f.2)} ≃
  (Σ f : α ↪ γ, β ↪ ↥((set.range f)ᶜ)) :=
(subtype_prod_equiv_sigma_subtype $
  λ (a : α ↪ γ) (b : β ↪ _), disjoint (set.range a) (set.range b)).trans $
  equiv.sigma_congr_right $ λ a,
    (subtype_equiv_prop begin
      ext f,
      rw [←set.range_subset_iff, set.subset_compl_iff_disjoint],
      exact disjoint.comm.trans disjoint_iff,
    end).trans (cod_restrict _ _)

/-- A combination of the above results, allowing us to turn one embedding over a sum type
into two dependent embeddings, the second of which avoids any members of the range
of the first. This is helpful for constructing larger embeddings out of smaller ones. -/
def sum_embedding_equiv_sigma_embedding_restricted {α β γ : Type*} :
  ((α ⊕ β) ↪ γ) ≃ (Σ f : α ↪ γ, β ↪ ↥((set.range f)ᶜ))
:= equiv.trans sum_embedding_equiv_prod_embedding_disjoint
               prod_embedding_disjoint_equiv_sigma_embedding_restricted

/-- Embeddings from a single-member type are equivalent to members of the target type. -/
def unique_embedding_equiv_result {α β : Type*} [unique α] : (α ↪ β) ≃ β :=
{ to_fun := λ f, f (default α),
  inv_fun := λ x, ⟨λ _, x, λ _ _ _, subsingleton.elim _ _⟩,
  left_inv := λ _, by { ext, simp_rw [function.embedding.coe_fn_mk], congr },
  right_inv := λ _, by simp }

end equiv
