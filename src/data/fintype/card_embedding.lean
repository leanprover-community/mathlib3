/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import data.fintype.card
import data.equiv.fin
import data.nat.factorial

/-!
# Birthday Problem

This file establishes the cardinality of `α ↪ β` in full generality.
-/

open finset

local notation `|` x `|` := finset.card x
local notation `‖` x `‖` := fintype.card x

namespace fintype

-- I wonder if this will be useful... can't find it on `library_search`
-- example {α β γ : Type*} : α ⊕ β → γ ≃ α → γ ⊕ β → γ := by library_search

lemma sum_embedding_equiv_disjoint_embedding {α β γ δ : Type*} :
  ((α ⊕ β) ↪ (γ ⊕ δ)) ≃ (α ↪ γ) ⊕ (β ↪ δ) := sorry

open function

private lemma card_embedding_aux (n : ℕ) (β) [fintype β] [decidable_eq β] (h : n ≤ ‖β‖) :
  ‖fin n ↪ β‖ = nat.desc_fac (‖β‖ - n) n :=
begin
  induction n with n hn,
  { nontriviality (fin 0 ↪ β),
  rw [nat.desc_fac_zero, fintype.card_eq_one_iff],
  refine ⟨nonempty.some nontrivial.to_nonempty, λ x, function.embedding.ext fin.elim0⟩ },
  {
    suffices : ‖(fin n ⊕ fin 1) ↪ β‖ = (‖β‖ - n.succ).desc_fac n.succ,
    { rw ←this,
      have : ((fin n ⊕ fin 1) ↪ β) ≃ (fin n.succ ↪ β) :=
        equiv.embedding_congr fin_sum_fin_equiv (equiv.refl _),
      rw ←of_equiv_card this, congr }, -- `congr` deals with different fintype instances

  }
end

variables {α β : Type*} [fintype α] [fintype β] [decidable_eq α] [decidable_eq β]

/- Establishes the cardinality of the type of all injections, if any exist.  -/
@[simp] theorem card_embedding (h : ‖α‖ ≤ ‖β‖) : ‖α ↪ β‖ = (nat.desc_fac (‖β‖ - ‖α‖) ‖α‖) :=
begin
  trunc_cases fintype.equiv_fin α with eq,
  rw fintype.card_congr (equiv.embedding_congr eq (equiv.refl β)),
  exact card_embedding_aux _ _ h,
end

/-- If `‖β‖ < ‖α‖` there is no embeddings `α ↪ β`. This is the pigeonhole principle. -/
@[simp] theorem card_embedding_eq_zero (h : ‖β‖ < ‖α‖) : ‖α ↪ β‖ = 0 :=
begin
  rw card_eq_zero_iff,
  intro f,
  obtain ⟨x, y, eq, fne⟩ := fintype.exists_ne_map_eq_of_card_lt f h,
  have := f.injective fne, contradiction
end

theorem card_embedding_eq_if: ‖α ↪ β‖ = if ‖α‖ ≤ ‖β‖ then nat.desc_fac (‖β‖ - ‖α‖) ‖α‖ else 0 :=
begin
  split_ifs with h,
    exact card_embedding h,
    exact card_embedding_eq_zero (not_le.mp h)
end

lemma card_embedding_eq_infinite {α β} [infinite α] [fintype β] : fintype.card (α ↪ β) = 0 :=
by erw [card, univ, function.embedding.fintype', finset.card_empty]

end fintype
