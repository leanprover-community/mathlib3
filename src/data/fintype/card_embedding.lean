/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import data.fintype.card
import data.equiv.fin
import data.equiv.embedding

/-!
# Birthday Problem

This file establishes the cardinality of `α ↪ β` in full generality.
-/

local notation `|` x `|` := finset.card x
local notation `‖` x `‖` := fintype.card x

open_locale nat

local attribute [semireducible] function.embedding.fintype

namespace fintype

-- We need the separate `fintype α` instance as it contains data,
-- and may not match definitionally with the instance coming from `unique.fintype`.
lemma card_embedding_eq_of_unique
  {α β : Type*} [unique α] [fintype α] [fintype β] [decidable_eq α] [decidable_eq β]:
‖α ↪ β‖ = ‖β‖ := card_congr equiv.unique_embedding_equiv_result

private lemma card_embedding_aux (n : ℕ) (β) [fintype β] [decidable_eq β] (h : n ≤ ‖β‖) :
  ‖fin n ↪ β‖ = ‖β‖.desc_fact n :=
begin
  induction n with n hn,
  { nontriviality (fin 0 ↪ β),
    rw [nat.desc_fact_zero, fintype.card_eq_one_iff],
    refine ⟨nonempty.some nontrivial.to_nonempty, λ x, function.embedding.ext fin.elim0⟩ },

  rw [nat.succ_eq_add_one, ←card_congr (equiv.embedding_congr fin_sum_fin_equiv (equiv.refl β)),
    card_congr equiv.sum_embedding_equiv_sigma_embedding_restricted],
  -- these `rw`s create goals for instances, which it doesn't infer for some reason
  all_goals { try { apply_instance } },
  -- however, this needs to be done here instead of at the end
  -- else, a later `simp`, which depends on the `fintype` instance, won't work.

  have : ∀ (f : fin n ↪ β), ‖fin 1 ↪ ↥((set.range f)ᶜ)‖ = ‖β‖ - n,
  { intro f,
    rw card_embedding_eq_of_unique,
    rw card_of_finset' (finset.map f finset.univ)ᶜ,
    { rw [finset.card_compl, finset.card_map, finset.card_fin] },
    { simp } },

  -- putting `card_sigma` in `simp` causes it not to fully simplify
  rw card_sigma,
  simp only [this, finset.sum_const, finset.card_univ, nsmul_eq_mul, nat.cast_id],

  replace h := (nat.lt_of_succ_le h).le,
  rw [nat.desc_fact_succ, hn h, mul_comm]
end

/- Establishes the cardinality of the type of all injections between two finite types.  -/
@[simp] theorem card_embedding_eq {α β} [fintype α] [fintype β] [decidable_eq α] [decidable_eq β] :
‖α ↪ β‖ = (‖β‖.desc_fact ‖α‖) :=
begin
  by_cases h : ‖α‖ ≤ ‖β‖,
  { trunc_cases fintype.trunc_equiv_fin α with eq,
    rw fintype.card_congr (equiv.embedding_congr eq (equiv.refl β)),
    exact card_embedding_aux _ _ h },
  rw ←lt_iff_not_ge at h,
  rw [card_eq_zero_iff.mpr (function.embedding.is_empty_of_card_lt h),
    nat.desc_fact_eq_zero_iff_lt.mpr h],
end

/- The cardinality of embeddings from an infinite type to a finite type is zero.
This is a re-statement of the pigeonhole principle. -/
@[simp] lemma card_embedding_eq_of_infinite {α β} [infinite α] [fintype β] : ‖α ↪ β‖ = 0 :=
card_eq_zero_iff.mpr function.embedding.is_empty

end fintype
