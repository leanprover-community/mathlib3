/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import data.fintype.big_operators
import logic.equiv.embedding

/-!
# Number of embeddings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file establishes the cardinality of `α ↪ β` in full generality.
-/

local notation (name := finset.card) `|` x `|` := finset.card x
local notation (name := fintype.card) `‖` x `‖` := fintype.card x

open function
open_locale nat big_operators

namespace fintype

lemma card_embedding_eq_of_unique {α β : Type*} [unique α] [fintype β] [fintype (α ↪ β)] :
  ‖α ↪ β‖ = ‖β‖ := card_congr equiv.unique_embedding_equiv_result

/- Establishes the cardinality of the type of all injections between two finite types. -/
@[simp] theorem card_embedding_eq {α β} [fintype α] [fintype β] [fintype (α ↪ β)] :
  ‖α ↪ β‖ = (‖β‖.desc_factorial ‖α‖) :=
begin
  classical,
  unfreezingI { induction ‹fintype α› using fintype.induction_empty_option
    with α₁ α₂ h₂ e ih α h ih },
  { letI := fintype.of_equiv _ e.symm,
    rw [← card_congr (equiv.embedding_congr e (equiv.refl β)), ih, card_congr e] },
  { rw [card_pempty, nat.desc_factorial_zero, card_eq_one_iff],
    exact ⟨embedding.of_is_empty, λ x, fun_like.ext _ _ is_empty_elim⟩ },
  { rw [card_option, nat.desc_factorial_succ, card_congr (embedding.option_embedding_equiv α β),
      card_sigma, ← ih],
    simp only [fintype.card_compl_set, fintype.card_range, finset.sum_const, finset.card_univ,
      smul_eq_mul, mul_comm] },
end

/- The cardinality of embeddings from an infinite type to a finite type is zero.
This is a re-statement of the pigeonhole principle. -/
@[simp] lemma card_embedding_eq_of_infinite {α β : Type*} [infinite α] [fintype β]
  [fintype (α ↪ β)] :
  ‖α ↪ β‖ = 0 :=
card_eq_zero

end fintype
