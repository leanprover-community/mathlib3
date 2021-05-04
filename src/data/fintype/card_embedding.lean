/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import data.fintype.card
import data.equiv.fin
import data.nat.factorial
import tactic
import tactic.slim_check

/-!
# Birthday Problem

This file establishes the cardinality of `α ↪ β` in full generality.
-/

open finset

local notation `|` x `|` := finset.card x
local notation `‖` x `‖` := fintype.card x

namespace fintype

def function_thing {α β γ : Type*} :
((α ⊕ β) → γ) ≃ (Σ f : α → γ, β → γ) :=
{ to_fun := _,
  inv_fun := _,
  left_inv := _,
  right_inv := _ }

def to_be_named {α β γ : Type*} :
((α ⊕ β) ↪ γ) ≃ (Σ f : α ↪ γ, β ↪ (set.range f).compl) :=
{ to_fun := λ f, ⟨function.embedding.inl.trans f, ⟨λ b, ⟨f (sum.inr b),
  begin
    apply set.mem_compl,
    suffices : ∀ (x : α), ¬f (sum.inl x) = f (sum.inr b), by simpa,
    intros x,
    rw [function.injective.eq_iff f.injective],
    simp only [not_false_iff]
  end⟩, by sorry⟩⟩,
  inv_fun := λ ⟨f, g⟩, ⟨function_thing.symm ⟨f, λ x, g x⟩, begin intros a b, by sorry end⟩,
  left_inv := begin intro f, ext, cases x with a b; sorry end,
  right_inv := _ }

private lemma card_embedding_aux (n : ℕ) (β) [fintype β] [decidable_eq β] (h : n ≤ ‖β‖) :
  ‖fin n ↪ β‖ = nat.desc_fac (‖β‖ - n) n :=
begin
  induction n with n hn,
  { nontriviality (fin 0 ↪ β),
  rw [nat.desc_fac_zero, fintype.card_eq_one_iff],
  refine ⟨nonempty.some nontrivial.to_nonempty, λ x, function.embedding.ext fin.elim0⟩ },

  rw [nat.succ_eq_add_one, ←card_congr (equiv.embedding_congr fin_sum_fin_equiv (equiv.refl β))],
  swap, apply_instance,
  rw card_congr to_be_named,
  swap, apply_instance,
  have : ∀ (f : fin n ↪ β), ‖fin 1 ↪ ↥((set.range f).compl)‖ = ‖β‖ - n, by sorry,
  simp, simp [this, card_univ], rw hn ((nat.lt_of_succ_le h).le), sorry
end

lemma asd (a n : ℕ) (h : n < a) : (a - n).desc_fac n * (a - n) = (a - (n + 1)).desc_fac (n + 1) :=
  by slim_check -- seems okay

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
