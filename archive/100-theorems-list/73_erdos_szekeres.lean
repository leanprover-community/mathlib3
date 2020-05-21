/-
Copyright (c) 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark,
-/
import tactic
import data.setoid
import data.finset

/-!
The problem is referred to as "Ascending or Descending Sequences" on the 100 theorems list.

We understand this to refer to the theorem which is the subject of this wikipedia page :
https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Szekeres_theorem

## Tags

ramsey_theory
-/
universe u
open finset

variables {α P : Type u}[partial_order P] [fintype P]

def is_chain (x : set P) : Prop := ∀ a b ∈ x, a ≤ b ∨ b ≤ a

def is_antichain (x : set P) : Prop := ∀ a b ∈ x, ¬ (a ≤ b ∨ b ≤ a)

variable (P)
structure chain_decomposition :=
(val : setoid P )
(chains : set (set P))
(chains_spec : chains = setoid.classes val)
(chain_spec : ∀ x ∈ chains, is_chain x)

structure finite_chain_decomposition :=
(val : chain_decomposition P)
(size : ℕ)
(finite : set.finite val.chains)
(chains : finset (set P))
(chains_spec : set.finite.to_finset finite = chains)
(size_spec : size = card chains)

variable {P}

-- instance : has_lift (finset α) (set α) := begin
-- refine {lift := λ x, {a : α | a ∈ x}},
end

instance {β : Type u} [fintype β] : has_lift (set β) (finset β) :=
begin
refine {lift := _},
intro x,
have key : set.finite x,
exact set.finite.of_fintype x,
exact set.finite.to_finset key,
end

lemma coe_roundtrip (x : finset α) : set.finite (coe x : set α) :=
begin
exact set.finite.of_fintype ↑x,
end

lemma dilworth_aux
(C : finite_chain_decomposition P)
(x : finset P)
(hx : is_antichain (coe x : set P)) :
C.size ≤ card x
:=
begin

end

variable (P)
theorem dilworth :
∃ (C : finite_chain_decomposition P) (x : finset P) (hx : is_antichain (coe x : set P)),
  C.size = card x
:=
begin

end

theorem dilworth_corr (n : ℕ) :
(∃ C : finite_chain_decomposition P, C.size ≤ n) ∨
(∃ (x : finset P) (hx : is_antichain (coe x : set P)), n ≤ card x)
:=
begin

end


theorem erdos_szekeres
(α : Type*) [linear_order α] (n m k : ℕ) (hk : k + 1 = n * m) (f : fin k → α) :
(∃ x : finset (fin k), card x = n + 1 ∧ ∀ a b ∈ x, a ≤ b → f a ≤ f b) ∨
(∃ x : finset (fin k), card x = m + 1 ∧ ∀ a b ∈ x, a ≤ b → f b ≤ f a)
:=
begin
let le := λ a b, a ≤ b ∧ f a ≤ f b,
have le_is_poset : partial_order (fin k),
refine {le := le,
 lt := λ a b, le a b ∧ ¬ le b a,
 le_refl := by { intro a, split; refl },
 le_trans := by { intros _ _ _ ha hb, cases ha, cases hb, split; {transitivity; assumption} },
 lt_iff_le_not_le := by tidy,
 le_antisymm := by { intros _ _ h1 h2, apply le_antisymm h1.left h2.left} },

--  tidy,
--  intros, split, simp only [and_imp, not_and, not_le],
--   {tidy,},
end
