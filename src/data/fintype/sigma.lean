/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fintype.basic
import data.finset.sigma


/-!
# fintype instances for sigma types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open function
open_locale nat

universes u v

variables {α β γ : Type*}

open finset function

instance {α : Type*} (β : α → Type*)
  [fintype α] [∀ a, fintype (β a)] : fintype (sigma β) :=
⟨univ.sigma (λ _, univ), λ ⟨a, b⟩, by simp⟩

@[simp] lemma finset.univ_sigma_univ {α : Type*} {β : α → Type*} [fintype α] [∀ a, fintype (β a)] :
  (univ : finset α).sigma (λ a, (univ : finset (β a))) = univ := rfl

instance psigma.fintype {α : Type*} {β : α → Type*} [fintype α] [∀ a, fintype (β a)] :
  fintype (Σ' a, β a) :=
fintype.of_equiv _ (equiv.psigma_equiv_sigma _).symm
