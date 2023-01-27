/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import logic.equiv.nat
import logic.equiv.fin
import data.countable.defs

/-!
# Countable types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we provide basic instances of the `countable` typeclass defined elsewhere.
-/

universes u v w

open function

instance : countable ℤ := countable.of_equiv ℕ equiv.int_equiv_nat.symm

/-!
### Definition in terms of `function.embedding`
-/

section embedding

variables {α : Sort u} {β : Sort v}

lemma countable_iff_nonempty_embedding : countable α ↔ nonempty (α ↪ ℕ) :=
⟨λ ⟨⟨f, hf⟩⟩, ⟨⟨f, hf⟩⟩, λ ⟨f⟩, ⟨⟨f, f.2⟩⟩⟩

lemma nonempty_embedding_nat (α) [countable α] : nonempty (α ↪ ℕ) :=
countable_iff_nonempty_embedding.1 ‹_›

protected lemma function.embedding.countable [countable β] (f : α ↪ β) : countable α :=
f.injective.countable

end embedding

/-!
### Operations on `Type*`s
-/

section type

variables {α : Type u} {β : Type v} {π : α → Type w}

instance [countable α] [countable β] : countable (α ⊕ β) :=
begin
  rcases exists_injective_nat α with ⟨f, hf⟩,
  rcases exists_injective_nat β with ⟨g, hg⟩,
  exact (equiv.nat_sum_nat_equiv_nat.injective.comp $ hf.sum_map hg).countable
end

instance [countable α] : countable (option α) :=
countable.of_equiv _ (equiv.option_equiv_sum_punit α).symm

instance [countable α] [countable β] : countable (α × β) :=
begin
  rcases exists_injective_nat α with ⟨f, hf⟩,
  rcases exists_injective_nat β with ⟨g, hg⟩,
  exact (nat.mkpair_equiv.injective.comp $ hf.prod_map hg).countable
end

instance [countable α] [Π a, countable (π a)] : countable (sigma π) :=
begin
  rcases exists_injective_nat α with ⟨f, hf⟩,
  choose g hg using λ a, exists_injective_nat (π a),
  exact ((equiv.sigma_equiv_prod ℕ ℕ).injective.comp $ hf.sigma_map hg).countable
end

end type

section sort

variables {α : Sort u} {β : Sort v} {π : α → Sort w}

/-!
### Operations on and `Sort*`s
-/

@[priority 500]
instance set_coe.countable {α} [countable α] (s : set α) : countable s := subtype.countable

instance [countable α] [countable β] : countable (psum α β) :=
countable.of_equiv (plift α ⊕ plift β) (equiv.plift.sum_psum equiv.plift)

instance [countable α] [countable β] : countable (pprod α β) :=
countable.of_equiv (plift α × plift β) (equiv.plift.prod_pprod equiv.plift)

instance [countable α] [Π a, countable (π a)] : countable (psigma π) :=
countable.of_equiv (Σ a : plift α, plift (π a.down)) (equiv.psigma_equiv_sigma_plift π).symm

instance [finite α] [Π a, countable (π a)] : countable (Π a, π a) :=
begin
  haveI : ∀ n, countable (fin n → ℕ),
  { intro n, induction n with n ihn,
    { apply_instance },
    { exactI countable.of_equiv _ (equiv.pi_fin_succ _ _).symm } },
  rcases finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩,
  have f := λ a, (nonempty_embedding_nat (π a)).some,
  exact ((embedding.Pi_congr_right f).trans (equiv.Pi_congr_left' _ e).to_embedding).countable
end

end sort
