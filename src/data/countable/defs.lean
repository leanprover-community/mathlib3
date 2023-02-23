/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.finite.defs

/-!
# Countable types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define a typeclass saying that a given `Sort*` is countable. See also `encodable`
for a version that singles out a specific encoding of elements of `α` by natural numbers.

This file also provides a few instances of this typeclass. More instances can be found in other
files.
-/

open function
universes u v
variables {α : Sort u} {β : Sort v}

/-!
### Definition and basic properties
-/

/-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
@[mk_iff countable_iff_exists_injective] class countable (α : Sort u) : Prop :=
(exists_injective_nat [] : ∃ f : α → ℕ, injective f)

instance : countable ℕ := ⟨⟨id, injective_id⟩⟩

export countable (exists_injective_nat)

protected lemma function.injective.countable [countable β] {f : α → β} (hf : injective f) :
  countable α :=
let ⟨g, hg⟩ := exists_injective_nat β in ⟨⟨g ∘ f, hg.comp hf⟩⟩

protected lemma function.surjective.countable [countable α] {f : α → β} (hf : surjective f) :
  countable β :=
(injective_surj_inv hf).countable

lemma exists_surjective_nat (α : Sort u) [nonempty α] [countable α] : ∃ f : ℕ → α, surjective f :=
let ⟨f, hf⟩ := exists_injective_nat α in ⟨inv_fun f, inv_fun_surjective hf⟩

lemma countable_iff_exists_surjective [nonempty α] : countable α ↔ ∃ f : ℕ → α, surjective f :=
⟨@exists_surjective_nat _ _, λ ⟨f, hf⟩, hf.countable⟩

lemma countable.of_equiv (α : Sort*) [countable α] (e : α ≃ β) : countable β :=
e.symm.injective.countable

lemma equiv.countable_iff (e : α ≃ β) : countable α ↔ countable β :=
⟨λ h, @countable.of_equiv _ _ h e, λ h, @countable.of_equiv _ _ h e.symm⟩

instance {β : Type v} [countable β] : countable (ulift.{u} β) :=
countable.of_equiv _ equiv.ulift.symm

/-!
### Operations on `Sort*`s
-/

instance [countable α] : countable (plift α) := equiv.plift.injective.countable

@[priority 100]
instance subsingleton.to_countable [subsingleton α] : countable α :=
⟨⟨λ _, 0, λ x y h, subsingleton.elim x y⟩⟩

@[priority 500]
instance [countable α] {p : α → Prop} : countable {x // p x} := subtype.val_injective.countable

instance {n : ℕ} : countable (fin n) :=
function.injective.countable (@fin.eq_of_veq n)

@[priority 100]
instance finite.to_countable [finite α] : countable α :=
let ⟨n, ⟨e⟩⟩ := finite.exists_equiv_fin α in countable.of_equiv _ e.symm

instance : countable punit.{u} := subsingleton.to_countable

-- Since this always succeeds, there is no reason not to have this at normal priority.
-- Perhaps the `instance_priority` linter could be clever enough to notice this itself.
@[nolint instance_priority]
instance Prop.countable (p : Prop) : countable p := subsingleton.to_countable

instance bool.countable : countable bool :=
⟨⟨λ b, cond b 0 1, bool.injective_iff.2 nat.one_ne_zero⟩⟩

instance Prop.countable' : countable Prop := countable.of_equiv bool equiv.Prop_equiv_bool.symm

@[priority 500] instance [countable α] {r : α → α → Prop} : countable (quot r) :=
(surjective_quot_mk r).countable

@[priority 500] instance [countable α] {s : setoid α} : countable (quotient s) := quot.countable
