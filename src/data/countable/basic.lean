/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.nat.basic

/-!
# Countable `Sort*`s and `Type*`s

In this file we define a typeclass saying that a given `Sort*` is countable. See also `encodable`
for a version that singles out a specific encoding of elements of `α` by natural numbers.

-/

universes u v

open function

section sort

variables {α : Sort u} {β : Sort v}

/-!
### Definition and basic properties
-/

/-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
class countable (α : Sort u) : Prop :=
(out' : nonempty (α ↪ ℕ))

instance : countable ℕ := ⟨⟨embedding.refl ℕ⟩⟩

lemma countable_iff_exists_injective :
  countable α ↔ ∃ f : α → ℕ, injective f :=
⟨λ ⟨⟨f⟩⟩, ⟨f, f.2⟩, λ ⟨f, hf⟩, ⟨⟨⟨f, hf⟩⟩⟩⟩

lemma countable_iff_nonempty_embedding : countable α ↔ nonempty (α ↪ ℕ) :=
⟨λ h, h.1, λ h, ⟨h⟩⟩

lemma nonempty_embedding_nat (α) [countable α] : nonempty (α ↪ ℕ) := ‹countable α›.1

protected lemma function.injective.countable [countable β] {f : α → β} (hf : injective f) :
  countable α :=
let ⟨e⟩ := nonempty_embedding_nat β in ⟨⟨embedding.trans ⟨f, hf⟩ e⟩⟩

protected lemma function.embedding.countable [countable β] (f : α ↪ β) : countable α :=
f.injective.countable

protected lemma function.surjective.countable [countable α] {f : α → β} (hf : surjective f) :
  countable β :=
(injective_surj_inv hf).countable

lemma countable_iff_exists_surjective [nonempty α] : countable α ↔ ∃ f : ℕ → α, surjective f :=
⟨λ ⟨⟨f⟩⟩, ⟨inv_fun f, inv_fun_surjective f.injective⟩, λ ⟨f, hf⟩, hf.countable⟩

protected lemma equiv.countable [countable β] (e : α ≃ β) : countable α := e.injective.countable

lemma equiv.countable_iff (e : α ≃ β) : countable α ↔ countable β :=
⟨λ h, @equiv.countable _ _ h e.symm, λ h, @equiv.countable _ _ h e⟩

instance {β : Type v} [countable β] : countable (ulift.{u} β) :=
equiv.ulift.injective.countable

/-!
### Operations on and `Sort*`s
-/

instance [countable α] : countable (plift α) := equiv.plift.injective.countable

@[priority 100]
instance subsingleton.to_countable [subsingleton α] : countable α :=
⟨⟨⟨λ _, 0, λ x y h, subsingleton.elim x y⟩⟩⟩

instance : countable punit.{u} := subsingleton.to_countable

instance Prop.countable' (p : Prop) : countable p := subsingleton.to_countable

instance bool.countable : countable bool :=
⟨⟨⟨λ b, cond b 0 1, bool.injective_iff.2 nat.one_ne_zero⟩⟩⟩

instance : countable Prop := equiv.Prop_equiv_bool.countable

@[priority 500]
instance [countable α] {p : α → Prop} : countable {x // p x} := subtype.val_injective.countable

@[priority 500]
instance set_coe.countable {α} [countable α] (s : set α) : countable s := subtype.countable

instance (n : ℕ) : countable (fin n) := subtype.countable

instance [countable α] [countable β] : countable (psum α β) :=
begin
  rcases nonempty_embedding_nat α with ⟨ea⟩,
  rcases nonempty_embedding_nat β with ⟨eb⟩,
  refine ⟨⟨⟨λ x, psum.rec_on x (bit0 ∘ ea) (bit1 ∘ eb), _⟩⟩⟩,
  rintro (a|a) (b|b) h; simp only [embedding.apply_eq_iff_eq, nat.bit0_eq_bit0, nat.bit0_ne_bit1,
    nat.bit1_ne_bit0, nat.bit1_eq_bit1] at h,
  exacts [h ▸ rfl, h.elim, h.elim, h ▸ rfl]
end

instance [countable α] {r : α → α → Prop} : countable (quot r) := (surjective_quot_mk r).countable
instance [countable α] {s : setoid α} : countable (quotient s) := quot.countable

end sort

/-!
### Operations on `Type*`s
-/

variables {α : Type u} {β : Type v}

instance [countable α] [countable β] : countable (α ⊕ β) :=
(equiv.psum_equiv_sum α β).symm.countable

instance [countable α] : countable (option α) :=
(equiv.option_equiv_sum_punit α).countable
