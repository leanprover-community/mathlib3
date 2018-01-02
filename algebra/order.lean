/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

universe u
variables {α : Type u}

lemma not_le_of_lt [preorder α] {a b : α} (h : a < b) : ¬ b ≤ a :=
(le_not_le_of_lt h).right

lemma not_lt_of_le [preorder α] {a b : α} (h : a ≤ b) : ¬ b < a
| hab := not_le_of_gt hab h

lemma le_iff_eq_or_lt [partial_order α] {a b : α} : a ≤ b ↔ a = b ∨ a < b :=
le_iff_lt_or_eq.trans or.comm

lemma lt_iff_le_and_ne [partial_order α] {a b : α} : a < b ↔ a ≤ b ∧ a ≠ b :=
⟨λ h, ⟨le_of_lt h, ne_of_lt h⟩, λ ⟨h1, h2⟩, lt_of_le_of_ne h1 h2⟩

lemma eq_or_lt_of_le [partial_order α] {a b : α} (h : a ≤ b) : a = b ∨ a < b :=
(lt_or_eq_of_le h).symm

@[simp] lemma not_lt [linear_order α] {a b : α} : ¬ a < b ↔ b ≤ a := ⟨le_of_not_gt, not_lt_of_ge⟩

lemma le_of_not_lt [linear_order α] {a b : α} : ¬ a < b → b ≤ a := not_lt.1

@[simp] lemma not_le [linear_order α] {a b : α} : ¬ a ≤ b ↔ b < a := (lt_iff_not_ge b a).symm

lemma lt_or_le [linear_order α] : ∀ a b : α, a < b ∨ b ≤ a := lt_or_ge
lemma le_or_lt [linear_order α] : ∀ a b : α, a ≤ b ∨ a > b := le_or_gt

lemma not_lt_iff_eq_or_lt [linear_order α] {a b : α} : ¬ a < b ↔ a = b ∨ b < a :=
not_lt.trans $ le_iff_eq_or_lt.trans $ or_congr eq_comm iff.rfl

lemma lt_iff_lt_of_strict_mono {β} [linear_order α] [preorder β]
  (f : α → β) (H : ∀ a b, a < b → f a < f b) {a b} :
  f a < f b ↔ a < b :=
⟨λ h, ((lt_trichotomy b a)
  .resolve_left $ λ h', lt_asymm h $ H _ _ h')
  .resolve_left $ λ e, ne_of_gt h $ congr_arg _ e, H _ _⟩

lemma injective_of_strict_mono {β} [linear_order α] [preorder β]
  (f : α → β) (H : ∀ a b, a < b → f a < f b) : function.injective f
| a b e := ((lt_trichotomy a b)
  .resolve_left $ λ h, ne_of_lt (H _ _ h) e)
  .resolve_right $ λ h, ne_of_gt (H _ _ h) e

lemma le_imp_le_iff_lt_imp_lt {β} [linear_order α] [linear_order β] {a b : α} {c d : β} :
  (a ≤ b → c ≤ d) ↔ (d < c → b < a) :=
⟨λ H h, lt_of_not_ge $ λ h', not_lt_of_ge (H h') h,
λ H h, le_of_not_gt $ λ h', not_le_of_gt (H h') h⟩

lemma le_iff_le_iff_lt_iff_lt {β} [linear_order α] [linear_order β] {a b : α} {c d : β} :
  (a ≤ b ↔ c ≤ d) ↔ (b < a ↔ d < c) :=
⟨λ H, not_le.symm.trans $ iff.trans (not_congr H) $ not_le,
λ H, not_lt.symm.trans $ iff.trans (not_congr H) $ not_lt⟩

lemma eq_of_forall_le_iff [partial_order α] {a b : α}
  (H : ∀ c, c ≤ a ↔ c ≤ b) : a = b :=
le_antisymm ((H _).1 (le_refl _)) ((H _).2 (le_refl _))

lemma le_of_forall_le [preorder α] {a b : α}
  (H : ∀ c, c ≤ a → c ≤ b) : a ≤ b :=
H _ (le_refl _)

lemma le_of_forall_lt [linear_order α] {a b : α}
  (H : ∀ c, c < a → c < b) : a ≤ b :=
le_of_not_lt $ λ h, lt_irrefl _ (H _ h)

lemma eq_of_forall_ge_iff [partial_order α] {a b : α}
  (H : ∀ c, a ≤ c ↔ b ≤ c) : a = b :=
le_antisymm ((H _).2 (le_refl _)) ((H _).1 (le_refl _))

namespace ordering

@[simp] def compares [has_lt α] : ordering → α → α → Prop
| lt a b := a < b
| eq a b := a = b
| gt a b := a > b

theorem compares.eq_lt [preorder α] :
  ∀ {o} {a b : α}, compares o a b → (o = lt ↔ a < b)
| lt a b h := ⟨λ _, h, λ _, rfl⟩
| eq a b h := ⟨λ h, by injection h, λ h', (ne_of_lt h' h).elim⟩
| gt a b h := ⟨λ h, by injection h, λ h', (lt_asymm h h').elim⟩

theorem compares.eq_eq [preorder α] :
  ∀ {o} {a b : α}, compares o a b → (o = eq ↔ a = b)
| lt a b h := ⟨λ h, by injection h, λ h', (ne_of_lt h h').elim⟩
| eq a b h := ⟨λ _, h, λ _, rfl⟩
| gt a b h := ⟨λ h, by injection h, λ h', (ne_of_gt h h').elim⟩

theorem compares.eq_gt [preorder α] :
  ∀ {o} {a b : α}, compares o a b → (o = gt ↔ a > b)
| lt a b h := ⟨λ h, by injection h, λ h', (lt_asymm h h').elim⟩
| eq a b h := ⟨λ h, by injection h, λ h', (ne_of_gt h' h).elim⟩
| gt a b h := ⟨λ _, h, λ _, rfl⟩

theorem compares.inj [preorder α] {o₁} :
  ∀ {o₂} {a b : α}, compares o₁ a b → compares o₂ a b → o₁ = o₂
| lt a b h₁ h₂ := h₁.eq_lt.2 h₂
| eq a b h₁ h₂ := h₁.eq_eq.2 h₂
| gt a b h₁ h₂ := h₁.eq_gt.2 h₂

theorem compares_of_strict_mono {β} [linear_order α] [preorder β]
  (f : α → β) (H : ∀ a b, a < b → f a < f b) {a b} : ∀ {o}, compares o (f a) (f b) ↔ compares o a b
| lt := lt_iff_lt_of_strict_mono f H
| eq := ⟨λ h, injective_of_strict_mono _ H h, congr_arg _⟩
| gt := lt_iff_lt_of_strict_mono f H

end ordering
