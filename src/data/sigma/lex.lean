/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.sigma.basic
import order.rel_classes

/-!
# Lexicographic order on a sigma type

This defines the lexicographical order of two arbitrary relations on a sigma type and proves some
lemmas about `psigma.lex`, which is defined in core Lean.

Given a relation in the index type and a relation on each summand, the lexicographical order on the
sigma type relates `a` and `b` if their summands are related or they are in the same summand and
related by the summand's relation.

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.list.lex`: Lexicographic order on lists.
* `data.sigma.order`: Lexicographic order on `Σ i, α i` per say.
* `data.psigma.order`: Lexicographic order on `Σ' i, α i`.
* `order.lexicographic`: Lexicographic order on `α × β`. Can be thought of as the special case of
  `sigma.lex` where all summands are the same
-/

namespace sigma
variables {ι : Type*} {α : ι → Type*} {r r₁ r₂ : ι → ι → Prop} {s s₁ s₂ : Π i, α i → α i → Prop}
  {a b : Σ i, α i}

/-- The lexicographical order on a sigma type. It takes in a relation on the index type and a
relation for each summand. `a` is related to `b` iff their summands are related or they are in the
same summand and are related through the summand's relation. -/
inductive lex (r : ι → ι → Prop) (s : Π i, α i → α i → Prop) : Π a b : Σ i, α i, Prop
| left {i j : ι} (a : α i) (b : α j) : r i j → lex ⟨i, a⟩ ⟨j, b⟩
| right {i : ι} (a b : α i)          : s i a b → lex ⟨i, a⟩ ⟨i, b⟩

lemma lex_iff : lex r s a b ↔ r a.1 b.1 ∨ ∃ h : a.1 = b.1, s _ (h.rec a.2) b.2 :=
begin
  split,
  { rintro (⟨i, j, a, b, hij⟩ | ⟨i, a, b, hab⟩),
    { exact or.inl hij },
    { exact or.inr ⟨rfl, hab⟩ } },
  { obtain ⟨i, a⟩ := a,
    obtain ⟨j, b⟩ := b,
    dsimp only,
    rintro (h | ⟨rfl, h⟩),
    { exact lex.left _ _ h },
    { exact lex.right _ _ h } }
end

instance lex.decidable (r : ι → ι → Prop) (s : Π i, α i → α i → Prop) [decidable_eq ι]
  [decidable_rel r] [Π i, decidable_rel (s i)] :
  decidable_rel (lex r s) :=
λ a b, decidable_of_decidable_of_iff infer_instance lex_iff.symm

lemma lex.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σ i, α i}
  (h : lex r₁ s₁ a b) :
  lex r₂ s₂ a b :=
begin
  obtain (⟨i, j, a, b, hij⟩ | ⟨i, a, b, hab⟩) := h,
  { exact lex.left _ _ (hr _ _ hij) },
  { exact lex.right _ _ (hs _ _ _ hab) }
end

lemma lex.mono_left (hr : ∀ a b, r₁ a b → r₂ a b) {a b : Σ i, α i} (h : lex r₁ s a b) :
  lex r₂ s a b :=
h.mono hr $ λ _ _ _, id

lemma lex.mono_right (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σ i, α i} (h : lex r s₁ a b) :
  lex r s₂ a b :=
h.mono (λ _ _, id) hs

instance [Π i, is_refl (α i) (s i)] : is_refl _ (lex r s) := ⟨λ ⟨i, a⟩, lex.right _ _ $ refl _⟩

instance [is_irrefl ι r] [Π i, is_irrefl (α i) (s i)] : is_irrefl _ (lex r s) :=
⟨begin
  rintro _ (⟨i, j, a, b, hi⟩ | ⟨i, a, b, ha⟩),
  { exact irrefl _ hi },
  { exact irrefl _ ha }
end⟩

instance [is_trans ι r] [Π i, is_trans (α i) (s i)] : is_trans _ (lex r s) :=
⟨begin
  rintro _ _ _ (⟨i, j, a, b, hij⟩ | ⟨i, a, b, hab⟩) (⟨_, k, _, c, hk⟩ | ⟨_, _, c, hc⟩),
  { exact lex.left _ _ (trans hij hk) },
  { exact lex.left _ _ hij },
  { exact lex.left _ _ hk },
  { exact lex.right _ _ (trans hab hc) }
end⟩

instance [is_symm ι r] [Π i, is_symm (α i) (s i)] : is_symm _ (lex r s) :=
⟨begin
  rintro _ _ (⟨i, j, a, b, hij⟩ | ⟨i, a, b, hab⟩),
  { exact lex.left _ _ (symm hij) },
  { exact lex.right _ _ (symm hab) }
end⟩

local attribute [instance] is_asymm.is_irrefl

instance [is_asymm ι r] [Π i, is_antisymm (α i) (s i)] : is_antisymm _ (lex r s) :=
⟨begin
  rintro _ _ (⟨i, j, a, b, hij⟩ | ⟨i, a, b, hab⟩) (⟨_, _, _, _, hji⟩ | ⟨_, _, _, hba⟩),
  { exact (asymm hij hji).elim },
  { exact (irrefl _ hij).elim },
  { exact (irrefl _ hji).elim },
  { exact ext rfl (heq_of_eq $ antisymm hab hba) }
end⟩

instance [is_trichotomous ι r] [Π i, is_total (α i) (s i)] : is_total _ (lex r s) :=
⟨begin
  rintro ⟨i, a⟩ ⟨j, b⟩,
  obtain hij | rfl | hji := trichotomous_of r i j,
  { exact or.inl (lex.left _ _ hij) },
  { obtain hab | hba := total_of (s i) a b,
    { exact or.inl (lex.right _ _ hab) },
    { exact or.inr (lex.right _ _ hba) } },
  { exact or.inr (lex.left _ _ hji) }
end⟩

instance [is_trichotomous ι r] [Π i, is_trichotomous (α i) (s i)] : is_trichotomous _ (lex r s) :=
⟨begin
  rintro ⟨i, a⟩ ⟨j, b⟩,
  obtain hij | rfl | hji := trichotomous_of r i j,
  { exact or.inl (lex.left _ _ hij) },
  { obtain hab | rfl | hba := trichotomous_of (s i) a b,
    { exact or.inl (lex.right _ _ hab) },
    { exact or.inr (or.inl rfl) },
    { exact or.inr (or.inr $ lex.right _ _ hba) } },
  { exact or.inr (or.inr $ lex.left _ _ hji) }
end⟩

end sigma

/-! ### `psigma` -/

namespace psigma
variables {ι : Sort*} {α : ι → Sort*} {r r₁ r₂ : ι → ι → Prop} {s s₁ s₂ : Π i, α i → α i → Prop}

lemma lex_iff {a b : Σ' i, α i} : lex r s a b ↔ r a.1 b.1 ∨ ∃ h : a.1 = b.1, s _ (h.rec a.2) b.2 :=
begin
  split,
  { rintro (⟨i, j, a, b, hij⟩ | ⟨i, a, b, hab⟩),
    { exact or.inl hij },
    { exact or.inr ⟨rfl, hab⟩ } },
  { obtain ⟨i, a⟩ := a,
    obtain ⟨j, b⟩ := b,
    dsimp only,
    rintro (h | ⟨rfl, h⟩),
    { exact lex.left _ _ h },
    { exact lex.right _ h } }
end

instance lex.decidable (r : ι → ι → Prop) (s : Π i, α i → α i → Prop) [decidable_eq ι]
  [decidable_rel r] [Π i, decidable_rel (s i)] :
  decidable_rel (lex r s) :=
λ a b, decidable_of_decidable_of_iff infer_instance lex_iff.symm

lemma lex.mono {r₁ r₂ : ι → ι → Prop} {s₁ s₂ : Π i, α i → α i → Prop}
  (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σ' i, α i}
  (h : lex r₁ s₁ a b) :
  lex r₂ s₂ a b :=
begin
  obtain (⟨i, j, a, b, hij⟩ | ⟨i, a, b, hab⟩) := h,
  { exact lex.left _ _ (hr _ _ hij) },
  { exact lex.right _ (hs _ _ _ hab) }
end

lemma lex.mono_left {r₁ r₂ : ι → ι → Prop} {s : Π i, α i → α i → Prop}
  (hr : ∀ a b, r₁ a b → r₂ a b) {a b : Σ' i, α i} (h : lex r₁ s a b) :
  lex r₂ s a b :=
h.mono hr $ λ _ _ _, id

lemma lex.mono_right {r : ι → ι → Prop} {s₁ s₂ : Π i, α i → α i → Prop}
  (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σ' i, α i} (h : lex r s₁ a b) :
  lex r s₂ a b :=
h.mono (λ _ _, id) hs

end psigma
