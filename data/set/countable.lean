/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Countable sets.
-/

import data.encodable data.set.finite data.set.lattice data.set.prod logic.function_inverse
noncomputable theory

open function set encodable

namespace option

@[simp] lemma bind_some {α β : Type*} {a : α} {f : α → option β} : some a >>= f = f a :=
rfl

end option

namespace set

section enumerate
parameters {α : Type*} (sel : set α → option α)

def enumerate : set α → ℕ → option α
| s 0       := sel s
| s (n + 1) := do a ← sel s, enumerate (s - {a}) n

lemma enumerate_eq_none_of_sel {s : set α} (h : sel s = none) : ∀{n}, enumerate s n = none
| 0       := by simp [h, enumerate]; refl
| (n + 1) := by simp [h, enumerate]; refl

lemma enumerate_eq_none : ∀{s n₁ n₂}, enumerate s n₁ = none → n₁ ≤ n₂ → enumerate s n₂ = none
| s 0       m := assume : sel s = none, by simp [enumerate_eq_none_of_sel, this]
| s (n + 1) m := assume h hm,
  begin
    cases hs : sel s,
    { by simp [enumerate_eq_none_of_sel, hs] },
    { cases m,
      case nat.zero {
        have : n + 1 = 0, from nat.eq_zero_of_le_zero hm,
        contradiction },
      case nat.succ m' {
        simp [hs, enumerate] at h ⊢,
        have hm : n ≤ m', from nat.le_of_succ_le_succ hm,
        exact enumerate_eq_none h hm } }
  end

lemma enumerate_mem (h_sel : ∀s a, sel s = some a → a ∈ s) :
  ∀{s n a}, enumerate s n = some a → a ∈ s
| s 0 a     := h_sel s a
| s (n+1) a :=
  begin
    cases h : sel s,
    case option.none { simp [enumerate_eq_none_of_sel, h], contradiction },
    case option.some a' {
      simp [enumerate, h],
      exact assume h' : enumerate _ (s - {a'}) n = some a,
        have a ∈ s - {a'}, from enumerate_mem h',
        this.left }
  end

lemma enumerate_inj {n₁ n₂ : ℕ} {a : α} {s : set α} (h_sel : ∀s a, sel s = some a → a ∈ s) :
  enumerate s n₁ = some a → enumerate s n₂ = some a → n₁ = n₂ :=
have ∀{n m s}, enumerate s n = some a → enumerate s (n + m) = some a → m = 0,
begin
  intros n m, induction n,
  case nat.zero {
    cases m,
    case nat.zero { simp [enumerate] },
    case nat.succ n {
      simp [enumerate] {contextual := tt},
      exact assume s _ h,
        have a ∈ s \ {a}, from enumerate_mem _ h_sel h,
        by simp [mem_diff] at this; assumption } },
  case nat.succ n ih {
    intro s,
    cases h : sel s,
    case option.none { simp [enumerate, h], contradiction },
    case option.some a' {
      simp at ih,
      simp [enumerate, h, nat.add_succ] {contextual := tt},
      exact ih } }
end,
match le_total n₁ n₂ with
| or.inl h := let ⟨m, hm⟩ := nat.le.dest h in hm ▸ assume h₁ h₂, by simp [this h₁ h₂]
| or.inr h := let ⟨m, hm⟩ := nat.le.dest h in hm ▸ assume h₁ h₂, by simp [this h₂ h₁]
end

end enumerate

open classical (hiding some)
local attribute [instance] decidable_inhabited prop_decidable
universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

section encodable

def encodable_of_inj [encodable β] (f : α → β) (hf : injective f) : encodable α :=
let g : β → option α := λb, if h : ∃a, f a = b then some (classical.some h) else none in
encodable_of_left_injection f g $ assume a,
  have h : ∃a', f a' = f a, from ⟨a, rfl⟩,
  have f (classical.some h) = f a, from some_spec h,
  have classical.some h = a, from hf this,
  by simp [g, h, this]

end encodable

/-- Countable sets

A set is countable if there exists a injective functions from the set into the natural numbers.
This is choosen instead of surjective functions, as this would require that α is non empty.
-/
def countable (s : set α) : Prop := ∃f:α → ℕ, ∀x∈s, ∀y∈s, f x = f y → x = y

lemma countable_iff_exists_surjective [ne : inhabited α] {s : set α} :
  countable s ↔ (∃f:ℕ → α, s ⊆ range f) :=
iff.intro
  (assume ⟨f, hf⟩, ⟨inv_fun_on f s, assume a ha, ⟨f a, inv_fun_on_eq' hf ha⟩⟩)
  (assume ⟨f, hf⟩, ⟨inv_fun f, assume x hx y hy h,
    calc x = f (inv_fun f x) : (inv_fun_eq $ hf hx).symm
      ... = f (inv_fun f y) : by rw [h]
      ... = y : inv_fun_eq $ hf hy⟩)

lemma countable.to_encodable {s : set α} (h : countable s) : encodable {a // a ∈ s} :=
let f := classical.some h in
have hf : ∀x∈s, ∀y∈s, f x = f y → x = y, from classical.some_spec h,
let f' : {a // a ∈ s} → ℕ := f ∘ subtype.val in
encodable_of_inj f' $ assume ⟨a, ha⟩ ⟨b, hb⟩ (h : f a = f b), subtype.eq $ hf a ha b hb h

lemma countable_encodable' {s : set α} (e : encodable {a // a∈s}) : countable s :=
⟨λx, if h : x ∈ s then @encode _ e ⟨x, h⟩ else 0, assume x hx y hy h,
  have @encode _ e ⟨x, hx⟩ = @encode _ e ⟨y, hy⟩,
    by simp [hx, hy] at h; assumption,
  have decode {a // a∈s} (@encode _ e ⟨x, hx⟩) = decode {a // a∈s} (@encode _ e ⟨y, hy⟩),
    from congr_arg _ this,
  begin simp [encodek] at this, injection this with h, injection h end⟩

lemma countable_encodable [e : encodable α] {s : set α} : countable s :=
⟨encode, assume x _ y _ eq,
  have decode α (encode x) = decode α (encode y), from congr_arg _ eq,
  by simp [encodek] at this; exact option.some.inj this⟩

lemma countable_empty : countable (∅ : set α) :=
⟨λ_, 0, by simp⟩

lemma countable_singleton {a : α} : countable ({a} : set α) :=
⟨λ_, 0, by simp⟩

lemma countable_subset {s₁ s₂ : set α} (h : s₁ ⊆ s₂) : countable s₂ → countable s₁
| ⟨f, hf⟩ := ⟨f, assume x hx y hy eq, hf x (h hx) y (h hy) eq⟩

lemma countable_image {s : set α} {f : α → β} (hs : countable s) : countable (f '' s) :=
let f' : {a // a ∈ s} → {b // b ∈ f '' s} := λ⟨a, ha⟩, ⟨f a, mem_image_of_mem f ha⟩ in
have hf' : surjective f', from assume ⟨b, a, ha, hab⟩, ⟨⟨a, ha⟩, subtype.eq hab⟩,
countable_encodable' $ @encodable_of_inj _ _ hs.to_encodable (surj_inv hf') (injective_surj_inv hf')

lemma countable_sUnion {s : set (set α)} (hs : countable s) (ht : ∀a∈s, countable a) :
  countable (⋃₀ s) :=
let f := classical.some hs in
let g := λa ha, classical.some (ht a ha) in
_

end set
