/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Enumerate elements of a set with a select function.
-/

import data.encodable data.set.finite data.set.lattice data.set.prod logic.function_inverse
noncomputable theory

open function set encodable

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
    case none { simp [enumerate_eq_none_of_sel, h], contradiction },
    case some a' {
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
    case nat.succ m {
      simp [enumerate] {contextual := tt},
      exact assume s _ h,
        have a ∈ s \ {a}, from enumerate_mem _ h_sel h,
        by simpa } },
  case nat.succ n ih {
    intro s,
    cases h : sel s,
    case none { simp [enumerate, h], contradiction },
    case some a' {
      simp [enumerate, h, nat.add_succ] {contextual := tt},
      simpa using ih } }
end,
match le_total n₁ n₂ with
| or.inl h := let ⟨m, hm⟩ := nat.le.dest h in hm ▸ assume h₁ h₂, by simp [this h₁ h₂]
| or.inr h := let ⟨m, hm⟩ := nat.le.dest h in hm ▸ assume h₁ h₂, by simp [this h₂ h₁]
end

end enumerate

end set
