/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Enumerate elements of a set with a select function.
-/
import data.set.lattice
import tactic.wlog
noncomputable theory

open function set

namespace set

section enumerate
parameters {α : Type*} (sel : set α → option α)

def enumerate : set α → ℕ → option α
| s 0       := sel s
| s (n + 1) := do a ← sel s, enumerate (s \ {a}) n

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
      case nat.succ : m' {
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
    case none { simp [enumerate_eq_none_of_sel, h] },
    case some : a' {
      simp [enumerate, h],
      exact assume h' : enumerate _ (s \ {a'}) n = some a,
        have a ∈ s \ {a'}, from enumerate_mem h',
        this.left }
  end

lemma enumerate_inj {n₁ n₂ : ℕ} {a : α} {s : set α} (h_sel : ∀s a, sel s = some a → a ∈ s)
  (h₁ : enumerate s n₁ = some a) (h₂ : enumerate s n₂ = some a) : n₁ = n₂ :=
begin
  wlog hn : n₁ ≤ n₂,
  { rcases nat.le.dest hn with ⟨m, rfl⟩, clear hn,
    induction n₁ generalizing s,
    case nat.zero {
      cases m,
      case nat.zero { refl },
      case nat.succ : m {
        have : enumerate sel (s \ {a}) m = some a, { simp [enumerate, *] at * },
        have : a ∈ s \ {a}, from enumerate_mem _ h_sel this,
        by simpa } },
    case nat.succ { cases h : sel s; simp [enumerate, nat.add_succ, add_comm, *] at *; tauto } }
end

end enumerate

end set
