/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/

import tactic.ext
import tactic.solve_by_elim
import data.stream.basic
import data.finset.basic
import tactic.rcases

section ext_trace_test
setup_tactic_parser

namespace tactic
namespace interactive

meta def ext_trace_test (patts : parse rcases_patt_parse_hi*)
  (fuel : parse (tk ":" *> small_nat)?) (tgt_trace : string) : tactic unit := do
  ⟨_, σ⟩ ← state_t.run (ext_core {}) ⟨patts, [], fuel⟩,
  guard $ ", ".intercalate σ.trace_msg = tgt_trace

end interactive
end tactic

end ext_trace_test

example (α β γ : Type) (f g : α × β → γ) (H : ∀ a : α, ∀ b : β, f (a,b) = g (a,b)) : f = g :=
begin
  ext_trace_test ⟨a,b⟩ "apply funext, rintro ⟨a, b⟩", apply H
end

example : subsingleton unit :=
begin
  split, intros, ext
end

example (x y : ℕ) : true :=
begin
  have : x = y,
  { ext <|> admit },
  have : x = y,
  { ext i <|> admit },
  have : x = y,
  { ext : 1 <|> admit },
  trivial
end

example (X Y : ℕ × ℕ)  (h : X.1 = Y.1) (h : X.2 = Y.2) : X = Y :=
begin
  ext; assumption
end

example (X Y : (ℕ → ℕ) × ℕ)  (h : ∀ i, X.1 i = Y.1 i) (h : X.2 = Y.2) : X = Y :=
begin
  ext x; solve_by_elim,
end

example (X Y : ℕ → ℕ × ℕ)  (h : ∀ i, X i = Y i) : true :=
begin
  have : X = Y,
  { ext i : 1,
    guard_target X i = Y i,
    admit },
  have : X = Y,
  { ext i,
    guard_target (X i).fst = (Y i).fst, admit,
    guard_target (X i).snd = (Y i).snd, admit, },
  have : X = Y,
  { ext : 1,
    guard_target X x = Y x,
    admit },
  trivial,
end

example (s₀ s₁ : set ℕ) (h : s₁ = s₀) : s₀ = s₁ :=
by { ext1, guard_target x ∈ s₀ ↔ x ∈ s₁, simp * }

example (s₀ s₁ : stream ℕ) (h : s₁ = s₀) : s₀ = s₁ :=
by { ext1, guard_target s₀.nth n = s₁.nth n, simp * }

example (s₀ s₁ : ℤ → set (ℕ × ℕ))
        (h : ∀ i a b, (a,b) ∈ s₀ i ↔ (a,b) ∈ s₁ i) : s₀ = s₁ :=
begin
  ext i ⟨a,b⟩,
  apply h
end

example (s₀ s₁ : ℤ → set (ℕ × ℕ))
        (h : ∀ i a b, (a,b) ∈ s₀ i ↔ (a,b) ∈ s₁ i) : s₀ = s₁ :=
begin
  ext_trace_test i ⟨a,b⟩ "apply funext, rintro i, apply set.ext, rintro ⟨a, b⟩",
  apply h
end

/- extensionality -/

example : true :=
begin
  have : ∀ (s₀ s₁ : set ℤ), s₀ = s₁,
  { intros, ext1,
    guard_target x ∈ s₀ ↔ x ∈ s₁,
    admit },
  have : ∀ (s₀ s₁ : finset ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target a ∈ s₀ ↔ a ∈ s₁,
    admit },
  have : ∀ (s₀ s₁ : multiset ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target multiset.count a s₀ = multiset.count a s₁,
    admit },
  have : ∀ (s₀ s₁ : list ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target list.nth s₀ n = list.nth s₁ n,
    admit },
  have : ∀ (s₀ s₁ : stream ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target stream.nth n s₀ = stream.nth n s₁,
    admit },
  have : ∀ n (s₀ s₁ : array n ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target array.read s₀ i = array.read s₁ i,
    admit },
  trivial
end

structure dependent_fields :=
(a : bool)
(v : if a then ℕ else ℤ)

@[ext] lemma df.ext (s t : dependent_fields) (h : s.a = t.a)
 (w : (@eq.rec _ s.a (λ b, if b then ℕ else ℤ) s.v t.a h) = t.v) : s = t :=
begin
  cases s, cases t,
  dsimp at *,
  congr,
  exact h,
  subst h,
  simp,
  simp at w,
  exact w,
end

example (s : dependent_fields) : s = s :=
begin
  tactic.ext1 [] {tactic.apply_cfg . new_goals := tactic.new_goals.all},
  guard_target s.a = s.a,
  refl,
  refl,
end

@[ext] structure dumb (V : Type) := (val : V)
