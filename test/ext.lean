/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/

import tactic.basic
import tactic.ext
import tactic.solve_by_elim
import data.set.basic data.stream.basic

@[extensionality] lemma unit.ext (x y : unit) : x = y :=
begin
  cases x, cases y, refl
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

def my_foo {α} (x : semigroup α) (y : group α) : true := trivial

example {α : Type} : true :=
begin
  have : true,
  { refine_struct (@my_foo α { .. } { .. } ),
      -- 9 goals
    guard_tags _field mul semigroup, admit,
      -- case semigroup, mul
      -- α : Type
      -- ⊢ α → α → α

    guard_tags _field mul_assoc semigroup, admit,
      -- case semigroup, mul_assoc
      -- α : Type
      -- ⊢ ∀ (a b c : α), a * b * c = a * (b * c)

    guard_tags _field mul group, admit,
      -- case group, mul
      -- α : Type
      -- ⊢ α → α → α

    guard_tags _field mul_assoc group, admit,
      -- case group, mul_assoc
      -- α : Type
      -- ⊢ ∀ (a b c : α), a * b * c = a * (b * c)

    guard_tags _field one group, admit,
      -- case group, one
      -- α : Type
      -- ⊢ α

    guard_tags _field one_mul group, admit,
      -- case group, one_mul
      -- α : Type
      -- ⊢ ∀ (a : α), 1 * a = a

    guard_tags _field mul_one group, admit,
      -- case group, mul_one
      -- α : Type
      -- ⊢ ∀ (a : α), a * 1 = a

    guard_tags _field inv group, admit,
      -- case group, inv
      -- α : Type
      -- ⊢ α → α

    guard_tags _field mul_left_inv group, admit,
      -- case group, mul_left_inv
      -- α : Type
      -- ⊢ ∀ (a : α), a⁻¹ * a = 1
  },
  trivial
end

def my_bar {α} (x : semigroup α) (y : group α) (i j : α) : α := i

example {α : Type} : true :=
begin
  have : monoid α,
  { refine_struct { mul := my_bar { .. } { .. } },
    guard_tags _field mul semigroup, admit,
    guard_tags _field mul_assoc semigroup, admit,
    guard_tags _field mul group, admit,
    guard_tags _field mul_assoc group, admit,
    guard_tags _field one group, admit,
    guard_tags _field one_mul group, admit,
    guard_tags _field mul_one group, admit,
    guard_tags _field inv group, admit,
    guard_tags _field mul_left_inv group, admit,
    guard_tags _field mul_assoc monoid, admit,
    guard_tags _field one monoid, admit,
    guard_tags _field one_mul monoid, admit,
    guard_tags _field mul_one monoid, admit, },
  trivial
end

structure dependent_fields :=
(a : bool)
(v : if a then ℕ else ℤ)

@[extensionality] lemma df.ext (s t : dependent_fields) (h : s.a = t.a)
 (w : (@eq.rec _ s.a (λ b, if b then ℕ else ℤ) s.v t.a h) = t.v): s = t :=
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
