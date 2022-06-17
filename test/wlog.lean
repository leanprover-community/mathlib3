/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.wlog

section wlog

example {x y : ℕ} (a : x = 1) : true :=
begin
  suffices : false, trivial,
  wlog h : x = y,
  { guard_target x = y ∨ y = x,
    admit },
  { guard_hyp h : x = y,
    guard_hyp a : x = 1,
    admit }
end

example {x y : ℕ} : true :=
begin
  suffices : false, trivial,
  wlog h : x ≤ y,
  { guard_hyp h : x ≤ y,
    guard_target false,
    admit }
end

example {x y z : ℕ} : true :=
begin
  suffices : false, trivial,
  wlog : x ≤ y + z using x y,
  { guard_target x ≤ y + z ∨ y ≤ x + z,
    admit },
  { guard_hyp case : x ≤ y + z,
    guard_target false,
    admit },
end

example {x : ℕ} (S₀ S₁ : set ℕ) (P : ℕ → Prop)
  (h : x ∈ S₀ ∪ S₁) : true :=
begin
  suffices : false, trivial,
  wlog h' : x ∈ S₀ using S₀ S₁,
  { guard_target x ∈ S₀ ∨ x ∈ S₁,
    admit },
  { guard_hyp h  : x ∈ S₀ ∪ S₁,
    guard_hyp h' : x ∈ S₀,
    admit }
end

example {n m i : ℕ} {p : ℕ → ℕ → ℕ → Prop} : true :=
begin
  suffices : false, trivial,
  wlog : p n m i using [n m i, n i m, i n m],
  { guard_target p n m i ∨ p n i m ∨ p i n m,
    admit },
  { guard_hyp case : p n m i,
    admit }
end

example {n m i : ℕ} {p : ℕ → Prop} : true :=
begin
  suffices : false, trivial,
  wlog : p n using [n m i, m n i, i n m],
  { guard_target p n ∨ p m ∨ p i,
    admit },
  { guard_hyp case : p n,
    admit }
end

example {n m i : ℕ} {p : ℕ → ℕ → Prop} {q : ℕ → ℕ → ℕ → Prop} : true :=
begin
  suffices : q n m i, trivial,
  have h : p n i ∨ p i m ∨ p m i, from sorry,
  wlog : p n i := h using n m i,
  { guard_hyp h : p n i,
    guard_target q n m i,
    admit },
  { guard_hyp h : p i m,
    guard_hyp this : q i m n,
    guard_target q n m i,
    admit },
  { guard_hyp h : p m i,
    guard_hyp this : q m i n,
    guard_target q n m i,
    admit },
end

example (X : Type) (A B C : set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext x,
  split,
  { intro hyp,
    cases hyp,
    wlog x_in : x ∈ B using B C,
    { assumption },
    { exact or.inl ⟨hyp_left, x_in⟩ } },
  { intro hyp,
    wlog x_in : x ∈ A ∩ B using B C,
    { assumption },
    { exact ⟨x_in.left, or.inl x_in.right⟩ } }
end

example (X : Type) (A B C : set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext x,
  split,
  { intro hyp,
    wlog x_in : x ∈ B := hyp.2 using B C,
    { exact or.inl ⟨hyp.1, x_in⟩ } },
  { intro hyp,
    wlog x_in : x ∈ A ∩ B := hyp using B C,
    { exact ⟨x_in.left, or.inl x_in.right⟩ } }
end

example (X : Type) (A B C : set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext x,
  split,
  { intro hyp,
    cases hyp,
    wlog x_in : x ∈ B := hyp_right using B C,
    { exact or.inl ⟨hyp_left, x_in⟩ }, },
  { intro hyp,
    wlog x_in : x ∈ A ∩ B := hyp using B C,
    { exact ⟨x_in.left, or.inl x_in.right⟩ } }
end

end wlog
