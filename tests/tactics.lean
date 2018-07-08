/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic data.set.lattice

section solve_by_elim
example {a b : Prop} (h₀ : a → b) (h₁ : a) : b :=
begin
  apply_assumption,
  apply_assumption,
end

example {a b : Prop} (h₀ : a → b) (h₁ : a) : b :=
by solve_by_elim

example {α : Type} {a b : α → Prop} (h₀ : ∀ x : α, b x = a x) (y : α) : a y = b y :=
by solve_by_elim

example {α : Type} {p : α → Prop} (h₀ : ∀ x, p x) (y : α) : p y :=
begin
  apply_assumption,
end
end solve_by_elim

section tauto₀
variables p q r : Prop
variables h : p ∧ q ∨ p ∧ r
include h
example : p ∧ p :=
by tauto

end tauto₀

section tauto₁
variables α : Type
variables p q r : α → Prop
variables h : (∃ x, p x ∧ q x) ∨ (∃ x, p x ∧ r x)
include h
example : ∃ x, p x :=
by tauto

end tauto₁

section tauto₂
variables α : Type
variables x : α
variables p q r : α → Prop
variables h₀ : (∀ x, p x → q x → r x) ∨ r x
variables h₁ : p x
variables h₂ : q x

include h₀ h₁ h₂
example : ∃ x, r x :=
by tauto

end tauto₂

section tauto₃


-- 260ms -- 82ms -- 214ms -- 38ms -- 30ms -- 19ms -- 14ms -- 10ms -- 6ms
example (p : Prop) : p ∧ true ↔ p := by tauto
-- 380ms -- 127ms -- 214ms -- 54ms -- 60ms -- 24ms -- 21ms -- 15ms -- 10ms
example (p : Prop) : p ∨ false ↔ p := by tauto
-- 1.66s -- 455ms -- 204ms -- 78ms -- 100ms -- 59ms -- 24ms -- 19ms -- 14ms
example (p q r : Prop) [decidable p] [decidable r] : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r) := by tauto
-- 1.67s -- 485ms -- 135ms -- 90ms -- 76ms -- 56ms -- 11ms -- 14ms -- 10ms
example (p q r : Prop) [decidable q] [decidable r] : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r) := by tauto
-- 1.63s -- 547ms -- 138ms -- 76ms -- 80ms -- 62ms -- 12ms -- 13ms -- 13ms
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : ¬ p) : q := by tauto
-- 1.55s -- 419ms -- 248ms -- 118ms -- 85ms -- 87ms -- 30ms -- 16ms -- 28ms
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : p) : ¬ q := by tauto
-- 1.62s -- 441ms -- 171ms -- 103ms -- 119ms -- 66ms -- 17ms -- 33ms -- 19ms
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : q) : ¬ p := by tauto
-- 2.41s -- 597ms -- 230ms -- 129ms -- 125ms -- 89ms -- 41ms -- 32ms -- 37ms
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : ¬ q) : p := by tauto
-- 5.38s -- 1.56s -- 1.18s -- 639ms -- 524ms -- 318ms -- 70ms -- 68ms -- 49ms
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : ¬ q) (h'' : ¬ p) : false := by tauto
-- 5.38s -- 1.61s -- 643ms -- 314ms -- 505ms -- 243ms -- 136ms -- 132ms -- 98ms
example (p q r : Prop) [decidable q] [decidable p] (h : p ↔ q) (h' : r ↔ q) (h'' : ¬ r) : ¬ p := by tauto
-- 3.7s -- 965ms -- 613ms -- 661ms -- 298ms -- 347ms -- 87ms -- 69ms -- 66ms
example (p q r : Prop) [decidable q] [decidable p] (h : p ↔ q) (h' : r ↔ q) : p ↔ r :=
by tauto
-- 7.27s -- 1.9s -- 1.32s -- 332ms -- 305ms -- 274ms -- 177ms -- 149ms -- 127ms
example (p q r : Prop) [decidable p] [decidable q] [decidable r] (h : ¬ p = q) (h' : r = q) : p ↔ ¬ r := by tauto

section modulo_symmetry
variables {p q r : Prop} {α : Type} {x y : α} [decidable_eq α]
variables [decidable p] [decidable q] [decidable r]
variables (h : x = y)
variables (h'' : (p ∧ q ↔ q ∨ r) ↔ (r ∧ p ↔ r ∨ q))
include h
include h''
-- 4.25s -- 74ms -- 5ms   -- 4ms  -- 10ms
example (h' : ¬ y = x) : p ∧ q := by tauto
-- 4.25s -- 74ms -- 36ms  -- 41ms -- 297ms
example (h' : p ∧ ¬ y = x) : p ∧ q := by tauto
-- 4.25s -- 63ms -- 3.9ms -- 2ms  -- 2ms
example : y = x := by tauto
-- 19ms -- 52ms -- 1ms    -- 1ms  -- 2ms
example (h' : ¬ x = y) : p ∧ q := by tauto
-- 19ms -- 43ms -- 2ms    -- 3ms  -- 3ms
example : x = y := by tauto

end modulo_symmetry

end tauto₃

section wlog

example {x y : ℕ} (a : x = 1) : true :=
begin
  suffices : false, trivial,
  wlog h : x = y,
  { guard_target x = y ∨ y = x,
    admit },
  { guard_hyp h := x = y,
    guard_hyp a := x = 1,
    admit }
end

example {x y : ℕ} : true :=
begin
  suffices : false, trivial,
  wlog h : x ≤ y,
  { guard_hyp h := x ≤ y,
    guard_target false,
    admit }
end

example {x y z : ℕ} : true :=
begin
  suffices : false, trivial,
  wlog h : x ≤ y + z,
  { guard_target x ≤ y + z ∨ x ≤ z + y,
    admit },
  { guard_hyp h := x ≤ y + z,
    guard_target false,
    admit }
end

example {x y z : ℕ} : true :=
begin
  suffices : false, trivial,
  wlog : x ≤ y + z using x y,
  { guard_target x ≤ y + z ∨ y ≤ x + z,
    admit },
  { guard_hyp case := x ≤ y + z,
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
  { guard_hyp h  := x ∈ S₀ ∪ S₁,
    guard_hyp h' := x ∈ S₀,
    admit }
end

example {n m i : ℕ} {p : ℕ → ℕ → ℕ → Prop} : true :=
begin
  suffices : false, trivial,
  wlog : p n m i using [n m i, n i m, i n m],
  { guard_target p n m i ∨ p n i m ∨ p i n m,
    admit },
  { guard_hyp case := p n m i,
    admit }
end

example {n m i : ℕ} {p : ℕ → Prop} : true :=
begin
  suffices : false, trivial,
  wlog : p n using [n m i, m n i, i n m],
  { guard_target p n ∨ p m ∨ p i,
    admit },
  { guard_hyp case := p n,
    admit }
end

example {n m i : ℕ} {p : ℕ → ℕ → Prop} {q : ℕ → ℕ → ℕ → Prop} : true :=
begin
  suffices : q n m i, trivial,
  have h : p n i ∨ p i m ∨ p m i, from sorry,
  wlog : p n i := h using n m i,
  { guard_hyp h := p n i,
    guard_target q n m i,
    admit },
  { guard_hyp h := p i m,
    guard_hyp this := q i m n,
    guard_target q n m i,
    admit },
  { guard_hyp h := p m i,
    guard_hyp this := q m i n,
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

example (m n p q : nat) (h : m + n = p) : true :=
begin
  have : m + n = q,
  { generalize_hyp h' : m + n = x at h,
    guard_hyp h' := m + n = x,
    guard_hyp h := x = p,
    guard_target m + n = q,
    admit },
  have : m + n = q,
  { generalize_hyp h' : m + n = x at h ⊢,
    guard_hyp h' := m + n = x,
    guard_hyp h := x = p,
    guard_target x = q,
    admit },
  trivial
end

example (α : Sort*) (L₁ L₂ L₃ : list α)
  (H : L₁ ++ L₂ = L₃) : true :=
begin
  have : L₁ ++ L₂ = L₂,
  { generalize_hyp h : L₁ ++ L₂ = L at H,
    induction L with hd tl ih,
    case list.nil
    { tactic.cleanup,
      change list.nil = L₃ at H,
      admit },
    case list.cons
    { change hd :: tl = L₃ at H,
      admit } },
  trivial
end

section convert
open set

variables {α β : Type}
local attribute [simp]
private lemma singleton_inter_singleton_eq_empty {x y : α} :
  ({x} ∩ {y} = (∅ : set α)) ↔ x ≠ y :=
by simp [singleton_inter_eq_empty]

example {f : β → α} {x y : α} (h : x ≠ y) : f ⁻¹' {x} ∩ f ⁻¹' {y} = ∅ :=
begin
  have : {x} ∩ {y} = (∅ : set α) := by simpa using h,
  convert preimage_empty,
  rw [←preimage_inter,this],
end

end convert

section rcases

universe u
variables {α β γ : Type u}

example (x : α × β × γ) : true :=
begin
  rcases x with ⟨a, b, c⟩,
  { guard_hyp a := α,
    guard_hyp b := β,
    guard_hyp c := γ,
    trivial }
end

example (x : α × β × γ) : true :=
begin
  rcases x with ⟨a, ⟨b, c⟩⟩,
  { guard_hyp a := α,
    guard_hyp b := β,
    guard_hyp c := γ,
    trivial }
end

example (x : (α × β) × γ) : true :=
begin
  rcases x with ⟨⟨a, b⟩, c⟩,
  { guard_hyp a := α,
    guard_hyp b := β,
    guard_hyp c := γ,
    trivial }
end

example (x : inhabited α × option β ⊕ γ) : true :=
begin
  rcases x with ⟨⟨a⟩, _ | b⟩ | c,
  { guard_hyp a := α, trivial },
  { guard_hyp a := α, guard_hyp b := β, trivial },
  { guard_hyp c := γ, trivial }
end

example (x y : ℕ) (h : x = y) : true :=
begin
  rcases x with _|⟨⟩|z,
  { guard_hyp h := nat.zero = y, trivial },
  { guard_hyp h := nat.succ nat.zero = y, trivial },
  { guard_hyp z := ℕ,
    guard_hyp h := z.succ.succ = y, trivial },
end

-- from equiv.sum_empty
example (s : α ⊕ empty) : true :=
begin
  rcases s with _ | ⟨⟨⟩⟩,
  { guard_hyp s := α, trivial }
end

end rcases

section ext

example (x y : ℕ) : true :=
begin
  have : x = y,
  { ext <|> admit },
  have : x = y,
  { ext i <|> admit },
  have : x = y,
  { ext 1 <|> admit },
  trivial
end

example (X Y : ℕ × ℕ)  (h : X.1 = Y.1) (h : X.2 = Y.2) : X = Y :=
begin
  ext ; assumption
end

example (X Y : (ℕ → ℕ) × ℕ)  (h : ∀ i, X.1 i = Y.1 i) (h : X.2 = Y.2) : X = Y :=
begin
  ext x ; solve_by_elim,
end

example (X Y : ℕ → ℕ × ℕ)  (h : ∀ i, X i = Y i) : true :=
begin
  have : X = Y,
  { ext 1 with i,
    guard_target X i = Y i,
    admit },
  have : X = Y,
  { ext i,
    guard_target (X i).fst = (Y i).fst, admit,
    guard_target (X i).snd = (Y i).snd, admit, },
  have : X = Y,
  { ext 1,
    guard_target X x = Y x,
    admit },
  trivial,
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

end ext
