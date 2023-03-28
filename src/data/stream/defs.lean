/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

/-!
# Definition of `stream` and functions on streams

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A stream `stream α` is an infinite sequence of elements of `α`. One can also think about it as an
infinite list. In this file we define `stream` and some functions that take and/or return streams.
-/

universes u v w

/-- A stream `stream α` is an infinite sequence of elements of `α`. -/
def stream (α : Type u) := nat → α

open nat

namespace stream
variables {α : Type u} {β : Type v} {δ : Type w}

/-- Prepend an element to a stream. -/
def cons (a : α) (s : stream α) : stream α
| 0       := a
| (n + 1) := s n

notation (name := stream.cons) h :: t := cons h t

/-- Head of a stream: `stream.head s = stream.nth 0 s`. -/
def head (s : stream α) : α :=
s 0

/-- Tail of a stream: `stream.tail (h :: t) = t`. -/
def tail (s : stream α) : stream α :=
λ i, s (i+1)

/-- Drop first `n` elements of a stream. -/
def drop (n : nat) (s : stream α) : stream α :=
λ i, s (i+n)

/-- `n`-th element of a stream. -/
def nth (s : stream α) (n : ℕ) : α :=
s n

/-- Proposition saying that all elements of a stream satisfy a predicate. -/
def all (p : α → Prop) (s : stream α) := ∀ n, p (nth s n)

/-- Proposition saying that at least one element of a stream satisfies a predicate. -/
def any (p : α → Prop) (s : stream α) := ∃ n, p (nth s n)

/-- `a ∈ s` means that `a = stream.nth n s` for some `n`. -/
instance : has_mem α (stream α) :=
⟨λ a s, any (λ b, a = b) s⟩

/-- Apply a function `f` to all elements of a stream `s`. -/
def map (f : α → β) (s : stream α) : stream β :=
λ n, f (nth s n)

/-- Zip two streams using a binary operation:
`stream.nth n (stream.zip f s₁ s₂) = f (stream.nth s₁) (stream.nth s₂)`. -/
def zip (f : α → β → δ) (s₁ : stream α) (s₂ : stream β) : stream δ :=
λ n, f (nth s₁ n) (nth s₂ n)

/-- Enumerate a stream by tagging each element with its index. -/
def enum (s : stream α) : stream (ℕ × α) := λ n, (n, s.nth n)

/-- The constant stream: `stream.nth n (stream.const a) = a`. -/
def const (a : α) : stream α :=
λ n, a

/-- Iterates of a function as a stream. -/
def iterate (f : α → α) (a : α) : stream α :=
λ n, nat.rec_on n a (λ n r, f r)

def corec (f : α → β) (g : α → α) : α → stream β :=
λ a, map f (iterate g a)

def corec_on (a : α) (f : α → β) (g : α → α) : stream β :=
corec f g a

def corec' (f : α → β × α) : α → stream β := corec (prod.fst ∘ f) (prod.snd ∘ f)

/-- Use a state monad to generate a stream through corecursion -/
def corec_state {σ α} (cmd : state σ α) (s : σ) : stream α :=
corec prod.fst (cmd.run ∘ prod.snd) (cmd.run s)

-- corec is also known as unfold
def unfolds (g : α → β) (f : α → α) (a : α) : stream β :=
corec g f a

/-- Interleave two streams. -/
def interleave (s₁ s₂ : stream α) : stream α :=
corec_on (s₁, s₂)
  (λ ⟨s₁, s₂⟩, head s₁)
  (λ ⟨s₁, s₂⟩, (s₂, tail s₁))

infix ` ⋈ `:65 := interleave

/-- Elements of a stream with even indices. -/
def even (s : stream α) : stream α :=
corec
  (λ s, head s)
  (λ s, tail (tail s))
  s

/-- Elements of a stream with odd indices. -/
def odd (s : stream α) : stream α :=
even (tail s)

/-- Append a stream to a list. -/
def append_stream : list α → stream α → stream α
| []              s := s
| (list.cons a l) s := a :: append_stream l s

infix ` ++ₛ `:65 := append_stream

/-- `take n s` returns a list of the `n` first elements of stream `s` -/
def take : ℕ → stream α → list α
| 0     s := []
| (n+1) s := list.cons (head s) (take n (tail s))

/-- An auxiliary definition for `stream.cycle` corecursive def -/
protected def cycle_f : α × list α × α × list α → α
| (v, _, _, _) := v

/-- An auxiliary definition for `stream.cycle` corecursive def -/
protected def cycle_g : α × list α × α × list α → α × list α × α × list α
| (v₁, [],              v₀, l₀) := (v₀, l₀, v₀, l₀)
| (v₁, list.cons v₂ l₂, v₀, l₀) := (v₂, l₂, v₀, l₀)

/-- Interpret a nonempty list as a cyclic stream. -/
def cycle : Π (l : list α), l ≠ [] → stream α
| []              h := absurd rfl h
| (list.cons a l) h := corec stream.cycle_f stream.cycle_g (a, l, a, l)

/-- Tails of a stream, starting with `stream.tail s`. -/
def tails (s : stream α) : stream (stream α) :=
corec id tail (tail s)

/-- An auxiliary definition for `stream.inits`. -/
def inits_core (l : list α) (s : stream α) : stream (list α) :=
corec_on (l, s)
  (λ ⟨a, b⟩, a)
  (λ p, match p with (l', s') := (l' ++ [head s'], tail s') end)

/-- Nonempty initial segments of a stream. -/
def inits (s : stream α) : stream (list α) :=
inits_core [head s] (tail s)

/-- A constant stream, same as `stream.const`. -/
def pure (a : α) : stream α :=
const a

/-- Given a stream of functions and a stream of values, apply `n`-th function to `n`-th value. -/
def apply (f : stream (α → β)) (s : stream α) : stream β :=
λ n, (nth f n) (nth s n)

infix ` ⊛ `:75 := apply  -- input as \o*

/-- The stream of natural numbers: `stream.nth n stream.nats = n`. -/
def nats : stream nat :=
λ n, n

end stream
