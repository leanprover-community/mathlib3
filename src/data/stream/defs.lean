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
structure stream (α : Type u) := (nth : ℕ → α)

open nat

namespace stream
variables {α : Type u} {β : Type v} {δ : Type w}

/-- Prepend an element to a stream. -/
def cons (a : α) (s : stream α) : stream α := ⟨λ n, nat.cases_on n a s.nth⟩

notation (name := stream.cons) h ` :: ` t := cons h t

/-- Head of a stream: `stream.head s = stream.nth 0 s`. -/
def head (s : stream α) : α := s.nth 0

/-- Tail of a stream: `stream.tail (h :: t) = t`. -/
def tail (s : stream α) : stream α := ⟨λ i, s.nth (i+1)⟩

/-- Drop first `n` elements of a stream. -/
def drop (n : ℕ) (s : stream α) : stream α := ⟨λ i, s.nth (i + n)⟩

/-- Proposition saying that all elements of a stream satisfy a predicate. -/
def all (p : α → Prop) (s : stream α) := ∀ n, p (nth s n)

/-- Proposition saying that at least one element of a stream satisfies a predicate. -/
def any (p : α → Prop) (s : stream α) := ∃ n, p (nth s n)

/-- `a ∈ s` means that `a = stream.nth s n` for some `n`. -/
instance : has_mem α (stream α) := ⟨λ a s, any (λ b, a = b) s⟩

/-- Apply a function `f` to all elements of a stream `s`. -/
def map (f : α → β) (s : stream α) : stream β :=
⟨λ n, f (nth s n)⟩

/-- Zip two streams using a binary operation:
`stream.nth (stream.zip f s₁ s₂) n = f (stream.nth s₁ n) (stream.nth s₂ n)`. -/
def zip (f : α → β → δ) (s₁ : stream α) (s₂ : stream β) : stream δ :=
⟨λ n, f (nth s₁ n) (nth s₂ n)⟩

/-- Enumerate a stream by tagging each element with its index. -/
def enum (s : stream α) : stream (ℕ × α) := ⟨λ n, (n, s.nth n)⟩

/-- The constant stream: `stream.nth (pure a) n = a`. -/
instance : has_pure stream := ⟨λ _ a, ⟨λ _, a⟩⟩

/-- Iterates of a function as a stream. -/
def iterate (f : α → α) (a : α) : stream α := ⟨λ n, (f^[n] a)⟩

/-- Values of `f : α → β` on the iterates of a function `g : α → α`. -/
def corec (f : α → β) (g : α → α) (a : α) : stream β := map f (iterate g a)

/-- A version of `stream.corec` with a different order of arguments. -/
def corec_on (a : α) (f : α → β) (g : α → α) : stream β := corec f g a

/-- A version of `stream.corec` that takes a single function `f : α → β × α` as an argument. -/
def corec' (f : α → β × α) : α → stream β := corec (prod.fst ∘ f) (prod.snd ∘ f)

/-- Use a state monad to generate a stream through corecursion -/
def corec_state {σ α} (cmd : state σ α) (s : σ) : stream α :=
corec prod.fst (cmd.run ∘ prod.snd) (cmd.run s)

/-- Interleave two streams. -/
def interleave (s₁ s₂ : stream α) : stream α :=
⟨λ n, @nat.bit_cases_on (λ _, α) n $ λ b k, cond b (s₂.nth k) (s₁.nth k)⟩

infix ` ⋈ `:65 := interleave

/-- Elements of a stream with even indices. -/
def even (s : stream α) : stream α := ⟨λ n, s.nth (bit0 n)⟩

/-- Elements of a stream with odd indices. -/
def odd (s : stream α) : stream α := even (tail s)

/-- Append a stream to a list. -/
def _root_.list.append_stream : list α → stream α → stream α
| []       s := s
| (a :: l) s := a :: _root_.list.append_stream l s

infix (name := list.append_stream) ` ++ₛ `:65 := list.append_stream

/-- `take s n` returns a list of the `n` first elements of stream `s` -/
def take : ℕ → stream α → list α
| 0       s := []
| (n + 1) s := head s :: take n (tail s)

/-- Interpret a nonempty list as a cyclic stream. -/
def cycle (l : list α) (hl : l ≠ []) : stream α :=
⟨λ n, l.nth_le (n % l.length) (nat.mod_lt _ $ by { cases l, contradiction, exact nat.succ_pos _ })⟩

/-- Tails of a stream, starting with `s`. -/
def tails (s : stream α) : stream (stream α) := ⟨λ n, s.drop n⟩

/-- Initial segments of a stream. -/
def inits (s : stream α) : stream (list α) := ⟨λ n, s.take n⟩

/-- Given a stream of functions and a stream of values, apply `n`-th function to `n`-th value. -/
def apply (f : stream (α → β)) (s : stream α) : stream β := ⟨λ n, (nth f n) (nth s n)⟩

infix ` ⊛ `:75 := apply  -- input as \o*

/-- The stream of natural numbers: `stream.nth stream.nats n = n`. -/
def nats : stream nat := ⟨id⟩

end stream
