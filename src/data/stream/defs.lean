/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

/-!
# Definition of `stream` and functions on streams

A stream `stream α` is an infinite sequence of elements of `α`. One can also think about it as an
infinite list. In this file we define `stream` and some functions that take and/or return streams.
-/

universes u v w

def stream (α : Type u) := nat → α

open nat

namespace stream
variables {α : Type u} {β : Type v} {δ : Type w}

def cons (a : α) (s : stream α) : stream α :=
λ i,
  match i with
  | 0      := a
  | succ n := s n
  end

notation h :: t := cons h t

@[reducible] def head (s : stream α) : α :=
s 0

def tail (s : stream α) : stream α :=
λ i, s (i+1)

def drop (n : nat) (s : stream α) : stream α :=
λ i, s (i+n)

@[reducible] def nth (n : nat) (s : stream α) : α :=
s n

def all (p : α → Prop) (s : stream α) := ∀ n, p (nth n s)

def any (p : α → Prop) (s : stream α) := ∃ n, p (nth n s)

protected def mem (a : α) (s : stream α) := any (λ b, a = b) s

instance : has_mem α (stream α) :=
⟨stream.mem⟩

def map (f : α → β) (s : stream α) : stream β :=
λ n, f (nth n s)

def zip (f : α → β → δ) (s₁ : stream α) (s₂ : stream β) : stream δ :=
λ n, f (nth n s₁) (nth n s₂)

def const (a : α) : stream α :=
λ n, a

def iterate (f : α → α) (a : α) : stream α :=
λ n, nat.rec_on n a (λ n r, f r)

def corec (f : α → β) (g : α → α) : α → stream β :=
λ a, map f (iterate g a)

def corec_on (a : α) (f : α → β) (g : α → α) : stream β :=
corec f g a

def corec' (f : α → β × α) : α → stream β := corec (prod.fst ∘ f) (prod.snd ∘ f)

-- corec is also known as unfold
def unfolds (g : α → β) (f : α → α) (a : α) : stream β :=
corec g f a

def interleave (s₁ s₂ : stream α) : stream α :=
corec_on (s₁, s₂)
  (λ ⟨s₁, s₂⟩, head s₁)
  (λ ⟨s₁, s₂⟩, (s₂, tail s₁))

infix `⋈`:65 := interleave

def even (s : stream α) : stream α :=
corec
  (λ s, head s)
  (λ s, tail (tail s))
  s

def odd (s : stream α) : stream α :=
even (tail s)

def append_stream : list α → stream α → stream α
| []              s := s
| (list.cons a l) s := a :: append_stream l s

infix `++ₛ`:65 := append_stream

def approx : nat → stream α → list α
| 0     s := []
| (n+1) s := list.cons (head s) (approx n (tail s))

/-- `take s n` returns a list of the `n` first elements of stream `s` -/
def take {α} (s : stream α) (n : ℕ) : list α :=
(list.range n).map s

/-- An auxiliary definition for `stream.cycle` corecursive def -/
protected def cycle_f : α × list α × α × list α → α
| (v, _, _, _) := v

/-- An auxiliary definition for `stream.cycle` corecursive def -/
protected def cycle_g : α × list α × α × list α → α × list α × α × list α
| (v₁, [],              v₀, l₀) := (v₀, l₀, v₀, l₀)
| (v₁, list.cons v₂ l₂, v₀, l₀) := (v₂, l₂, v₀, l₀)

def cycle : Π (l : list α), l ≠ [] → stream α
| []              h := absurd rfl h
| (list.cons a l) h := corec stream.cycle_f stream.cycle_g (a, l, a, l)

def tails (s : stream α) : stream (stream α) :=
corec id tail (tail s)

def inits_core (l : list α) (s : stream α) : stream (list α) :=
corec_on (l, s)
  (λ ⟨a, b⟩, a)
  (λ p, match p with (l', s') := (l' ++ [head s'], tail s') end)


def inits (s : stream α) : stream (list α) :=
inits_core [head s] (tail s)

def pure (a : α) : stream α :=
const a

def apply (f : stream (α → β)) (s : stream α) : stream β :=
λ n, (nth n f) (nth n s)

infix `⊛`:75 := apply  -- input as \o*

def nats : stream nat :=
λ n, n

end stream
