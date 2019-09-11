/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import data.seq.seq
/-!
# Basic Definitions for Continued Fractions

## Summary

We define generalised, simple, and regular continued fractions and functions to evaluate their
convergents. We follow the naming conventions from Wikipedia and [wall2018analytic], Chapter 1.

## Main definitions

- Generalised continued fractions
- Simple continued fractions
- Regular continued fractions
- Computation of convergents using the recurrence relation in `convergents`.
- Computation of convergents by directly evaluating the fraction described by the gcf in
`convergents'`.

## Implementation notes

We use sequences from `data.seq` to encode potentially infinite sequences.

## References

- https://en.wikipedia.org/wiki/Generalized_continued_fraction
- [Wall, H.S., *Analytic Theory of Continued Fractions*][wall2018analytic]

## Tags

numerics, number theory, approximations, fractions
-/


/-
A *generalised continued fraction* (gcf) is a potentially infinite expression of the form

                                a₀
                h + --------------------------
                                  a₁
                      b₀ + --------------------
                                    a₂
                            b₁ + --------------
                                        a₃
                                  b₂ + --------
                                      b₃ + ...

where `h` is called the *head term* or *integer part*, the `aᵢ` are called the
*partial numerators* and the `bᵢ` the *partial denominators* of the gcf. For convenience, one often
writes `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`.
-/

-- Fix a carrier `α`.
variable (α : Type*)

/-- We collect a partial numerator `aᵢ` and partial denominator `bᵢ` in a pair `⟨aᵢ,bᵢ⟩`. -/
protected structure gcf.pair := (a : α) (b : α)

/- Interlude: define some expected coercions and instances. -/
namespace gcf.pair

/-- Make a gcf.pair printable. -/
instance [has_repr α] : has_repr (gcf.pair α) :=
⟨λ p, "(a : " ++ (repr p.a) ++ ", b : " ++ (repr p.b) ++ ")"⟩

section coe
/-- Fix another type `β` and assume `α` can be converted to `β`. -/
variables {α} {β : Type*} [has_coe α β]

/-- Coerce a gcf.pair by elementwise coercion. -/
instance has_coe_to_gcf_pair : has_coe (gcf.pair α) (gcf.pair β) := ⟨λ ⟨a, b⟩, ⟨(a : β), (b : β)⟩⟩

@[simp, move_cast]
lemma coe_to_gcf_pair {a b : α} : (↑(gcf.pair.mk a b) : gcf.pair β) = gcf.pair.mk (a : β) (b : β) :=
rfl

end coe
end gcf.pair

/-- A gcf consists of a head term `h` and a sequence of gcf.pairs `s`. -/
structure gcf := (h : α) (s : seq $ gcf.pair α)

variable {α}

namespace gcf

/-- Returns the sequence of partial numerators `aᵢ` of `g`. -/
def partial_numerators (g : gcf α) : seq α := g.s.map gcf.pair.a
/-- Returns the sequence of partial denominators `bᵢ` of `g`. -/
def partial_denominators (g : gcf α) : seq α := g.s.map gcf.pair.b

/-- A gcf terminates at position `n` if its sequence terminates at position `n`. -/
def terminates_at (g : gcf α) (n : ℕ) : Prop := g.s.terminates_at n

/-- It is decidable whether a gcf terminates at a given position. -/
instance terminates_at_decidable (g : gcf α) (n : ℕ) : decidable (g.terminates_at n) :=
by { unfold terminates_at, apply_instance }

/-- A gcf terminates if its sequence terminates. -/
def terminates (g : gcf α) : Prop := g.s.terminates

/- Interlude: define some expected coercions. -/
section coe
/-- Fix another type `β` and assume `α` can be converted to `β`. -/
variables {β : Type*} [has_coe α β]

/-- Coerce a sequence by elementwise coercion. -/
def seq.coe_to_seq : has_coe (seq α) (seq β) := ⟨seq.map (λ a, (a : β))⟩

local attribute [instance] seq.coe_to_seq

/-- Coerce a gcf by elementwise coercion. -/
instance has_coe_to_gcf : has_coe (gcf α) (gcf β) := ⟨λ ⟨h, s⟩, ⟨(h : β), (s : seq $ gcf.pair β)⟩⟩

@[simp, move_cast]
lemma coe_to_gcf {g : gcf α} : (↑(g : gcf α) : gcf β) = ⟨(g.h : β), (g.s : seq $ gcf.pair β)⟩ :=
by { cases g, refl }

end coe
end gcf

/-
We now continue to define simple continued fractions. A *simple continued fraction* (scf) is a gcf
whose partial numerators are all equal to one.

                                1
                h + --------------------------
                                  1
                      b₀ + --------------------
                                    1
                            b₁ + --------------
                                        1
                                  b₂ + --------
                                      b₃ + ...


Again, for convenience, one writes `[h; b₀, b₁, b₂,...]`.
-/

/-- A gcf is a simple continued fraction (scf) if all partial numerators are equal to one. -/
def gcf.is_scf (g : gcf α) [has_one α] : Prop :=
∀ (n : ℕ) (aₙ : α), g.partial_numerators.nth n = some aₙ → aₙ = 1

variable (α)
/--
A simple continued fraction (scf) is a gcf whose partial numerators are equal to one.
It is the subtype of gcfs that satisfy `gcf.is_scf`.
 -/
def scf [has_one α] := {g : gcf α // g.is_scf}

variable {α}
/- Interlude: define some expected coercions. -/
namespace scf
variable [has_one α]

/-- Lift a scf to a gcf using the inclusion map. -/
instance has_coe_to_gcf : has_coe (scf α) (gcf α) := by {unfold scf, apply_instance}

@[simp, elim_cast]
lemma coe_to_gcf {s : scf α} : (↑s : gcf α) = s.val := rfl

end scf

/-
Next, we define regular continued fractions. A *regular continued fraction* (rcf) is a scf whose
partial denominators `bᵢ` are all positive, i.e. `0 < bᵢ`.
-/

/-- A scf is a regular continued fraction (rcf) if all partial denominators are positive. -/
def scf.is_rcf [has_one α] [has_zero α] [has_lt α] (s : scf α) : Prop :=
∀ (n : ℕ) (bₙ : α), (↑s : gcf α).partial_denominators.nth n = some bₙ → 0 < bₙ

variable (α)

/--
A regular continued fraction (rcf) is a scf whose partial denominators are all positive.
It is the subtype of scfs that satisfy `scf.is_rcf`.
 -/
def rcf [has_one α] [has_zero α] [has_lt α] := {s : scf α // s.is_rcf}

variable {α}

/- Interlude: define some expected coercions. -/
namespace rcf
variables [has_one α] [has_zero α] [has_lt α]

/-- Lift a rcf to a scf using the inclusion map. -/
instance has_coe_to_scf : has_coe (rcf α) (scf α) := by {unfold rcf, apply_instance}

@[simp, elim_cast]
lemma coe_to_scf {r : rcf α} : (↑r : scf α) = r.val := rfl

/-- Lift a rcf to a scf using the inclusion map. -/
instance has_coe_to_gcf : has_coe (rcf α) (gcf α) := ⟨λ r, ↑(↑r : scf α)⟩

@[simp, elim_cast]
lemma coe_to_gcf {r : rcf α} : (↑r : gcf α) = r.val := rfl

end rcf

/-
We now define how to compute the convergents of a gcf. There are two standard ways to do this:
directly evaluating the (infinite) fraction described by the gcf or using a recurrence relation.
For rcfs, these computations are equivalent as shown in
`algebra.continued_fractions.theorems.convergents_equiv`.
-/
namespace gcf

-- Fix a division ring for the computations.
variable [division_ring α]

/-
We start with the definition of the recurrence relation. Given a gcf `g`, for all `n ≥ 1`, we define

  `A₋₁ = 1,  A₀ = b₀,   Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`, and
  `B₋₁ = 0,  B₀ = 1,    Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`.

`Aₙ, `Bₙ` are called the *nth continuants*, Aₙ the *nth numerator*, and `Bₙ` the
*nth denominator* of `g`. The *nth convergent* of `g` is given by `Aₙ / Bₙ`.
-/

/--
Returns the next numerator `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`, where `predA` is `Aₙ₋₁` and
`ppredA` is `Aₙ₋₂`.
-/
def next_numerator (aₙ bₙ ppredA predA : α) : α := bₙ * predA + aₙ * ppredA

/--
Returns the next denominator `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`, where `predB` is `Bₙ₋₁` and
`ppredB` is `Bₙ₋₂`.
-/
def next_denominator (aₙ bₙ ppredB predB : α) : α := bₙ * predB + aₙ * ppredB

/--
Returns the next continuants `⟨Aₙ, Bₙ⟩` using `next_numerator` and `next_denominator`, where `pred`
is `⟨Aₙ₋₁, Bₙ₋₁⟩` and `ppred` is `⟨Aₙ₋₂, Bₙ₋₂⟩`.
-/
def next_continuants (aₙ bₙ : α) (ppred pred : gcf.pair α) : gcf.pair α :=
⟨next_numerator aₙ bₙ ppred.a pred.a, next_denominator aₙ bₙ ppred.b pred.b⟩

/-- Returns the continuants `⟨Aₙ₋₁, Bₙ₋₁⟩` of `g`. -/
def continuants_aux (g : gcf α) : stream (gcf.pair α)
| 0 := ⟨1, 0⟩
| 1 := ⟨g.h, 1⟩
| (n + 2) :=
  match g.s.nth n with
  | none := continuants_aux (n + 1)
  | some gp := next_continuants gp.a gp.b (continuants_aux n) (continuants_aux $ n + 1)
  end

/-- Returns the continuants `⟨Aₙ, Bₙ⟩` of `g`. -/
def continuants (g : gcf α) : stream (gcf.pair α) := g.continuants_aux.tail

/-- Returns the numerators `Aₙ` of `g`. -/
def numerators (g : gcf α) : stream α := g.continuants.map gcf.pair.a

/-- Returns the denominators `Bₙ` of `g`. -/
def denominators (g : gcf α) : stream α := g.continuants.map gcf.pair.b

/-- Returns the convergents `Aₙ / Bₙ` of `g`, where `Aₙ, Bₙ` are the nth continuants of `g`. -/
def convergents (g : gcf α) : stream α := λ (n : ℕ), (g.numerators n) / (g.denominators n)

/--
Returns the approximation of the fraction described by the given sequence up to a given position n.
For example, `convergents'_aux [(1, 2), (3, 4), (5, 6)] 2 = 1 / (2 + 3 / 4)` and
`convergents'_aux [(1, 2), (3, 4), (5, 6)] 0 = 0`.
-/
def convergents'_aux : seq (gcf.pair α) → ℕ → α
| s 0 := 0
| s (n + 1) := match s.head with
  | none := 0
  | some gp := gp.a / (gp.b + convergents'_aux s.tail n)
  end

/--
Returns the convergents of `g` by evaluating the fraction described by `g` up to a given
position `n`. For example, `convergents' [9; (1, 2), (3, 4), (5, 6)] 2 = 9 + 1 / (2 + 3 / 4)` and
`convergents' [9; (1, 2), (3, 4), (5, 6)] 0 = 9`
-/
def convergents' (g : gcf α) (n : ℕ) : α := g.h + convergents'_aux g.s n

end gcf
