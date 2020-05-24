/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.basic
import algebra.ordered_field
import algebra.archimedean
/-!
# Computable Continued Fractions

## Summary

We formalise the standard computation of regular continued fractions for linear ordered floor
fields. The algorithm is rather simple and connected to the Euclidean algorithm. It can be found,
for example, on Wikipedia:
https://en.wikipedia.org/wiki/Continued_fraction#Calculating_continued_fraction_representations.

## Main definitions

- `generalized_continued_fraction.of`: computes the generalised continued fraction of a value.
In fact, it computes a regular continued fraction (the proof will be added in a future commit).

## References

- https://en.wikipedia.org/wiki/Continued_fraction

## Tags

numerics, number theory, approximations, fractions
-/

namespace generalized_continued_fraction
open generalized_continued_fraction as gcf

-- Fix a carrier `K`.
variable (K : Type*)

/--
We collect an integer part `b = ⌊v⌋` and fractional part `fr = v - ⌊v⌋` of a value `v` in a pair
`⟨b, fr⟩`.
-/
structure int_fract_pair := (b : ℤ) (fr : K)

/- Interlude: define some expected coercions and instances. -/
namespace int_fract_pair

/-- Make an `int_fract_pair` printable. -/
instance [has_repr K] : has_repr (int_fract_pair K) :=
⟨λ p, "(b : " ++ (repr p.b) ++ ", fract : " ++ (repr p.fr) ++ ")"⟩

instance inhabited [inhabited K] : inhabited (int_fract_pair K) := ⟨⟨0, (default _)⟩⟩

variable {K}

section coe
/-! Interlude: define some expected coercions. -/
/- Fix another type `β` and assume `K` can be converted to `β`. -/
variables {β : Type*} [has_coe K β]

/-- Coerce a pair by coercing the fractional component. -/
instance has_coe_to_int_fract_pair : has_coe (int_fract_pair K) (int_fract_pair β) :=
⟨λ ⟨b, fr⟩, ⟨b, (fr : β)⟩⟩


@[simp, norm_cast]
lemma coe_to_int_fract_pair {b : ℤ} {fr : K} :
  (↑(int_fract_pair.mk b fr) : int_fract_pair β) = int_fract_pair.mk b (↑fr : β) :=
rfl

end coe

-- Note: this could be relaxed to something like `discrete_linear_ordered_division_ring` in the
-- future.
/-- Fix a linear ordered ring with `floor` function. -/
variables [discrete_linear_ordered_field K] [floor_ring K]

/-- Creates the integer and fractional part of a value `v`, i.e. `⟨⌊v⌋, v - ⌊v⌋⟩`. -/
protected def of (v : K) : int_fract_pair K := ⟨⌊v⌋, fract v⟩

/-- Creates the stream of integer and fractional parts of a value `v`. -/
protected def stream (v : K) : stream $ option (int_fract_pair K)
| 0 := some (int_fract_pair.of v)
| (n + 1) := do ap_n ← stream n,
  if ap_n.fr = 0 then none else int_fract_pair.of ap_n.fr⁻¹

/--
Shows that `stream` has the sequence property, that is once we return `none` at position `n`,
we also return `none` at `n + 1`.
-/
lemma stream_is_seq (v : K) : (int_fract_pair.stream v).is_seq :=
by { assume _ hyp, simp [int_fract_pair.stream, hyp] }

/-- Creates the sequence with head of `int_fract_pair`s. -/
protected def seq1 (v : K) : seq1 $ int_fract_pair K :=
⟨
  int_fract_pair.of v,--the head
  seq.tail -- take the tail of `int_fract_pair.stream` since the first element is in the head
  ⟨ -- create a sequence from `int_fract_pair.stream`
    int_fract_pair.stream v, -- the underlying stream
    @stream_is_seq _ _ _ v
  ⟩
⟩
end int_fract_pair

variable {K}

/--
Returns the `generalized continued fraction` of a value. In fact, the returned gcf is also
a regular continued fraction (the proof will be added in a future commit).
-/
protected def of [discrete_linear_ordered_field K] [floor_ring K] (v : K) : gcf K :=
let ⟨h, s⟩ := int_fract_pair.seq1 v in -- get the sequence of integer and fractional parts.
⟨
  h.b, -- the head is just the first integer part
  s.map (λ p, ⟨1, p.b⟩) -- the sequence consists of the remaining integer parts as the partial
                        -- denominators; all partial numerators are simply 1
⟩

end generalized_continued_fraction
