/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import order.basic
import data.equiv.encodable

/-!
# Generic cofilters

This file proves the dual Rasiowa–Sikorski lemma: given a preorder `P`, a term `p : P`, and
a countable family `𝒟` of cofinal subsets of `P`, we construct a downwards closed, upwards
directed subset of `P` which contains `p` and intersects every set in `𝒟`.

## Main definitions

- `generic.cofilter p 𝒟`: the constructed subset of `P`, a `𝒟`-generic cofilter.
- `generic.directed_on p 𝒟`: the fact that the generic cofilter is upwards directed.
- `generic.meets p 𝒟`: the fact that the generic cofilter intersects all sets in `𝒟`.

## Usage

This provides a framework for certain recursive constructions, similar to Zorn's lemma.
Loosely speaking, suppose we want to construct an object satisfying some countable family
of conditions. In this framework, we need to:

- Define a type `P`, whose terms should represent finitary attempts at constructing the object.
- Provide a 'starting point' `p : P` for the construction.
- Define a reflexive and transitive order `≤` on `P`, where `x ≤ y` should mean '`y` extends `x`'.
- For each condition, define a subset of `P`, consisting of attemps which guarantee the condition,
  together with a proof that any attempt can be extended so as to guarantee the condition.
- Use `generic.cofilter` to define the desired object, as a limit of the attempts.

## References

https://en.wikipedia.org/wiki/Rasiowa–Sikorski_lemma

## Tags

generic, filter, countable, cofinal, dense

-/

variables {P : Type*} [preorder P]

/-- A downwards closed set, or initial segment. -/
def downwards_closed (s : set P) : Prop := ∀ (x : P) (y ∈ s), x ≤ y → x ∈ s

/-- A subset of a preorder is cofinal if it contains arbitrarily large elements. -/
def cofinal (s : set P) : Prop := ∀ x : P, ∃ y ∈ s, x ≤ y

namespace cofinal

variables {s : set P} (h : cofinal s) (x : P)

/-- An element of a cofinal set lying above a given element. -/
noncomputable def above : P :=
classical.some $ h x

lemma above_mem : above h x ∈ s :=
by { have := classical.some_spec (h x), tauto }

lemma le_above : x ≤ above h x :=
by { have := classical.some_spec (h x), tauto }

end cofinal

namespace generic

variables (p : P) {ι : Type*} [encodable ι] (𝒟 : ι → { D : set P // cofinal D })

/-- Given a countable family of cofinal sets and a starting point,
  this is an increasing sequence that intersects each cofinal set. -/
noncomputable def seq : ℕ → P
| 0 := p
| (n+1) := match encodable.decode ι n with
            | none := seq n
            | some i := cofinal.above (𝒟 i).property (seq n)
           end

lemma seq.monotone : monotone (seq p 𝒟) :=
begin
  apply monotone_of_monotone_nat,
  intros n,
  dunfold seq,
  cases encodable.decode ι n,
  { refl },
  { apply cofinal.le_above },
end

lemma seq.starting_point : seq p 𝒟 0 = p := rfl

lemma seq.encode_mem (i : ι) : seq p 𝒟 (encodable.encode i + 1) ∈ (𝒟 i).val :=
by { dunfold seq, rw encodable.encodek, apply cofinal.above_mem, }

/-- Given a countable family `𝒟` of cofinal subsets of a preorder `P` and a starting point
    `p : P`, `generic.cofilter p 𝒟` is a subset of `P` which
    - contains `p`
    - is downwards closed
    - is upwards directed
    - meets every set in `𝒟` -/
def cofilter : set P := { x : P | ∃ n, x ≤ seq p 𝒟 n }

lemma starting_point_mem : p ∈ cofilter p 𝒟 := ⟨0, le_refl _⟩

lemma downwards_closed : downwards_closed (cofilter p 𝒟) :=
λ x y ⟨n, hn⟩ hx, ⟨n, le_trans hx hn⟩

lemma directed_on : directed_on (≤) (cofilter p 𝒟) :=
λ x ⟨n, hn⟩ y ⟨m, hm⟩, ⟨_, ⟨max n m, le_refl _⟩,
    le_trans hn $ seq.monotone p 𝒟 (le_max_left _ _),
    le_trans hm $ seq.monotone p 𝒟 (le_max_right _ _) ⟩

lemma meets (i : ι) : (cofilter p 𝒟 ∩ (𝒟 i).val).nonempty :=
⟨_, ⟨_, le_refl _⟩, seq.encode_mem p 𝒟 i⟩

attribute [irreducible] cofilter

end generic
