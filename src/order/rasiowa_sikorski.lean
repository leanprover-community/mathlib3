/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import order.basic
import data.equiv.encodable

/-!
# The Rasiowa–Sikorski lemma

This file contains the (dual) Rasiowa–Sikorski lemma.

## Main definitions

We work with a preorder `P`, a term `p : P`, and a countable family `𝒟` of cofinal subsets of `P`.

- `rasiowa_sikorski.witness p 𝒟 : set P`: the witness to the lemma, a `𝒟`-generic 'cofilter'.
- `rasiowa_sikorski.directed_on p 𝒟`: the fact that the witness is (upwards) directed.
- `rasiowa_sikorski.meets p 𝒟`: the fact that the witness is `𝒟`-generic.

## Usage

This provides an API for certain recursive constructions, similar to Zorn's lemma.
Loosely speaking, suppose we want to construct an object satisfying some countable family
of conditions. To apply Rasiowa–Sikorski, we need to:

- Define a type `P`, whose terms should represent finitary attempts at constructing the object.
- Provide a 'starting point' `p : P` for the construction.
- Define a reflexive and transitive order `≤` on `P`, where `x ≤ y` should mean '`y` extends `x`'.
- For each condition, define a subset of `P`, consisting of attemps which guarantee the condition,
  together with a proof that any attempt can be extended so as to guarantee the condition.
- Use `rasiowa_sikorski.witness` to define the desired object, as a limit of the attempts.

## References

https://en.wikipedia.org/wiki/Rasiowa–Sikorski_lemma

## Tags

generic, filter, countable, cofinal, dense

-/

variables {P : Type*} [preorder P]

/-- A downwards closed set, or initial segment. -/
def downwards_closed (s : set P) := ∀ (x : P) (y ∈ s), x ≤ y → x ∈ s

/-- A subset of a preorder is cofinal if contains arbitrarily large elements. -/
def cofinal (s : set P) := ∀ x : P, ∃ y ∈ s, x ≤ y

namespace cofinal

variables {s : set P} (h : cofinal s) (x : P)

/-- An element of a cofinal set lying above a given element. -/
noncomputable def above : P :=
classical.some $ h x

lemma above_elem : above h x ∈ s :=
by { have := classical.some_spec (h x), tauto }

lemma le_above : x ≤ above h x :=
by { have := classical.some_spec (h x), tauto }

end cofinal

namespace rasiowa_sikorski

variables (p : P) {ι : Type*} [encodable ι] (𝒟 : ι → { D : set P // cofinal D })

/-- Given a countable family of cofinal sets and a starting point,
  constructs an increasing sequence that meets each cofinal set. -/
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

lemma seq.encode_elem (i : ι) : seq p 𝒟 (encodable.encode i + 1) ∈ (𝒟 i).val :=
by { dunfold seq, rw encodable.encodek, apply cofinal.above_elem, }

/-- The witness to the Rasiowa–Sikorski lemma: a `𝒟`-generic cofilter. -/
def witness : set P := { x : P | ∃ n, x ≤ seq p 𝒟 n }

lemma downwards_closed : downwards_closed (witness p 𝒟) :=
λ x y ⟨n, hn⟩ hx, ⟨n, le_trans hx hn⟩

lemma directed_on : directed_on (≤) (witness p 𝒟) :=
λ x ⟨n, hn⟩ y ⟨m, hm⟩, ⟨_, ⟨max n m, le_refl _⟩,
    le_trans hn $ seq.monotone p 𝒟 (le_max_left _ _),
    le_trans hm $ seq.monotone p 𝒟 (le_max_right _ _) ⟩

lemma starting_point : p ∈ witness p 𝒟 := ⟨0, le_refl _⟩

lemma meets (i : ι) : (witness p 𝒟 ∩ (𝒟 i).val).nonempty :=
⟨_, ⟨_, le_refl _⟩, seq.encode_elem p 𝒟 i⟩

attribute [irreducible] witness

end rasiowa_sikorski
