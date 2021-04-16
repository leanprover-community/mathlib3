/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/

import ..todo
import topology.separation

/-!
A formal roadmap for the shrinking lemma for local finite countable covers.

It contains the statement of the lemma, and an informal sketch of the proof,
along with references.

The lemma is now formalized as `exists_subset_Union_closure_subset` in `topology/shrinking_lemma`.
This file is preserved as an example of a formal roadmap.

The actual implementation differs from the roadmap in two aspects:

- it uses a custom `structure` with a `partial_order` instead of a combination
  of `sigma` and `subtype`;
- it provides a version for coverings of a closed set in a normal space. While mathematically it's
  almost the same (just add `sᶜ` to the covering), it's easier to prove a version for a closed set,
  then apply it to `univ` than to deal with coverings indexed by `option α`.
-/

open set

universes u v

/-- A point-finite open cover of a closed subset of a normal space can be "shrunk" to a new open
cover so that the closure of each new open set is contained in the corresponding original open
set. -/
lemma roadmap.shrinking_lemma {X : Type u} [topological_space X] [normal_space X]
  {s : set X} (hs : is_closed s) {α : Type v} (u : α → set X) (uo : ∀ a, is_open (u a))
  (uf : ∀ x, finite {a | x ∈ u a}) (su : s ⊆ Union u) :
  ∃ v : α → set X, s ⊆ Union v ∧ ∀ a, is_open (v a) ∧ closure (v a) ⊆ u a :=
todo
/-
Apply Zorn's lemma to
 T = Σ (i : set α), {v : α → set X // s ⊆ Union v ∧ (∀ a, is_open (v a)) ∧
                                      (∀ a ∈ i, closure (v a) ⊆ u a) ∧ (∀ a ∉ i, v a = u a)}
with the ordering
 ⟨i, v, _⟩ ≤ ⟨i', v', _⟩ ↔ i ⊆ i' ∧ ∀ a ∈ i, v a = v' a
The hypothesis that `X` is normal implies that a maximal element must have `i = univ`.
Point-finiteness of `u` (hypothesis `uf`) implies that
the least upper bound of a chain in `T` again yields a covering of `s`.

Compare proofs in
* https://ncatlab.org/nlab/show/shrinking+lemma#ShrinkingLemmaForLocallyFiniteCountableCovers
* Bourbaki, General Topology, Chapter IX, §4.3
* Dugundji, Topology, Chapter VII, Theorem 6.1
-/
