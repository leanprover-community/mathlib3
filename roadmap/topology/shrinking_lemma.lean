import roadmap.todo
import topology.separation

open set

universes u v

/-- A point-finite open cover of a closed subset of a normal space can be "shrunk" to a new open cover
 so that the closure of each new open set is contained in the corresponding original open set. -/
lemma shrinking_lemma {X : Type u} [topological_space X] [normal_space X]
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
