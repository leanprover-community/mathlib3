/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
/-!

# Hamiltonian paths and cycles

## Main definitions

* `simple_graph.walk.is_hamiltonian`

## Tags

Eulerian circuits

-/

namespace simple_graph
variables {V : Type*} {G : simple_graph V}

namespace walk

/-- A walk `p` is *Hamiltonian* if it visits every vertex exactly once and every edge at most
once. -/
def is_hamiltonian [decidable_eq V] {u v : V} (p : G.walk u v) : Prop :=
p.edges.nodup ∧ ∀ v, p.support.count v = 1

lemma is_hamiltonian.is_path [decidable_eq V] {u v : V} {p : G.walk u v}
  (h : p.is_hamiltonian) : p.is_path :=
begin
  rw is_hamiltonian at h,
  split,
  { use h.1, },
  { rw list.nodup_iff_count_le_one,
    simp [h], },
end

/-- A loop `p` is a *Hamiltonian cycle* if it visits every vertex exactly once.
This is slightly different from `simple_graph.walk.is_hamiltonian` because it does
not double count the loop's basepoint. -/
-- Needs `p.is_trail` to prevent case of length-2 walk.
def is_hamiltonian_cycle [decidable_eq V] {u : V} (p : G.walk u u) : Prop :=
p.is_trail ∧ ∀ v, p.support.tail.count v = 1

lemma is_hamiltonian_cycle.is_cycle [decidable_eq V] {u : V} {p : G.walk u u}
  (h : p.is_hamiltonian_cycle) : p.is_cycle :=
begin
  cases h with hen h,
  rw is_cycle_def,
  split,
  { exact hen, },
  split,
  { cases p,
    { specialize h u,
      simpa using h, },
    { simp, }, },
  { rw list.nodup_iff_count_le_one,
    simp [h], },
end

end walk

end simple_graph
