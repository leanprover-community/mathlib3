import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition

import .mathlib
import .reachable_outside
import .ends

open function
open finset
open set
open classical
open simple_graph.walk
open relation

universes u v w



noncomputable theory
local attribute [instance] prop_decidable

namespace simple_graph


variables  {V : Type u}
           (G : simple_graph V)
           {V' : Type v}
           (G' : simple_graph V')
           {V'' : Type w}
           (G'' : simple_graph V'')

namespace ends

open ro_component
open simple_graph

def cofinite (f : V → V') := ∀ x : V', (set.preimage f {x}).finite

lemma cofinite.comp {f : V → V'} {f' : V' → V''} (cof : cofinite f) (cof' : cofinite f') : cofinite (f' ∘ f) := sorry

def cofinite.preimage {f : V → V'} (cof : cofinite f) (K : finset V') : finset V := sorry
lemma cofinite.preimage.coe {f : V → V'} (cof : cofinite f) (K : finset V') : ↑(cof.preimage K) = set.preimage f K := sorry


def good_finset (f : V → V') (cof : cofinite f) (K : finset V') :=
  {L : finset V | cofinite.preimage cof K ⊆ L
                ∧ ∀ D : inf_ro_components G L, ∃! C : inf_ro_components G' K, f '' D ⊆ C}

structure coarse :=
  (to_fun : V → V')
  (cof : cofinite to_fun)
  (coarse : ∀ (K : finset V'), good_finset G G' to_fun cof K)

def close (f g : coarse G G') :=
  ∀ (K : finset V') (L : good_finset G G' f.to_fun f.cof K) (M : good_finset G G' f.to_fun f.cof K),
    ∃ N : finset V, ↑L ⊆ N ∧ ↑M ⊆ N
                  ∧ ∀ D : inf_ro_components G N,
                    ∃! C : inf_ro_components G' K, f.to_fun '' D ⊆ C ∧ g.to_fun '' D ⊆ C

def qi_embedding (f : V → V') : Prop := sorry -- ∃ (K : ℕ), ∀ (u v : V), dist (f u) (f v) ≤ K * (dist u v) + K ∧ dist u v ≤ K * (dist (f u) (f v)) + K

def coarse.of_qi_embedding (f : V → V') (qie : qi_embedding f) : coarse G G' f := sorry

def coarse.comp {f : V → V'} {f' : V' → V''} (coa : coarse G G' f) (coa' : coarse G' G'' f') : coarse G G'' (f' ∘ f) := sorry

def ends_map {f : V → V'} (coa : coarse G G' f) : @ends V G → @ends V' G' := sorry



end ends

end simple_graph
