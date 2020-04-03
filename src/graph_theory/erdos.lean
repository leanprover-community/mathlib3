/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

-- TODO: rename this file

import graph_theory.basic
import measure_theory.probability_mass_function

/-!
# Graphs with high chromatic number and girth
-/

open_locale classical
noncomputable theory

universe variables v v₁ v₂ v₃ u u₁ u₂ u₃

variables {V : Type u}

def graph.weighted_edge_count [fintype V] (G : graph V) (p : nnreal) (hp : p ≤ 1) :
  nnreal :=
finset.prod finset.univ $ λ (xy : V × V),
if xy.1 ~[G] xy.2 then p else (1 - p)

@[ext]
lemma graph.ext (G₁ G₂ : graph V) (h : ∀ x y, (x ~[G₁] y) ↔ (x ~[G₂] y)) : G₁ = G₂ :=
begin
  repeat {cases G₁ with G₁, cases G₂ with G₂},
  have : G₁ = G₂, { ext, apply h },
  cases this, congr, ext, refl,
end

-- def graph.edges_as_sets (G : graph V) : set ({s : finset V // s.card = 2} ⊕ V)
-- | (sum.inl s) := ∃ (x y : V), x ∈ s.1 ∧ y ∈ s.1 ∧ x ≠ y ∧ (x ~[G] y)
-- | (sum.inr x) := x ~[G] x

-- def graph.foo (G : graph V) (x y : V) : {s : finset V // s.card = 2} ⊕ V :=
-- if h : x = y then sum.inr x else sum.inl ⟨{x,y}, by {  }⟩

-- lemma graph.edges_as_sets_bijective : function.bijective (@graph.edges_as_sets V) :=
-- begin
--   split,
--   { assume G₁ G₂ h, ext, },
--   {  }
-- end

abbreviation random_graph (V : Type u) := pmf (graph V)

namespace random_graph

/-- The Erdős–Rényi model for random graphs. -/
def with_edge_prob (V : Type u) [fintype V] (p : nnreal) (hp : p ≤ 1) :
  random_graph V :=
⟨λ G, G.weighted_edge_count p hp,
begin

end⟩

end random_graph
