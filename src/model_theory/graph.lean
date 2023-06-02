/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.satisfiability
import combinatorics.simple_graph.basic

/-!
# First-Ordered Structures in Graph Theory

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file defines first-order languages, structures, and theories in graph theory.

## Main Definitions
* `first_order.language.graph` is the language consisting of a single relation representing
adjacency.
* `simple_graph.Structure` is the first-order structure corresponding to a given simple graph.
* `first_order.language.Theory.simple_graph` is the theory of simple graphs.
* `first_order.language.simple_graph_of_structure` gives the simple graph corresponding to a model
of the theory of simple graphs.

-/

universes u v w w'

namespace first_order
namespace language
open_locale first_order
open Structure

variables {L : language.{u v}} {α : Type w} {V : Type w'} {n : ℕ}

/-! ### Simple Graphs -/

/-- The language consisting of a single relation representing adjacency. -/
protected def graph : language :=
language.mk₂ empty empty empty empty unit

/-- The symbol representing the adjacency relation. -/
def adj : language.graph.relations 2 := unit.star

/-- Any simple graph can be thought of as a structure in the language of graphs. -/
def _root_.simple_graph.Structure (G : simple_graph V) :
  language.graph.Structure V :=
Structure.mk₂ empty.elim empty.elim empty.elim empty.elim (λ _, G.adj)

namespace graph

instance : is_relational (language.graph) := language.is_relational_mk₂

instance : subsingleton (language.graph.relations n) :=
language.subsingleton_mk₂_relations

end graph

/-- The theory of simple graphs. -/
protected def Theory.simple_graph : language.graph.Theory :=
{adj.irreflexive, adj.symmetric}

@[simp] lemma Theory.simple_graph_model_iff [language.graph.Structure V] :
  V ⊨ Theory.simple_graph ↔
    irreflexive (λ x y : V, rel_map adj ![x,y]) ∧ symmetric (λ x y : V, rel_map adj ![x,y]) :=
by simp [Theory.simple_graph]

instance simple_graph_model (G : simple_graph V) :
  @Theory.model _ V G.Structure Theory.simple_graph :=
begin
  simp only [Theory.simple_graph_model_iff, rel_map_apply₂],
  exact ⟨G.loopless, G.symm⟩,
end

variables (V)

/-- Any model of the theory of simple graphs represents a simple graph. -/
@[simps] def simple_graph_of_structure [language.graph.Structure V] [V ⊨ Theory.simple_graph] :
  simple_graph V :=
{ adj := λ x y, rel_map adj ![x,y],
  symm := relations.realize_symmetric.1 (Theory.realize_sentence_of_mem Theory.simple_graph
      (set.mem_insert_of_mem _ (set.mem_singleton _))),
  loopless := relations.realize_irreflexive.1 (Theory.realize_sentence_of_mem Theory.simple_graph
      (set.mem_insert _ _)) }

variables {V}

@[simp] lemma _root_.simple_graph.simple_graph_of_structure (G : simple_graph V) :
  @simple_graph_of_structure V G.Structure _ = G :=
by { ext, refl }

@[simp] lemma Structure_simple_graph_of_structure
  [S : language.graph.Structure V] [V ⊨ Theory.simple_graph] :
  (simple_graph_of_structure V).Structure = S :=
begin
  ext n f xs,
  { exact (is_relational.empty_functions n).elim f },
  { ext n r xs,
    rw iff_eq_eq,
    cases n,
    { exact r.elim },
    { cases n,
      { exact r.elim },
      { cases n,
        { cases r,
          change rel_map adj ![xs 0, xs 1] = _,
          refine congr rfl (funext _),
          simp [fin.forall_fin_two], },
        { exact r.elim } } } }
end

theorem Theory.simple_graph_is_satisfiable :
  Theory.is_satisfiable Theory.simple_graph :=
⟨@Theory.Model.of _ _ unit (simple_graph.Structure ⊥) _ _⟩

end language
end first_order
