/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller.
-/

import data.equiv.basic
import combinatorics.graphs.sym2
import combinatorics.graphs.multigraphs
import tactic
open function (hiding graph)
open equiv
open sym2

universes u v

namespace graph

structure graph (V : Type u) extends multigraph V :=
(single_edge : injective ends)
(loopless : ∀ e : E, ¬(ends e).is_diag)

variables {V : Type u}

def to_multigraph (g : graph V) : multigraph V :=
⟨g.E, g.ends⟩

def from_relation {α : Type u} {r : α → α → Prop} (h₁ : symmetric r) (h₂ : irreflexive r) : graph α :=
{
  E := {z : sym2 α // ∃ x y, r x y ∧ z = sym2.mk x y},
  ends := λ z, z.val,
  single_edge :=
    begin
      rintros ⟨z₁,x₁,y₁,hr₁,hz₁⟩ ⟨z₂,h₂,x₂,y₂,hr₂,hz₂⟩,
      simp,
    end,
  loopless :=
    begin
      rintro ⟨z,x,y,hr,hz⟩ abs,
      dsimp at abs,
      rw hz at abs,
      have heq := sym2.mk_is_diag abs,
      rw heq at hr,
      exact h₂ y hr,
    end
}

def graph.adj {V : Type u} (g : graph V) (x y : V) : Prop := g.to_multigraph.adj x y

lemma adj_of_from_relation {α : Type u} {r : α → α → Prop} (h₁ : symmetric r) (h₂ : irreflexive r)
: ∀ x y, r x y ↔ (graph.from_relation h₁ h₂).adj x y :=
begin
  intros x y,
  split,
  intro hr,
  refine ⟨⟨⟨sym2.mk x y, x, y, hr, rfl⟩, rfl⟩⟩,
  rintro ⟨⟨⟨a,b,c,d,e⟩,f⟩⟩,
  dsimp [from_relation] at f,
  rw e at f,
  have h := sym2.eq f,
  cases h,
  rw [h.1,h.2] at d, exact d,
  rw [h.1,h.2] at d, exact h₁ d,
end


def complete_graph (α : Type u) [decidable_eq α] : graph α :=
@graph.from_relation _ (λ x y, x ≠ y) (λ x y h, h.symm) (λ x : α, by simp)

def finite_complete_graph (n : ℕ) := complete_graph (fin n)

--
-- Finite graphs
--

instance finite_edge_set [fintype V] (g : graph V) : fintype g.E := sorry

def graph.nverts [fintype V] (g : graph V) := fintype.card V
def graph.nedges [fintype V] (g : graph V) := fintype.card g.E

end graph
