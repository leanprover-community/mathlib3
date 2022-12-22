/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.coloring
import data.polynomial.eval
import algebra.big_operators.basic
import order.upper_lower

/-!
# Chromatic polynomial

-/

open_locale big_operators
open_locale classical

namespace simple_graph
variables {V : Type*} (G : simple_graph V)

noncomputable
def chromatic_polynomial [fintype V] (R : Type*) [ring R] : polynomial R :=
∑ H in set.to_finset {H | H ≤ G},
  (-1) ^ fintype.card H.edge_set *
  polynomial.X ^ fintype.card H.connected_component

section intermediate

/-- In a spanning subgraph `G`, we imagine that we contract the edges in `H`.
For colorings, we have the following interpretations for the coloring constraints
between two vertices `v w : V`:
- if there is an edge of `H` between `v` and `w`, then `v` and `w` have the same color
- if there is an edge of `G \ H` between `v` and `w` then `v` and `w` have different colors
- otherwise, no constraints  -/
@[ext] structure del_contr (V : Type*) :=
(H : simple_graph V)
(G : simple_graph V)
(prop : H ≤ G)

@[ext] structure del_contr.coloring (D : del_contr V) (α : Type*) :=
(f : V → α)
(Hprop : ∀ (v w : V), D.H.adj v w → f v = f w)
(Gprop : ∀ (v w : V), ¬ D.H.adj v w → D.G.adj v w → f v ≠ f w)

noncomputable instance [fintype V] : fintype (del_contr V) :=
fintype.of_equiv {P : simple_graph V × simple_graph V // P.1 ≤ P.2}
{ to_fun := λ P, ⟨P.1.1, P.1.2, P.2⟩,
  inv_fun := λ (D : del_contr V), ⟨(D.H, D.G), D.prop⟩,
  left_inv := begin rintro ⟨⟨_, _⟩, _⟩, refl end,
  right_inv := begin rintro ⟨_, _, _⟩, refl end }

noncomputable instance [fintype V] {α : Type*} [fintype α] (D : del_contr V) :
  fintype (D.coloring α) :=
fintype.of_injective del_contr.coloring.f (by { intros c c' h, ext, rw h })

/-- Contract all the edges in the given edge set. -/
@[simps] def del_contr.contract (D : del_contr V) (s : set (sym2 V)) : del_contr V :=
{ H := D.H ⊔ simple_graph.from_edge_set s,
  G := D.G ⊔ simple_graph.from_edge_set s,
  prop := sup_le_sup_right D.prop (simple_graph.from_edge_set s) }

/-- Delete all the edges in the given edge set. -/
@[simps] def del_contr.delete (D : del_contr V) (s : set (sym2 V)) : del_contr V :=
{ H := D.H \ simple_graph.from_edge_set s,
  G := D.G \ simple_graph.from_edge_set s,
  prop := sdiff_le_sdiff_right D.prop }

lemma del_contr.delete_delete (D : del_contr V) (s s' : set (sym2 V)) :
  (D.delete s).delete s' = D.delete (s ∪ s') :=
begin
  ext; simp; tauto
end

lemma del_contr.contract_contract (D : del_contr V) (s s' : set (sym2 V)) :
  (D.contract s).contract s' = D.contract (s ∪ s') :=
begin
  ext; simp; tauto
end

noncomputable
def del_contr.chromatic_polynomial (D : del_contr V) [fintype V] (R : Type*) [ring R] :
  polynomial R :=
∑ H in set.to_finset {H | D.H ≤ H ∧ H ≤ D.G},
  (-1) ^ (fintype.card H.edge_set - fintype.card D.H.edge_set) *
  polynomial.X ^ fintype.card H.connected_component

lemma del_contr.chromatic_polynomial_eval (D : del_contr V) [fintype V]
  (R : Type*) [ring R] (α : Type*) [fintype α] :
  (D.chromatic_polynomial R).eval (fintype.card α) = fintype.card (D.coloring α) :=
begin
  sorry
end

lemma del_contr.chromatic_polynomial_graph [fintype V] (R : Type*) [ring R] :
  (del_contr.mk ⊥ G bot_le).chromatic_polynomial R = G.chromatic_polynomial R :=
begin
  sorry
end

def coloring_equiv_coloring (α : Type*) :
  G.coloring α ≃ (del_contr.mk ⊥ G bot_le).coloring α :=
{ to_fun := λ c,
  { f := c,
    Hprop := by simp,
    Gprop := λ v w h, c.valid },
  inv_fun := λ c', coloring.mk c'.f (by simpa using c'.Gprop),
  left_inv := begin
    rintro ⟨c, _⟩,
    refl,
  end,
  right_inv := begin
    rintro ⟨c, _⟩,
    refl,
  end }

end intermediate

lemma chromatic_polynomial_eval [fintype V] (R : Type*) [ring R] (α : Type*) [fintype α] :
  (G.chromatic_polynomial R).eval (fintype.card α) = fintype.card (G.coloring α) :=
begin
  rw ← del_contr.chromatic_polynomial_graph,
  rw del_contr.chromatic_polynomial_eval,
  congr' 1,
  rw fintype.card_eq,
  exact ⟨(coloring_equiv_coloring G α).symm⟩,
end

end simple_graph
