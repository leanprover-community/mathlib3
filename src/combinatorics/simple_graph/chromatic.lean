/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.coloring
import data.polynomial.eval
import algebra.big_operators.basic
import algebra.big_operators.ring
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

-- Direct calculation.
-- note: should be true for `[ring R]` as well since calculation takes place in center.
lemma chromatic_polynomial_eval [fintype V] (R : Type*) [comm_ring R] (α : Type*) [fintype α] :
  (G.chromatic_polynomial R).eval (fintype.card α) = fintype.card (G.coloring α) :=
begin
  symmetry,
  calc (fintype.card (G.coloring α) : R)
        = fintype.card {f : V → α // ∀ {v w : V}, G.adj v w → f v ≠ f w} : _
    ... = ∑ (f : V → α), ite (∀ {v w : V}, G.adj v w → f v ≠ f w) 1 0 : _
    ... = ∑ (f : V → α), ∏ e in G.edge_finset,
            sym2.lift ⟨λ v w, ite (v ≠ w) 1 0, by { intros, simp_rw ne_comm }⟩ e : _
    ... = ∑ (f : V → α), ∏ e in G.edge_finset,
            (1 - sym2.lift ⟨λ v w, ite (v = w) 1 0, by { intros, simp_rw eq_comm }⟩ e) : _
    ... = ∑ (f : V → α), ∑ A in G.edge_finset.powerset, ∏ e in A,
            (- sym2.lift ⟨λ v w, ite (v = w) 1 0, by { intros, simp_rw eq_comm }⟩ e) :
              by { refine finset.sum_congr rfl (λ f _, _),
                   simp_rw [sub_eq_add_neg, add_comm (1 : R)],
                   rw finset.prod_add,
                   refine finset.sum_congr rfl (λ t _, _),
                   rw [finset.prod_const_one, mul_one], }
    ... = ∑ (f : V → α), ∑ A in G.edge_finset.powerset, (-1) ^ A.card * ∏ e in A,
            sym2.lift ⟨λ v w, ite (v = w) 1 0, by { intros, simp_rw eq_comm }⟩ e : _
    ... = ∑ A in G.edge_finset.powerset, ∑ (f : V → α), (-1) ^ A.card * ∏ e in A,
            sym2.lift ⟨λ v w, ite (v = w) 1 0, by { intros, simp_rw eq_comm }⟩ e : _
    ... = ∑ A in G.edge_finset.powerset, (-1) ^ A.card * ∑ (f : V → α), ∏ e in A,
            sym2.lift ⟨λ v w, ite (v = w) 1 0, by { intros, simp_rw eq_comm }⟩ e : _
    ... = ∑ A in G.edge_finset.powerset, (-1) ^ A.card * ∑ (f : V → α),
            ite (∀ e ∈ A, sym2.lift ⟨λ v w, f v = f w,
              by { intros, rw [eq_iff_iff, eq_comm], }⟩ e) 1 0 : _
    ... = ∑ A in G.edge_finset.powerset, (-1) ^ A.card * ∑ (f : V → α),
            ite (∀ v w, ⟦(v, w)⟧ ∈ A → f v = f w) 1 0 : _
    ... = ∑ A in G.edge_finset.powerset, (-1) ^ A.card *
            fintype.card {f : V → α // ∀ v w, ⟦(v, w)⟧ ∈ A → f v = f w} : _
    ... = ∑ A in G.edge_finset.powerset, (-1) ^ A.card *
            fintype.card ((from_edge_set ↑A).connected_component → α) : _
    ... = ∑ A in G.edge_finset.powerset, (-1) ^ A.card *
            fintype.card α ^ fintype.card (from_edge_set ↑A).connected_component : _
    ... = ∑ H in set.to_finset {H | H ≤ G}, (-1) ^ G.edge_finset.card *
            fintype.card α ^ fintype.card H.connected_component : _
    ... = (G.chromatic_polynomial R).eval (fintype.card α) : _,
    all_goals { sorry }
end

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

lemma foo (D : del_contr V) (e : sym2 V) (he : e ∈ D.H.edge_set) :
  {H | D.H ≤ H ∧ H ≤ D.G} =
    {H | (D.delete {e}).H ≤ H ∧ H ≤ (D.delete {e}).G}
    ∪ {H | (D.contract {e}).H ≤ H ∧ H ≤ (D.contract {e}).G} :=
begin
  ext H,
  simp only [set.mem_set_of_eq, del_contr.delete_H, sdiff_le_iff, del_contr.delete_G,
    del_contr.contract_H, sup_le_iff, del_contr.contract_G, set.mem_union],
  simp_rw [← edge_set_subset_edge_set, edge_set_sup, edge_set_from_edge_set],
  --by_cases h : e ∈ H.edge_set,
  sorry
end

theorem del_contr.del_contr_rel (D : del_contr V) [fintype V] (R : Type*) [ring R]
  (e : sym2 V) (he : e ∈ D.H.edge_set) :
  D.chromatic_polynomial R =
    (D.delete {e}).chromatic_polynomial R - (D.contract {e}).chromatic_polynomial R :=
begin
  sorry
end

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

lemma chromatic_polynomial_eval' [fintype V] (R : Type*) [ring R] (α : Type*) [fintype α] :
  (G.chromatic_polynomial R).eval (fintype.card α) = fintype.card (G.coloring α) :=
begin
  rw ← del_contr.chromatic_polynomial_graph,
  rw del_contr.chromatic_polynomial_eval,
  congr' 1,
  rw fintype.card_eq,
  exact ⟨(coloring_equiv_coloring G α).symm⟩,
end

end simple_graph

-- this is finset.prod_add
lemma finset.prod_add' {α γ : Type*} [comm_ring γ] (f g : α → γ)
  (s : finset α) :
  (∏ x in s, (f x + g x)) = ∑ A in s.powerset, (∏ x in A, f x) * (∏ y in s \ A, g y) :=
begin
  classical,
  induction s using finset.induction with z s hz ih,
  { simp },
  { simp only [finset.sum_powerset_insert, hz, ih, finset.prod_insert, not_false_iff,
      finset.insert_sdiff_insert],
    rw [add_comm, add_mul],
    congr' 1,
    { rw finset.mul_sum,
      apply finset.sum_congr rfl,
      intros x hx,
      rw finset.mem_powerset at hx,
      rw [mul_comm, mul_assoc],
      congr' 1,
      rw finset.insert_sdiff_of_not_mem,
      swap, { intro h, exact hz (hx h), },
      rw [finset.prod_insert, mul_comm],
      simp [hz], },
    { rw finset.mul_sum,
      apply finset.sum_congr rfl,
      intros x hx,
      rw finset.mem_powerset at hx,
      rw finset.prod_insert,
      swap, { intro h, exact hz (hx h), },
      rw mul_assoc,
      congr' 2,
      congr' 1,
      rw finset.sdiff_insert_of_not_mem hz, } }
end
