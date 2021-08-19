/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import data.rel
import linear_algebra.matrix.trace

/-!
# Adjacency Matrices

This module defines the adjacency matrix of a graph, and provides theorems connecting graph
properties to computational properties of the matrix.

## Main definitions

* `adj_matrix` is the adjacency matrix of a `simple_graph` with coefficients in a given semiring.

-/

open_locale big_operators matrix
open finset matrix simple_graph

universes u v
variables {α : Type u} [fintype α]
variables (R : Type v) [semiring R]

namespace simple_graph

variables (G : simple_graph α) (R) [decidable_rel G.adj]

/-- `adj_matrix G R` is the matrix `A` such that `A i j = (1 : R)` if `i` and `j` are
  adjacent in the simple graph `G`, and otherwise `A i j = 0`. -/
def adj_matrix : matrix α α R
| i j := if (G.adj i j) then 1 else 0

variable {R}

@[simp]
lemma adj_matrix_apply (v w : α) : G.adj_matrix R v w = if (G.adj v w) then 1 else 0 := rfl

@[simp]
theorem transpose_adj_matrix : (G.adj_matrix R)ᵀ = G.adj_matrix R :=
by { ext, simp [adj_comm] }

@[simp]
lemma adj_matrix_dot_product (v : α) (vec : α → R) :
  dot_product (G.adj_matrix R v) vec = ∑ u in G.neighbor_finset v, vec u :=
by simp [neighbor_finset_eq_filter, dot_product, sum_filter]

@[simp]
lemma dot_product_adj_matrix (v : α) (vec : α → R) :
  dot_product vec (G.adj_matrix R v) = ∑ u in G.neighbor_finset v, vec u :=
by simp [neighbor_finset_eq_filter, dot_product, sum_filter, finset.sum_apply]

@[simp]
lemma adj_matrix_mul_vec_apply (v : α) (vec : α → R) :
  ((G.adj_matrix R).mul_vec vec) v = ∑ u in G.neighbor_finset v, vec u :=
by rw [mul_vec, adj_matrix_dot_product]

@[simp]
lemma adj_matrix_vec_mul_apply (v : α) (vec : α → R) :
  ((G.adj_matrix R).vec_mul vec) v = ∑ u in G.neighbor_finset v, vec u :=
begin
  rw [← dot_product_adj_matrix, vec_mul],
  refine congr rfl _, ext,
  rw [← transpose_apply (adj_matrix R G) x v, transpose_adj_matrix],
end

@[simp]
lemma adj_matrix_mul_apply (M : matrix α α R) (v w : α) :
  (G.adj_matrix R ⬝ M) v w = ∑ u in G.neighbor_finset v, M u w :=
by simp [mul_apply, neighbor_finset_eq_filter, sum_filter]

@[simp]
lemma mul_adj_matrix_apply (M : matrix α α R) (v w : α) :
  (M ⬝ G.adj_matrix R) v w = ∑ u in G.neighbor_finset w, M v u :=
by simp [mul_apply, neighbor_finset_eq_filter, sum_filter, adj_comm]

variable (R)
theorem trace_adj_matrix : matrix.trace α R R (G.adj_matrix R) = 0 := by simp
variable {R}

theorem adj_matrix_mul_self_apply_self (i : α) :
  ((G.adj_matrix R) ⬝ (G.adj_matrix R)) i i = degree G i :=
by simp [degree]

variable {G}

@[simp]
lemma adj_matrix_mul_vec_const_apply {r : R} {v : α} :
  (G.adj_matrix R).mul_vec (function.const _ r) v = G.degree v * r :=
by simp [degree]

lemma adj_matrix_mul_vec_const_apply_of_regular {d : ℕ} {r : R} (hd : G.is_regular_of_degree d)
  {v : α} :
  (G.adj_matrix R).mul_vec (function.const _ r) v = (d * r) :=
by simp [hd v]

section walks
variables (G) [decidable_eq α]

/-- The `finset` of length-`n` walks from `u` to `v`. -/
def walk_len : Π (n : ℕ) (u v : α), finset (G.walk u v)
| 0 u v := if h : u = v
           then by { subst u, exact {walk.nil}, }
           else ∅
| (n+1) u v := finset.univ.bUnion (λ (w : α),
                 if h : G.adj u w
                 then (walk_len n w v).map ⟨λ p, walk.cons h p, begin
                     intros p q, simp,
                   end⟩
                 else ∅)

lemma walk_len_eq (n : ℕ) (u v : α) :
  ↑(G.walk_len n u v) = {p : G.walk u v | p.length = n} :=
begin
  induction n generalizing u v,
  { ext p,
    simp only [walk_len, nat.nat_zero_eq_zero, mem_coe, set.mem_set_of_eq],
    by_cases h : u = v,
    { subst h,
      cases p; simp, },
    { cases p,
      simp,
      simp [h], }, },
  { ext p,
    simp [walk_len],
    split,
    { rintro ⟨w, h⟩,
      by_cases huw : G.adj u w,
      { simp [huw] at h,
        obtain ⟨q, hq, rfl⟩ := h,
        simp [walk.length],
        rw [←finset.mem_coe, n_ih] at hq,
        exact hq, },
      { simp [huw] at h,
        exact h.elim, }, },
    { intro hp,
      cases p,
      { exfalso,
        simp at hp,
        injection hp, },
      { use p_v,
        simp [p_h],
        rw [←finset.mem_coe, n_ih],
        injection hp, }, }, },
end

instance walk_of_len_fintype {u v : α} (n : ℕ) : fintype {p : G.walk u v // p.length = n} :=
begin
  apply fintype.subtype (G.walk_len n u v),
  intro p,
  rw ←finset.mem_coe,
  rw walk_len_eq,
  simp,
end

lemma fintype_card_walk_eq (u v : α) (n : ℕ) :
  (G.walk_len n u v).card = fintype.card {p : G.walk u v // p.length = n} :=
begin
  rw fintype.card_of_subtype (G.walk_len n u v),
  intro p,
  rw ←finset.mem_coe,
  rw walk_len_eq,
  simp,
end

lemma extend_by_zero' {α β : Type*} [fintype α] [add_comm_monoid β]
  (s : finset α) [decidable_pred (∈ s)] (f : α → β) :
  ∑ i in s, f i = ∑ (i : α), if i ∈ s then f i else 0 :=
begin
  classical,
  convert finset.sum_add_sum_compl s _,
  have : filter (λ (i : α), i ∈ s) sᶜ = ∅,
  { ext, simp, },
  simp [finset.sum_ite, this],
end

theorem adj_matrix_pow_apply_eq_card_walk (n : ℕ) (u v : α) :
  (G.adj_matrix R ^ n) u v = fintype.card {p : G.walk u v // p.length = n} :=
begin
  rw ←fintype_card_walk_eq,
  induction n generalizing u v,
  { by_cases h : u = v,
    { subst h,
      simp [walk_len], },
    { simp [walk_len, h], }, },
  { rw [nat.succ_eq_add_one, add_comm, pow_add, pow_one],
    simp only [adj_matrix_mul_apply, mul_eq_mul],
    rw [extend_by_zero'],
    simp only [n_ih, mem_neighbor_finset],
    rw add_comm,
    simp only [walk_len],
    rw finset.card_bUnion,
    { norm_cast,
      congr' 2,
      ext x,
      by_cases hux : G.adj u x,
      { simp [hux], },
      { simp [hux], }, },
    { intros x hx y hy hxy,
      intros p hp,
      simp at hp,
      split_ifs at hp;
      simp at hp; try { exact hp.elim },
      obtain ⟨⟨qx, hql, hqp⟩, ⟨rx, hrl, hrp⟩⟩ := hp,
      cases p,
      injection hqp,
      injection hqp,
      injection hrp,
      exact (hxy (h_2.trans h_4.symm)).elim, }, },
end

end walks

end simple_graph
