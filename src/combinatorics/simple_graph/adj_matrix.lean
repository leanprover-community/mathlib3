/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Kyle Miller, Jalex Stark, Lu-Ming Zhang
-/
import algebra.indicator_function
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import data.rel
import linear_algebra.matrix.trace
import linear_algebra.matrix.symmetric

/-!
# Adjacency Matrices

This module defines the adjacency matrix of a graph, and provides theorems connecting graph
properties to computational properties of the matrix.

## Main definitions

* `matrix.is_adj_matrix`: `A : matrix V V α` is qualified as an "adjacency matrix" if
  (1) every entry of `A` is `0` or `1`,
  (2) `A` is symmetric,
  (3) every diagonal entry of `A` is `0`.

* `matrix.is_adj_matrix.to_graph`: for `A : matrix V V α` and `h : A.is_adj_matrix`,
  `h.to_graph` is the simple graph induced by `A`.

* `matrix.compl`: for `A : matrix V V α`, `A.compl` is supposed to be
  the adjacency matrix of the complement graph of the graph induced by `A`.

* `simple_graph.adj_matrix`: the adjacency matrix of a `simple_graph`.

-/

open_locale big_operators matrix
open finset matrix simple_graph

variables {V α β : Type*}

namespace matrix

/-- `A : matrix V V α` is qualified as an "adjacency matrix" if
    (1) every entry of `A` is `0` or `1`,
    (2) `A` is symmetric,
    (3) every diagonal entry of `A` is `0`. -/
structure is_adj_matrix [has_zero α] [has_one α] (A : matrix V V α) : Prop :=
(zero_or_one : ∀ i j, (A i j) = 0 ∨ (A i j) = 1 . obviously)
(symm : A.is_symm . obviously)
(apply_diag : ∀ i, A i i = 0 . obviously)

namespace is_adj_matrix

variables {A : matrix V V α}

@[simp]
lemma apply_diag_ne [mul_zero_one_class α] [nontrivial α] (h : is_adj_matrix A) (i : V) :
  ¬ A i i = 1 :=
by simp [h.apply_diag i]

@[simp]
lemma apply_ne_one_iff [mul_zero_one_class α] [nontrivial α] (h : is_adj_matrix A) (i j : V) :
  ¬ A i j = 1 ↔ A i j = 0 :=
by { obtain (h|h) := h.zero_or_one i j; simp [h] }

@[simp]
lemma apply_ne_zero_iff [mul_zero_one_class α] [nontrivial α] (h : is_adj_matrix A) (i j : V) :
  ¬ A i j = 0 ↔ A i j = 1 :=
by rw [←apply_ne_one_iff h, not_not]

/-- For `A : matrix V V α` and `h : is_adj_matrix A`,
    `h.to_graph` is the simple graph whose adjacency matrix is `A`. -/
@[simps]
def to_graph [mul_zero_one_class α] [nontrivial α] (h : is_adj_matrix A) :
  simple_graph V :=
{ adj := λ i j, A i j = 1,
  symm := λ i j hij, by rwa h.symm.apply i j,
  loopless := λ i, by simp [h] }

instance [mul_zero_one_class α] [nontrivial α] [decidable_eq α] (h : is_adj_matrix A) :
  decidable_rel h.to_graph.adj :=
by { simp only [to_graph], apply_instance }

end is_adj_matrix

/-- For `A : matrix V V α`, `A.compl` is supposed to be the adjacency matrix of
    the complement graph of the graph induced by `A.adj_matrix`. -/
def compl [has_zero α] [has_one α] [decidable_eq α] [decidable_eq V] (A : matrix V V α) :
  matrix V V α :=
λ i j, ite (i = j) 0 (ite (A i j = 0) 1 0)

section compl

variables [decidable_eq α] [decidable_eq V] (A : matrix V V α)

@[simp]
lemma compl_apply_diag [has_zero α] [has_one α] (i : V) :
  A.compl i i = 0 :=
by simp [compl]

@[simp]
lemma compl_apply [has_zero α] [has_one α] (i j : V) :
  A.compl i j = 0 ∨ A.compl i j = 1 :=
by { unfold compl, split_ifs; simp }

@[simp]
lemma is_symm_compl [has_zero α] [has_one α] (h : A.is_symm) :
  A.compl.is_symm :=
by { ext, simp [compl, h.apply, eq_comm] }

@[simp]
lemma is_adj_matrix_compl [has_zero α] [has_one α] (h : A.is_symm) :
  is_adj_matrix A.compl :=
{ symm := by simp [h] }

namespace is_adj_matrix

variable {A}

@[simp]
lemma compl [has_zero α] [has_one α] (h : is_adj_matrix A) :
  is_adj_matrix A.compl :=
is_adj_matrix_compl A h.symm

lemma to_graph_compl_eq [mul_zero_one_class α] [nontrivial α] (h : is_adj_matrix A) :
  h.compl.to_graph = (h.to_graph)ᶜ :=
begin
  ext v w,
  cases h.zero_or_one v w with h h;
  by_cases hvw : v = w;
  simp [matrix.compl, h, hvw]
end

end is_adj_matrix

end compl

end matrix

open matrix

namespace simple_graph

variables (G : simple_graph V) [decidable_rel G.adj]
variables (α)

/-- `adj_matrix G α` is the matrix `A` such that `A i j = (1 : α)` if `i` and `j` are
  adjacent in the simple graph `G`, and otherwise `A i j = 0`. -/
def adj_matrix [has_zero α] [has_one α] : matrix V V α
| i j := if (G.adj i j) then 1 else 0

variable {α}

@[simp]
lemma adj_matrix_apply (v w : V) [has_zero α] [has_one α] :
  G.adj_matrix α v w = if (G.adj v w) then 1 else 0 := rfl

@[simp]
theorem transpose_adj_matrix [has_zero α] [has_one α] :
  (G.adj_matrix α)ᵀ = G.adj_matrix α :=
by { ext, simp [adj_comm] }

@[simp]
lemma is_symm_adj_matrix [has_zero α] [has_one α] :
  (G.adj_matrix α).is_symm :=
transpose_adj_matrix G

variable (α)

/-- The adjacency matrix of `G` is an adjacency matrix. -/
@[simp]
lemma is_adj_matrix_adj_matrix [has_zero α] [has_one α] :
  (G.adj_matrix α).is_adj_matrix :=
{ zero_or_one := λ i j, by by_cases G.adj i j; simp [h] }

/-- The graph induced by the adjacency matrix of `G` is `G` itself. -/
lemma to_graph_adj_matrix_eq [mul_zero_one_class α] [nontrivial α] :
  (G.is_adj_matrix_adj_matrix α).to_graph = G :=
begin
  ext,
  simp only [is_adj_matrix.to_graph_adj, adj_matrix_apply, ite_eq_left_iff, zero_ne_one],
  apply not_not,
end

variables {α} [fintype V]

@[simp]
lemma adj_matrix_dot_product [non_assoc_semiring α] (v : V) (vec : V → α) :
  dot_product (G.adj_matrix α v) vec = ∑ u in G.neighbor_finset v, vec u :=
by simp [neighbor_finset_eq_filter, dot_product, sum_filter]

@[simp]
lemma dot_product_adj_matrix [non_assoc_semiring α] (v : V) (vec : V → α) :
  dot_product vec (G.adj_matrix α v) = ∑ u in G.neighbor_finset v, vec u :=
by simp [neighbor_finset_eq_filter, dot_product, sum_filter, finset.sum_apply]

@[simp]
lemma adj_matrix_mul_vec_apply [non_assoc_semiring α] (v : V) (vec : V → α) :
  ((G.adj_matrix α).mul_vec vec) v = ∑ u in G.neighbor_finset v, vec u :=
by rw [mul_vec, adj_matrix_dot_product]

@[simp]
lemma adj_matrix_vec_mul_apply [non_assoc_semiring α] (v : V) (vec : V → α) :
  ((G.adj_matrix α).vec_mul vec) v = ∑ u in G.neighbor_finset v, vec u :=
begin
  rw [← dot_product_adj_matrix, vec_mul],
  refine congr rfl _, ext,
  rw [← transpose_apply (adj_matrix α G) x v, transpose_adj_matrix],
end

@[simp]
lemma adj_matrix_mul_apply [non_assoc_semiring α] (M : matrix V V α) (v w : V) :
  (G.adj_matrix α ⬝ M) v w = ∑ u in G.neighbor_finset v, M u w :=
by simp [mul_apply, neighbor_finset_eq_filter, sum_filter]

@[simp]
lemma mul_adj_matrix_apply [non_assoc_semiring α] (M : matrix V V α) (v w : V) :
  (M ⬝ G.adj_matrix α) v w = ∑ u in G.neighbor_finset w, M v u :=
by simp [mul_apply, neighbor_finset_eq_filter, sum_filter, adj_comm]

variable (α)

theorem trace_adj_matrix [non_assoc_semiring α] [semiring β] [module β α]:
  matrix.trace _ β _ (G.adj_matrix α) = 0 :=
by simp

variable {α}

theorem adj_matrix_mul_self_apply_self [non_assoc_semiring α] (i : V) :
  ((G.adj_matrix α) ⬝ (G.adj_matrix α)) i i = degree G i :=
by simp [degree]

variable {G}

@[simp]
lemma adj_matrix_mul_vec_const_apply [semiring α] {a : α} {v : V} :
  (G.adj_matrix α).mul_vec (function.const _ a) v = G.degree v * a :=
by simp [degree]

lemma adj_matrix_mul_vec_const_apply_of_regular [semiring α] {d : ℕ} {a : α}
  (hd : G.is_regular_of_degree d) {v : V} :
  (G.adj_matrix α).mul_vec (function.const _ a) v = (d * a) :=
by simp [hd v]

section walks
variables (G) [decidable_eq V]

/-- The `finset` of length-`n` walks from `u` to `v`. -/
def walk_len : Π (n : ℕ) (u v : V), finset (G.walk u v)
| 0 u v := if h : u = v
           then by { subst u, exact {walk.nil} }
           else ∅
| (n+1) u v := finset.univ.bUnion (λ (w : V),
                 if h : G.adj u w
                 then (walk_len n w v).map ⟨λ p, walk.cons h p, begin
                     intros p q, simp,
                   end⟩
                 else ∅)

lemma walk_len_eq (n : ℕ) (u v : V) :
  ↑(G.walk_len n u v) = {p : G.walk u v | p.length = n} :=
begin
  induction n generalizing u v,
  { ext p,
    simp only [walk_len, nat.nat_zero_eq_zero, mem_coe, set.mem_set_of_eq],
    by_cases h : u = v,
    { subst h,
      cases p; simp },
    { cases p,
      simp,
      simp [h] } },
  { ext p,
    simp [walk_len],
    split,
    { rintro ⟨w, h⟩,
      by_cases huw : G.adj u w,
      { simp [huw] at h,
        obtain ⟨q, hq, rfl⟩ := h,
        simp [walk.length],
        rw [←finset.mem_coe, n_ih] at hq,
        exact hq },
      { simp [huw] at h,
        exact h.elim } },
    { intro hp,
      cases p,
      { exfalso,
        simp at hp,
        injection hp },
      { use p_v,
        simp [p_h],
        rw [←finset.mem_coe, n_ih],
        injection hp } } },
end

instance walk_of_len_fintype {u v : V} (n : ℕ) : fintype {p : G.walk u v // p.length = n} :=
begin
  apply fintype.subtype (G.walk_len n u v),
  intro p,
  rw ←finset.mem_coe,
  rw walk_len_eq,
  simp,
end

lemma fintype_card_walk_eq (u v : V) (n : ℕ) :
  (G.walk_len n u v).card = fintype.card {p : G.walk u v // p.length = n} :=
begin
  rw fintype.card_of_subtype (G.walk_len n u v),
  intro p,
  rw ←finset.mem_coe,
  rw walk_len_eq,
  simp,
end

theorem adj_matrix_pow_apply_eq_card_walk [semiring α] (n : ℕ) (u v : V) :
  (G.adj_matrix α ^ n) u v = fintype.card {p : G.walk u v // p.length = n} :=
begin
  rw ←fintype_card_walk_eq,
  induction n generalizing u v,
  { by_cases h : u = v,
    { subst h,
      simp [walk_len] },
    { simp [walk_len, h] } },
  { rw [nat.succ_eq_add_one, add_comm, pow_add, pow_one],
    simp only [adj_matrix_mul_apply, mul_eq_mul],
    rw set.sum_indicator_subset _ (subset_univ _),
    simp_rw [set.indicator_apply, mem_coe, mem_neighbor_finset, n_ih],
    rw add_comm,
    simp only [walk_len],
    rw finset.card_bUnion,
    { norm_cast,
      congr' 2,
      ext x,
      by_cases hux : G.adj u x,
      { simp [hux] },
      { simp [hux] } },
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
      exact (hxy (h_2.trans h_4.symm)).elim } },
end

end walks

end simple_graph

namespace matrix.is_adj_matrix
variables [mul_zero_one_class α] [nontrivial α]
variables {A : matrix V V α} (h : is_adj_matrix A)

/-- If `A` is qualified as an adjacency matrix,
    then the adjacency matrix of the graph induced by `A` is itself. -/
lemma adj_matrix_to_graph_eq [decidable_eq α] :
  h.to_graph.adj_matrix α = A :=
begin
  ext i j,
  obtain (h'|h') := h.zero_or_one i j; simp [h'],
end

end matrix.is_adj_matrix
