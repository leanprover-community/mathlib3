/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson, Jalex Stark, Kyle Miller.
-/
import combinatorics.adj_matrix
import linear_algebra.char_poly.coeff
import data.int.modeq
import data.zmod.basic
import tactic

/-!
# The Friendship Theorem

## Definitions and Statement
- A `friendship` graph is one in which any two distinct vertices have exactly one neighbor in common
- A `politician`, at least in the context of this problem, is a vertex in a graph which is adjacent
  to every other vertex.
- The friendship theorem (Erdős, Rényi, Sós 1966) states that every finite friendship graph has a
  politician.

## Proof outline
The proof revolves around the theory of adjacency matrices.
- Assume `G` is a finite friendship graph.
- First we show that any two nonadjacent vertices have the same degree
- Assume for contradiction that `G` does not have a politician.
- Conclude from the last two points that `G` is `d`-regular for some `d : ℕ`.
- Show that `G` has `d ^ 2 - d + 1` vertices.
- By casework, show that if `d = 0, 1, 2`, then `G` has a politician.
- If `3 ≤ d`, let `p` be a prime factor of `d - 1`.
- If `A` is the adjacency matrix of `G` with entries in `ℤ/pℤ`, we show that `A ^ p` has trace `1`.
- This gives a contradiction, as `A` has trace `0`, and thus `A ^ p` has trace `0`.

-/

open_locale classical big_operators
noncomputable theory

open finset simple_graph matrix

universes u v
variables {V : Type u} {R : Type v} [semiring R]

section friendship_def
variables (G : simple_graph V)

/--
This is the set of all vertices mutually adjacent to a pair of vertices.
-/
def common_friends [fintype V] (v w : V) : finset V := G.neighbor_finset v ∩ G.neighbor_finset w

/--
This property of a graph is the hypothesis of the friendship theorem:
every pair of vertices has exactly one common friend.
-/
def friendship [fintype V] : Prop := ∀ ⦃v w : V⦄, v ≠ w → (common_friends G v w).card = 1

/--
A politician is a vertex that is adjacent to all other vertices.
-/
def exists_politician : Prop := ∃ (v : V), ∀ (w : V), v ≠ w → G.adj v w

lemma mem_common_friends [fintype V] {v w : V} {a : V} :
  a ∈ common_friends G v w ↔ G.adj v a ∧ G.adj w a :=
by simp [common_friends]

end friendship_def

variables [fintype V] [inhabited V] {G : simple_graph V} {d : ℕ} (hG : friendship G)
include hG

variables (R)
/-- Another characterization of a friendship graph is that there is exactly one path of length 2
  between distinct vertices. These paths are counted in off-diagonal entries of the square of
  the adjacency matrix, so for a friendship graph, those entries are all 1. -/
theorem friendship_adj_sq_apply_of_ne {v w : V} (hvw : v ≠ w) :
  ((G.adj_matrix R) ^ 2) v w = 1 :=
begin
  rw [pow_two, ← nat.cast_one, ← hG hvw],
  simp [common_friends, neighbor_finset_eq_filter, finset.filter_filter, finset.filter_inter],
end

/-- This calculation amounts to counting the number of length 3 paths between nonadjacent vertices.
  We use it to show that nonadjacent vertices have equal degrees. -/
lemma friendship_adj_cube_apply_of_not_adj {v w : V} (non_adj : ¬ G.adj v w) :
  ((G.adj_matrix R) ^ 3) v w = degree G v :=
begin
  rw [pow_succ, mul_eq_mul, adj_matrix_mul_apply, degree, card_eq_sum_ones, sum_nat_cast],
  apply sum_congr rfl,
  intros x hx,
  rw [friendship_adj_sq_apply_of_ne _ hG, nat.cast_one],
  rintro ⟨rfl⟩,
  rw mem_neighbor_finset at hx,
  apply non_adj hx,
end

variable {R}

/-- The number of length 3 paths between `v` and `w` is the same as the number
  of paths between `w` and `v`, and this is encoded in the fact that the cube of the
  adjacency matrix is symmetric.
  Given our previous lemma, this means the degrees of nonadjacent vertices are also equal. -/
lemma degree_eq_of_not_adj {v w : V} (hvw : ¬ G.adj v w) :
  degree G v = degree G w :=
begin
  rw [← nat.cast_id (G.degree v), ← nat.cast_id (G.degree w),
        ← friendship_adj_cube_apply_of_not_adj ℕ hG hvw,
        ← friendship_adj_cube_apply_of_not_adj ℕ hG (λ h, hvw (G.sym h))],
    conv_lhs {rw ← transpose_adj_matrix},
    simp only [pow_succ, pow_two, mul_eq_mul, ← transpose_mul, transpose_apply],
    simp only [← mul_eq_mul, mul_assoc],
end

/-- If there does not exist a politician, then a friendship graph is regular. We already know that
  nonadjacent vertices have the same degree, and if there isn't a politician, we can show this for
  adjacent vertices by finding a vertex neither is adjacent to and using transitivity. -/
theorem counter_reg (hG' : ¬exists_politician G) :
  ∃ (d : ℕ), G.is_regular_of_degree d :=
begin
  have v := arbitrary V,
  use G.degree v,
  intro x,
  by_cases hvx : G.adj v x, swap, { exact eq.symm (degree_eq_of_not_adj hG hvx), },
  dunfold exists_politician at hG',
  push_neg at hG',
  rcases hG' v with ⟨w, hvw', hvw⟩,
  rcases hG' x with ⟨y, hxy', hxy⟩,
  by_cases hxw : G.adj x w,
    swap, { rw degree_eq_of_not_adj hG hvw, apply degree_eq_of_not_adj hG hxw },
  rw degree_eq_of_not_adj hG hxy,
  by_cases hvy : G.adj v y,
    swap, { apply eq.symm (degree_eq_of_not_adj hG hvy) },
  rw degree_eq_of_not_adj hG hvw,
  apply degree_eq_of_not_adj hG,
  intro hcontra,
  rcases finset.card_eq_one.mp (hG hvw') with ⟨a, h⟩,
  have hx : x ∈ common_friends G v w := (mem_common_friends G).mpr ⟨hvx, G.sym hxw⟩,
  have hy : y ∈ common_friends G v w := (mem_common_friends G).mpr ⟨hvy, G.sym hcontra⟩,
  rw [h, mem_singleton] at hx hy,
  apply hxy',
  rw [hy, hx],
end

/-- Knowing that a graph is a friendship graph determines the off-diagonal elements of the
  square of its adjacency matrix, and knowing the graph is `d`-regular determines the diagonal.  -/
theorem friendship_reg_adj_sq (hd : G.is_regular_of_degree d) :
  ((G.adj_matrix R) ^ 2) = λ v w, if v = w then d else 1 :=
begin
  ext v w, by_cases h : v = w,
  { rw [h, pow_two, mul_eq_mul, adj_matrix_mul_self_apply_self, hd], simp, },
  { rw [friendship_adj_sq_apply_of_ne R hG h, if_neg h], },
end

/-- We can compute the size of a `d`-regular friendship graph by applying the square of the
  adjacency matrix to a constant vector, and computing the result two different ways. -/
lemma friendship_reg_card (hd : G.is_regular_of_degree d) :
  d + (fintype.card V - 1) = d * d :=
begin
  let v := arbitrary V,
  transitivity ((G.adj_matrix ℕ) ^ 2).mul_vec (λ _, 1) v,
  { rw [friendship_reg_adj_sq hG hd, mul_vec, dot_product, ← insert_erase (mem_univ v)],
    simp only [sum_insert, mul_one, if_true, nat.cast_id, eq_self_iff_true,
               mem_erase, not_true, ne.def, not_false_iff, add_right_inj, false_and],
    rw [finset.sum_const_nat, card_erase_of_mem (mem_univ v), mul_one], refl,
    intros x hx, simp [(ne_of_mem_erase hx).symm], },
  { rw [pow_two, mul_eq_mul, ← mul_vec_mul_vec],
    simp [adj_matrix_mul_vec_const_apply_of_regular hd, neighbor_finset,
          card_neighbor_set_eq_degree, hd v], }
end

/-- The size of a `d`-regular friendship graph is `1 mod (d-1)`, and also `1 mod p` for a
  factor `p ∣ d-1`. -/
lemma friendship_reg_card_mod_p {p : ℕ} (dmod : (d : zmod p) = 1) (hd : G.is_regular_of_degree d) :
  (fintype.card V : zmod p) = 1 :=
begin
  have hpos : 0 < (fintype.card V),
  { rw fintype.card_pos_iff, apply_instance, },
  rw [← nat.succ_pred_eq_of_pos hpos, nat.succ_eq_add_one, nat.pred_eq_sub_one],
  simp only [add_left_eq_self, nat.cast_add, nat.cast_one],
  have h := congr_arg (λ n, (↑n : zmod p)) (friendship_reg_card hG hd),
  revert h, simp [dmod],
end

lemma friendship_reg_adj_sq_mod_p {p : ℕ} (dmod : (d : zmod p) = 1) (hd : G.is_regular_of_degree d) :
  (G.adj_matrix (zmod p)) ^ 2 = λ _ _, 1 :=
by simp [friendship_reg_adj_sq hG hd, dmod]

lemma friendship_reg_adj_sq_mul_J (hd : G.is_regular_of_degree d) :
  (G.adj_matrix R) * (λ _ _, 1) = λ _ _, d :=
by { ext x, simp [← hd x, degree] }

lemma friendship_reg_adj_mul_J_mod_p {p : ℕ} (dmod : (d : zmod p) = 1) (hd : G.is_regular_of_degree d) :
  (G.adj_matrix (zmod p)) * (λ _ _, 1) = λ _ _, 1 :=
by rw [friendship_reg_adj_sq_mul_J hG hd, dmod]

/-- When you mod out by a factor of `d-1`, the square and all higher powers of the adjacency matrix
  of a `d`-regular friendship graph reduce to the matrix whose entries are all 1. -/
lemma friendship_reg_adj_pow_mod_p {p : ℕ} (dmod : (d : zmod p) = 1) (hd : G.is_regular_of_degree d)
{k : ℕ} (hk : 2 ≤ k) :
  (G.adj_matrix (zmod p)) ^ k = λ _ _, 1 :=
begin
  iterate 2 {cases k with k, { exfalso, linarith, }, },
  induction k with k hind,
  apply friendship_reg_adj_sq_mod_p hG dmod hd,
  rw pow_succ,
  have h2 : 2 ≤ k.succ.succ := by omega,
  rw hind h2,
  apply friendship_reg_adj_mul_J_mod_p hG dmod hd,
end

/-- This is the main proof. Assuming that `3 ≤ d`, we take `p` to be a prime factor of `d-1`.
  Then the `p`th power of the adjacency matrix of a `d`-regular friendship graph must have trace 1
  mod `p`, but we can also show that the trace must be the `p`th power of the trace of the original
  adjacency matrix, which is 0.
-/
lemma three_le_deg_friendship_contra
  (hd : G.is_regular_of_degree d) (h : 3 ≤ d) : false :=
begin
  -- get a prime factor of d - 1
  let p : ℕ := (d - 1).min_fac,
  have p_dvd_d_pred := (zmod.nat_coe_zmod_eq_zero_iff_dvd _ _).mpr (d - 1).min_fac_dvd,
  have dpos : 0 < d := by linarith,
  have d_cast : ↑(d - 1) = (d : ℤ) - 1 := by norm_cast,
  haveI : fact p.prime := nat.min_fac_prime (by linarith),
  have hp2 : 2 ≤ p, { apply nat.prime.two_le, assumption },
  have dmod : (d : zmod p) = 1,
  { rw [← nat.succ_pred_eq_of_pos dpos, nat.succ_eq_add_one, nat.pred_eq_sub_one],
    simp only [add_left_eq_self, nat.cast_add, nat.cast_one], apply p_dvd_d_pred, },
  have Vmod := friendship_reg_card_mod_p hG dmod hd,
  -- now we reduce to a trace calculation
  have := zmod.trace_pow_card (G.adj_matrix (zmod p)),
  contrapose! this, clear this,
  -- the trace is 0 mod p when computed one way
  rw [trace_adj_matrix, zero_pow],
  -- but the trace is 1 mod p when computed the other way
  rw friendship_reg_adj_pow_mod_p hG dmod hd hp2,
  swap, { apply nat.prime.pos, assumption, },
  { dunfold fintype.card at Vmod,
    simp only [matrix.trace, diag_apply, mul_one, nsmul_eq_mul, linear_map.coe_mk, sum_const],
    rw [Vmod, ← nat.cast_one, zmod.nat_coe_zmod_eq_zero_iff_dvd, nat.dvd_one, nat.min_fac_eq_one_iff],
    linarith, },
end

/-- If `d ≤ 1`, a `d`-regular friendship graph has at most one vertex, which is
  trivially a politician. -/
lemma deg_le_one_friendship_has_pol (hd : G.is_regular_of_degree d) (hd1 : d ≤ 1) :
  exists_politician G :=
begin
  have sq : d * d = d := by { interval_cases d; norm_num },
  have h := friendship_reg_card hG hd,
  rw sq at h,
  have : fintype.card V ≤ 1,
  { cases fintype.card V with n,
    { exact zero_le _, },
    { have : n = 0,
      { rw [nat.succ_sub_succ_eq_sub, nat.sub_zero] at h,
        linarith },
      subst n, } },
  use arbitrary V, intros w h,
  exfalso, apply h,
  apply fintype.card_le_one_iff.mp this,
end

/-- If `d = 2`, a `d`-regular friendship graph has 3 vertices, so it must be complete graph,
  and all the vertices are politicians. -/
lemma deg_two_neighbor_finset_eq (hd : G.is_regular_of_degree 2) (v : V) :
  G.neighbor_finset v = finset.univ.erase v :=
begin
  apply finset.eq_of_subset_of_card_le,
  { rw finset.subset_iff,
    intro x,
    rw [mem_neighbor_finset, finset.mem_erase],
    exact λ h, ⟨ne.symm (G.ne_of_adj h), finset.mem_univ _⟩ },
  convert_to 2 ≤ _,
  convert_to _ = fintype.card V - 1,
  { have hfr:= friendship_reg_card hG hd,
    linarith },
  { exact finset.card_erase_of_mem (finset.mem_univ _), },
  { dsimp [is_regular_of_degree, degree] at hd,
    rw hd, }
end

lemma deg_two_friendship_has_pol (hd : G.is_regular_of_degree 2) :
  exists_politician G :=
begin
  have v := arbitrary V,
  use v, intros w hvw,
  rw [← mem_neighbor_finset, deg_two_neighbor_finset_eq hG hd v, finset.mem_erase],
  exact ⟨ne.symm hvw, finset.mem_univ _⟩,
end

lemma deg_le_two_friendship_has_pol (hd : G.is_regular_of_degree d) (h : d ≤ 2) :
  exists_politician G :=
begin
  interval_cases d,
  iterate 2 { apply deg_le_one_friendship_has_pol hG hd, norm_num },
  { exact deg_two_friendship_has_pol hG hd },
end

/-- We know that a friendship graph has a politician or is regular, so we assume it's regular.
  If the degree is at most 2, we observe by casework that it has a politician anyway.
  If the degree is at least 3, the graph cannot exist. -/
theorem friendship_theorem : exists_politician G :=
begin
  by_contradiction npG,
  rcases counter_reg hG npG with ⟨d, dreg⟩,
  have h : d ≤ 2 ∨ 3 ≤ d := by omega,
  cases h with dle2 dge3,
  { refine npG (deg_le_two_friendship_has_pol hG dreg dle2) },
  { exact three_le_deg_friendship_contra hG dreg dge3 },
end
