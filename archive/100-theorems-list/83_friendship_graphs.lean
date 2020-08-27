/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson, Jalex Stark.
-/
import combinatorics.adj_matrix
import linear_algebra.char_poly.coeff
import data.int.modeq
import data.zmod.basic
import tactic

open_locale classical big_operators
noncomputable theory

open finset simple_graph matrix

universes u v
variables {V : Type u} {R : Type v} [fintype V] [inhabited V] [semiring R]

section friendship_def
variables (G : simple_graph V)

/--
Given two vertices, a common friend is a vertex that is adjacent to both.
-/
def is_friend (v w : V) : V → Prop := λ u, G.adj v u ∧ G.adj w u

/--
This is the set of all friends between two vertices.
As characterized by `friends_eq_inter_neighbors`, it is the intersection
of their respective neighbor sets.
-/
def friends (v w : V) : finset V := univ.filter (is_friend G v w)

/--
This property of a graph is the hypothesis of the friendship theorem:
every pair of vertices has exactly one common friend.
-/
def friendship : Prop := ∀ ⦃v w : V⦄, v ≠ w → (friends G v w).card = 1

def exists_politician : Prop := ∃ (v : V), ∀ (w : V), v = w ∨ G.adj v w

lemma mem_friends {v w : V} {a : V} :
  a ∈ friends G v w ↔ is_friend G v w a :=
by { dunfold friends, simp }

lemma friends_eq_inter_neighbors {v w : V} :
  friends G v w = G.neighbor_finset v ∩ G.neighbor_finset w :=
by { ext, simp [friends, is_friend] }

end friendship_def

variables {G : simple_graph V} {d : ℕ} (hG : friendship G)
include hG

variables (R)
theorem friendship_adj_sq_apply_of_ne {v w : V} (hvw : v ≠ w) :
  ((G.adj_matrix R) ^ 2) v w = 1 :=
begin
  rw [pow_two, ← nat.cast_one, ← hG hvw, friends_eq_inter_neighbors],
  simp [neighbor_finset_eq_filter, finset.filter_filter, finset.filter_inter],
end

lemma friendship_adj_cube_apply_of_not_adj {v w : V} (non_adj : ¬ G.adj v w) :
  ((G.adj_matrix R) ^ 3) v w = degree G v :=
begin
  rw [pow_succ, mul_eq_mul, adj_matrix_mul_apply],
  dunfold degree, rw card_eq_sum_ones, rw sum_nat_cast,
  apply sum_congr rfl,
  intros x hx, rw [friendship_adj_sq_apply_of_ne, nat.cast_one], apply hG,
  intro contra, rw contra at hx, apply non_adj, rw mem_neighbor_finset at hx, apply hx,
end

variable {R}

lemma degree_eq_of_not_adj {v w : V} (hvw : ¬ G.adj v w) :
  degree G v = degree G w :=
begin
  by_cases h : v = w,
  { rw h },
  { have hv := friendship_adj_cube_apply_of_not_adj ℕ hG hvw,
    rw nat.cast_id at hv,
    rw [← hv, ← transpose_adj_matrix, pow_succ, pow_two],
    simp only [mul_eq_mul], repeat {rw ← transpose_mul},
    rw [transpose_apply, ← mul_eq_mul, ← mul_eq_mul, ← pow_two, ← pow_succ',
      friendship_adj_cube_apply_of_not_adj ℕ hG, nat.cast_id],
    rw G.edge_symm, apply hvw, },
end

theorem counter_reg (hG' : ¬exists_politician G) :
  ∃ (d : ℕ), G.is_regular_of_degree d :=
begin
  let v := arbitrary V,
  use G.degree v, intro x,
  by_cases hvx : G.adj v x,
    swap, { exact eq.symm (degree_eq_of_not_adj hG hvx), },
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
  have hx : x ∈ friends G v w := (mem_friends G).mpr ⟨hvx, G.sym hxw⟩,
  have hy : y ∈ friends G v w := (mem_friends G).mpr ⟨hvy, G.sym hcontra⟩,
  rw [h, mem_singleton] at hx hy,
  apply hxy',
  rw [hy, hx],
end

theorem friendship_reg_adj_sq (hd : G.is_regular_of_degree d) :
  ((G.adj_matrix R) ^ 2) = λ v w, ite (v = w) d 1 :=
begin
  ext, by_cases h : x = x_1,
  { cases h, rw [pow_two, mul_eq_mul, adj_matrix_mul_self_apply_self, hd], simp, },
  { rw [friendship_adj_sq_apply_of_ne R hG h, if_neg h], },
end

lemma friendship_reg_card (hd : G.is_regular_of_degree d) :
  d + (fintype.card V - 1) = d * d :=
begin
  let v := arbitrary V,
  transitivity ((G.adj_matrix ℕ) ^ 2).mul_vec (λ _, 1) v,
  { rw friendship_reg_adj_sq hG hd,
    dunfold mul_vec, dunfold dot_product,
    rw ← insert_erase (mem_univ v),
    simp only [sum_insert, mul_one, if_true, nat.cast_id, eq_self_iff_true,
               mem_erase, not_true, ne.def, not_false_iff, add_right_inj, false_and],
    rw [finset.sum_const_nat, card_erase_of_mem (mem_univ v), mul_one], refl,
    intros x hx, simp [(ne_of_mem_erase hx).symm], },
  { rw [pow_two, mul_eq_mul, ← mul_vec_mul_vec],
    simp [adj_matrix_mul_vec_const_apply_of_regular hd, neighbor_finset,
          card_neighbor_set_eq_degree, hd v], }
end

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
by { rw [friendship_reg_adj_sq hG hd, dmod], simp, }

lemma friendship_reg_adj_sq_mul_J (hd : G.is_regular_of_degree d) :
  (G.adj_matrix R) * (λ _ _, 1) = λ _ _, d :=
by { ext, rw ← hd x, simp [degree], }

lemma friendship_reg_adj_mul_J_mod_p {p : ℕ} (dmod : (d : zmod p) = 1) (hd : G.is_regular_of_degree d) :
  (G.adj_matrix (zmod p)) * (λ _ _, 1) = λ _ _, 1 :=
by rw [friendship_reg_adj_sq_mul_J hG hd, dmod]

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

lemma tr_pow_p_mod_p {p:ℕ} [fact p.prime] (M : matrix V V (zmod p)) :
  trace V (zmod p) (zmod p) (M ^ p) = (trace V (zmod p) (zmod p) M)^p :=
by rw [trace_eq_neg_char_poly_coeff, trace_eq_neg_char_poly_coeff,
       zmod.char_poly_pow_card, zmod.pow_card_eq_self]

/--
This is the main proof
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
  have := tr_pow_p_mod_p hG (G.adj_matrix (zmod p)),
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

lemma deg_le_one_friendship_has_pol (hd : G.is_regular_of_degree d) (hd1 : d ≤ 1) :
  exists_politician G :=
begin
  have sq : d * d = d := by { interval_cases d; norm_num },
  have h := friendship_reg_card hG hd,
  rw sq at h,
  have : fintype.card V ≤ 1,
  { cases fintype.card V,
    { exact zero_le _, },
    { have : n = 0,
      { rw [nat.succ_sub_succ_eq_sub, nat.sub_zero] at h,
        linarith },
      subst n, } },
  use arbitrary V, intro w, left,
  apply fintype.card_le_one_iff.mp this,
end

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
  dsimp [is_regular_of_degree, degree] at hd,
  rw hd,
end

lemma deg_two_friendship_has_pol (hd : G.is_regular_of_degree 2) :
  exists_politician G :=
begin
  have v := arbitrary V,
  use v, intro w,
  by_cases hvw : v = w,
  { left, exact hvw },
  { right,
    rw [← mem_neighbor_finset, deg_two_neighbor_finset_eq hG hd v, finset.mem_erase],
    exact ⟨ne.symm hvw, finset.mem_univ _⟩, },
end

lemma deg_le_two_friendship_has_pol (hd : G.is_regular_of_degree d) (h : d ≤ 2) :
  exists_politician G :=
begin
  interval_cases d,
  iterate 2 { apply deg_le_one_friendship_has_pol hG hd, norm_num },
  { exact deg_two_friendship_has_pol hG hd },
end

theorem friendship_theorem : exists_politician G :=
begin
  by_contradiction npG,
  rcases counter_reg hG npG with ⟨d, dreg⟩,
  have : d ≤ 2 ∨ 3 ≤ d := by omega,
  cases this,
  { refine npG (deg_le_two_friendship_has_pol hG dreg this) },
  { exact three_le_deg_friendship_contra hG dreg this },
end
#lint
