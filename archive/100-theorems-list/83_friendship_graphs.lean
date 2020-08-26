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

def is_friend (v w : V) (u : V) : Prop := G.adj v u ∧ G.adj w u

def friends  (v w : V) : finset V := finset.filter (is_friend G v w) finset.univ

def friendship : Prop := ∀ v w : V, v ≠ w → ∃!(u : V), is_friend G v w u

def exists_politician : Prop := ∃ v : V, ∀ w : V, v = w ∨ G.adj v w

def no_pol : Prop := ∀ v : V, ∃ w : V, v ≠ w ∧ ¬ G.adj v w

lemma exists_pol_of_not_no_pol :
  (¬ no_pol G) ↔ exists_politician G :=
begin
  unfold no_pol exists_politician, simp only [not_exists, not_and, not_not, ne.def, not_forall],
  apply exists_congr, intro v, apply forall_congr, intro w, tauto,
end

end friendship_def

variables {G : simple_graph V} {d : ℕ} (hG : friendship G)
include hG

lemma friends_eq_inter_neighbors {v w : V} :
  friends G v w = G.neighbor_finset v ∩ G.neighbor_finset w:=
by { ext, erw finset.mem_filter, simp [is_friend] }

lemma card_friends {v w : V} (hvw : v ≠ w) :
  (friends G v w).card = 1 :=
begin
  rw [finset.card_eq_one, finset.singleton_iff_unique_mem],
  suffices : exists_unique (is_friend G v w), { simpa [friends] },
  use fintype.choose (is_friend G v w) (hG v w hvw),
  split, { apply fintype.choose_spec },
  intros x hx,
  apply exists_unique.unique (hG v w hvw) hx,
  apply fintype.choose_spec,
end

variables (R)
theorem friendship_adj_sq_apply_of_ne
   {v w : V} (hvw : v ≠ w) :
((G.adj_matrix R)^2) v w = 1 :=
begin
  rw [pow_two, ← nat.cast_one, ← card_friends hG hvw,
    friends_eq_inter_neighbors hG],
  simp [neighbor_finset_eq_filter, finset.filter_filter, finset.filter_inter],
end

lemma friendship_adj_cube_apply_of_not_adj {v w : V} (non_adj : ¬ G.adj v w) :
  ((G.adj_matrix R) ^ 3) v w = degree G v :=
begin
  rw [pow_succ, mul_eq_mul, adj_matrix_mul_apply], unfold degree, rw card_eq_sum_ones, rw sum_nat_cast,
  apply sum_congr rfl,
  intros x hx, rw friendship_adj_sq_apply_of_ne, rw nat.cast_one, apply hG,
  intro contra, rw contra at hx, apply non_adj, rw mem_neighbor_finset at hx, apply hx,
end

variable {R}

lemma degree_eq_of_not_adj {v w : V} (hvw : ¬ G.adj v w) :
degree G v = degree G w :=
begin
  by_cases v = w, { rw h },

  have hv := friendship_adj_cube_apply_of_not_adj ℕ hG hvw, rw nat.cast_id at hv,
  rw [← hv, ← transpose_adj_matrix, pow_succ, pow_two],
  simp only [mul_eq_mul], repeat {rw ← transpose_mul},
  rw [transpose_apply, ← mul_eq_mul, ← mul_eq_mul, ← pow_two, ← pow_succ',
    friendship_adj_cube_apply_of_not_adj ℕ hG, nat.cast_id],
  rw G.edge_symm, apply hvw,
end

theorem counter_reg (hG' : no_pol G) :
∃ d:ℕ, G.is_regular_of_degree d :=
begin
  have np:=hG',
  have v := arbitrary V,
  use degree G v,
  intro x,
  by_cases hvx : G.adj v x,
    swap, symmetry, apply degree_eq_of_not_adj hG hvx,

  rcases hG' v with ⟨w, hvw', hvw⟩,
  rcases hG' x with ⟨y, hxy', hxy⟩,
  have degvw:= degree_eq_of_not_adj hG hvw,
  have degxy:= degree_eq_of_not_adj hG hxy,
  by_cases hxw : G.adj x w,
    swap, {rw degvw, apply degree_eq_of_not_adj hG hxw},
  rw degxy,
  by_cases hvy : G.adj v y,
    swap, {symmetry, apply degree_eq_of_not_adj hG hvy},
  rw degvw,
  apply degree_eq_of_not_adj hG,
  intro hcontra,
  apply hxy',
  apply exists_unique.unique (hG v w hvw'),
  exact ⟨hvx, G.sym hxw⟩,
  exact ⟨hvy, G.sym hcontra⟩,
end

theorem friendship_reg_adj_sq (hd : G.is_regular_of_degree d) :
((G.adj_matrix R) ^ 2) = λ v w, ite (v = w) d 1 :=
begin
  ext, by_cases h : x = x_1,
  { cases h, rw [pow_two, mul_eq_mul, adj_matrix_mul_self_apply_self, hd], simp, },
  rw [friendship_adj_sq_apply_of_ne R hG h, if_neg h],
end

lemma friendship_reg_card (hd : G.is_regular_of_degree d) :
  d + (fintype.card V - 1) = d * d :=
begin
  let v := arbitrary V,
  transitivity ((G.adj_matrix ℕ)^2).mul_vec (λ _, 1) v,
  { rw friendship_reg_adj_sq hG hd, unfold mul_vec, unfold dot_product,
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
  have hpos : 0 < (fintype.card V), rw fintype.card_pos_iff, apply_instance,
  rw ← nat.succ_pred_eq_of_pos hpos, rw nat.succ_eq_add_one, rw nat.pred_eq_sub_one,
  simp only [add_left_eq_self, nat.cast_add, nat.cast_one],
  have h := friendship_reg_card hG hd, apply_fun (coe : ℕ → zmod p) at h,
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
  {k : ℕ} (hk : 2 ≤ k):
(G.adj_matrix (zmod p)) ^ k = λ _ _, 1 :=
begin
  iterate 2 {cases k with k, { exfalso, linarith,},},
  induction k with k hind, apply friendship_reg_adj_sq_mod_p hG dmod hd,
  rw pow_succ,
  have h2 : 2 ≤ k.succ.succ := by omega,
  rw hind h2,
  apply friendship_reg_adj_mul_J_mod_p hG dmod hd,
end

lemma tr_pow_p_mod_p {p:ℕ} [fact p.prime] (M : matrix V V (zmod p)) :
trace V (zmod p) (zmod p) (M ^ p) = (trace V (zmod p) (zmod p) M)^p :=
by rw [trace_eq_neg_char_poly_coeff, trace_eq_neg_char_poly_coeff,
  char_poly_pow_p_char_p, frobenius_fixed]

-- this is the main proof
lemma three_le_deg_friendship_contra
  (hd : G.is_regular_of_degree d) (h : 3 ≤ d) : false :=
begin
  -- get a prime factor of d - 1
  let p : ℕ := (d - 1).min_fac,
  have p_dvd_d_pred := (d - 1).min_fac_dvd, rw ← zmod.nat_coe_zmod_eq_zero_iff_dvd at p_dvd_d_pred,
  have dpos : 0 < d := by linarith,
  have d_cast : coe (d - 1) = (d : ℤ) - 1 := by norm_cast,
  haveI : fact p.prime := nat.min_fac_prime (by linarith),
  have hp2 : 2 ≤ p, { apply nat.prime.two_le, assumption },

  have dmod : (d : zmod p) = 1,
  { rw ← nat.succ_pred_eq_of_pos dpos, rw nat.succ_eq_add_one, rw nat.pred_eq_sub_one,
  simp only [add_left_eq_self, nat.cast_add, nat.cast_one], apply p_dvd_d_pred, },
  have Vmod := friendship_reg_card_mod_p hG dmod hd,
  -- now we reduce to a trace calculation
  have := tr_pow_p_mod_p hG (G.adj_matrix (zmod p)), contrapose! this, clear this,
  -- the trace is 0 mod p when computed one way
  rw [trace_adj_matrix, zero_pow],
  -- but the trace is 1 mod p when computed the other way
  rw friendship_reg_adj_pow_mod_p hG dmod hd hp2, swap, apply nat.prime.pos, apply _inst,
  simp only [matrix.trace, diag_apply, mul_one, nsmul_eq_mul, linear_map.coe_mk, sum_const],
  unfold fintype.card at Vmod, rw Vmod, rw ← nat.cast_one, rw zmod.nat_coe_zmod_eq_zero_iff_dvd,
  simp only [nat.dvd_one, nat.min_fac_eq_one_iff], linarith,
end

lemma deg_le_one_friendship_has_pol
  (hd : G.is_regular_of_degree d) (hd1 : d ≤ 1) :
exists_politician G :=
begin
  have sq : d * d = d := by {interval_cases d; norm_num},
  have h := friendship_reg_card hG hd, rw sq at h,
  suffices : fintype.card V ≤ 1,
  { rw fintype.card_le_one_iff at this, use arbitrary V, intro w, left, apply this },
  cases fintype.card V, { simp },
  suffices : n = 0, { simp [this] },
  simp at h; linarith,
end

lemma deg_two_friendship_has_pol (hd : G.is_regular_of_degree 2) :
exists_politician G :=
begin
  have v := arbitrary V,
  have hfr:=friendship_reg_card hG hd,
  have h2 : fintype.card V - 1 = 2 := by linarith, clear hfr,

  have herase : (finset.univ.erase v).card = fintype.card V - 1,
  { apply finset.card_erase_of_mem,
    apply finset.mem_univ },
  rw h2 at herase, clear h2,

  existsi v, intro w,
  by_cases hvw : v = w, { left, exact hvw }, right,

  have h': G.neighbor_finset v = finset.univ.erase v,
  apply finset.eq_of_subset_of_card_le,
  { rw finset.subset_iff,
    intro x,
    rw [mem_neighbor_finset, finset.mem_erase],
    intro h,
    split, { symmetry, exact G.ne_of_adj h },
    apply finset.mem_univ },

  { rw herase,
    unfold is_regular_of_degree at hd, unfold degree at hd,
    rw hd },

  rw [← mem_neighbor_finset, h', finset.mem_erase],
  split, { symmetry, exact hvw },
  apply finset.mem_univ
end

lemma deg_le_two_friendship_has_pol (hd : G.is_regular_of_degree d) :
d ≤ 2 → exists_politician G:=
begin
  intro, interval_cases d,
  iterate 2 { apply deg_le_one_friendship_has_pol hG hd, norm_num },
  { exact deg_two_friendship_has_pol hG hd },
end

theorem friendship_theorem : exists_politician G :=
begin
  rw ← exists_pol_of_not_no_pol,
  intro npG,
  have regG : ∃ (d:ℕ), G.is_regular_of_degree d,
  { apply counter_reg; assumption },
  cases regG with d dreg,

  have : d ≤ 2 ∨ 3 ≤ d := by omega, cases this,
  { have : exists_politician G, { apply deg_le_two_friendship_has_pol hG dreg, linarith },
    rw ← exists_pol_of_not_no_pol at this, contradiction },

  apply three_le_deg_friendship_contra hG dreg, assumption,
end
