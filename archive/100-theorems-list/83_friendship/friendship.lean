import .adjacency_matrix
import .counting_paths
import .char_poly
import data.int.modeq
import data.zmod.basic
import number_theory.quadratic_reciprocity
import tactic

open_locale classical
noncomputable theory

open simple_graph bigraph

universes u v
variables {V : Type u} {R : Type v} [fintype V] [inhabited V] [ring R]

section friendship_def
variables (G : simple_graph V)

def is_friend (v w : V) (u : V) : Prop :=
G.E v u ∧ G.E w u

def friends  (v w : V) : finset V :=
  finset.filter (is_friend G v w) (finset.univ:finset V)

def friendship : Prop :=
∀ v w : V, v ≠ w → ∃!(u : V), is_friend G v w u

def exists_politician : Prop :=
  ∃ v : V, ∀ w : V, v = w ∨ G.E v w

def no_pol : Prop :=
  ∀ v : V, ∃ w : V, v ≠ w ∧ ¬ G.E v w

lemma exists_pol_of_not_no_pol :
  (¬ no_pol G) ↔ exists_politician G :=
begin
  unfold no_pol exists_politician, simp only [not_exists, not_and, classical.not_forall, ne.def, classical.not_not],
  apply exists_congr, intro v, apply forall_congr, intro w, tauto,
end

end friendship_def

variables {G : simple_graph V} {d : ℕ} (hG : friendship G)
include hG

lemma friends_eq_inter_neighbors {v w : V} :
  friends G v w = neighbors G v ∩ neighbors G w:=
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

lemma lunique_paths {v : V} {B : finset V} (hv : v ∉ B):
left_unique (path_bigraph G (neighbors G v) B) :=
begin
  rw left_unique_one_reg,
  unfold left_regular,
  intros b hb,
  have hsub : left_fiber (path_bigraph G (neighbors G v) B) b = (neighbors G v) ∩ (neighbors G b),
  apply left_fiber_eq_nbrs_inter_A hb,
  rw [hsub, ← friends_eq_inter_neighbors hG],
  apply card_friends hG,
  rintro rfl, contradiction,
end

lemma runique_paths {v : V} {A : finset V} (hv : v ∉ A):
right_unique (path_bigraph G A (neighbors G v)):=
begin
  rw [← path_bigraph_swap, right_unique_swap],
  exact lunique_paths hG hv,
end

lemma counter_non_adj_deg_eq (hG' : no_pol G) {v w : V} (hvw : ¬ G.E v w) :
degree G v = degree G w :=
begin
  by_cases v=w, { rw h },

  let b:= bigraph.mk (neighbors G v) (neighbors G w) (λ (x:V), λ (y:V), G.E x y),

  apply card_eq_of_lunique_runique b,
  { apply lunique_paths hG,
    rw neighbor_iff_adjacent,
    intro contra,
    apply hvw,
    apply G.undirected contra },
  apply runique_paths hG,
  rw neighbor_iff_adjacent,
  apply hvw,
end

theorem counter_reg (hG' : no_pol G) :
∃ d:ℕ, regular_graph G d :=
begin
  have np:=hG',
  have h2:=counter_non_adj_deg_eq hG,
  have v := arbitrary V,
  use degree G v,
  intro x,
  by_cases hvx : G.E v x,
    swap, symmetry, apply counter_non_adj_deg_eq hG hG' hvx,

  rcases hG' v with ⟨w, hvw', hvw⟩,
  rcases hG' x with ⟨y, hxy', hxy⟩,
  have degvw:=counter_non_adj_deg_eq hG hG' hvw,
  have degxy:=counter_non_adj_deg_eq hG hG' hxy,
  by_cases hxw : G.E x w,
    swap, {rw degvw, apply counter_non_adj_deg_eq hG hG' hxw},
  rw degxy,
  by_cases hvy : G.E v y,
    swap, {symmetry, apply counter_non_adj_deg_eq hG hG' hvy},
  rw degvw,
  apply counter_non_adj_deg_eq hG hG',
  intro hcontra,
  apply hxy',
  apply exists_unique.unique (hG v w hvw'),
  exact ⟨hvx, G.undirected hxw⟩,
  exact ⟨hvy, G.undirected hcontra⟩,
end

-- bad name
lemma friendship_reg_card_count_1 (v:V) :
  card_edges (path_bigraph G (neighbors G v) (finset.erase finset.univ v)) =
    (finset.erase finset.univ v).card :=
by { apply card_edges_of_lunique, apply lunique_paths hG, apply finset.not_mem_erase }

theorem friendship_reg_card
  (hd : regular_graph G d) :
(fintype.card V) - 1 + d = d * d :=
begin
  have v:=arbitrary V,
  have hv : v ∈ finset.univ,
    {apply finset.mem_univ}, swap, {apply_instance},

  have un:(finset.erase finset.univ v)∪ {v}=finset.univ,
  { convert finset.insert_erase hv, rw finset.insert_eq, cc, },

  rw ← reg_card_count_3 hd v,
  rw ← un,

  rw ← finset.card_univ,
  rw ← nat.pred_eq_sub_one,
  rw ← finset.card_erase_of_mem hv,

  rw ← friendship_reg_card_count_1 hG v,

  rw ← reg_card_count_2 hd v,

  symmetry,
  apply card_edges_add_of_eq_disj_union_eq,
  simp,
end

theorem friendship_reg_card'
  (hd : regular_graph G d) :
(fintype.card V:ℤ) = d * (↑d -1) +1:=
begin
  rw mul_sub, norm_cast, rw ← friendship_reg_card hG hd,
  have : 0 ≠ fintype.card V,
  { have v := arbitrary V,
    unfold fintype.card,
    have : v ∈ @finset.univ V _, simp,
    symmetry, exact finset.card_ne_zero_of_mem this },
  push_cast, ring, norm_cast, omega,
end

lemma d_dvd_card_V
  (hd : regular_graph G d)
  {p : ℕ} (hp : p ∣ d - 1) (d_pos : 0 < d) :
(p:ℤ) ∣ fintype.card V - 1 :=
begin
  rw friendship_reg_card' hG hd, ring,
  cases hp with k hk,
  use d * k, norm_cast, rw hk, ring,
end

variables (R)
theorem friendship_adj_sq_off_diag_eq_one
   {v w : V} (hvw : v ≠ w) :
((adjacency_matrix G R)^2) v w = 1 :=
begin
  rw [pow_two, adjacency_matrix_mul_apply, ← nat.cast_one, ← card_friends hG hvw, friends_eq_inter_neighbors hG],
  unfold neighbors, simp [finset.inter_filter],
  congr, ext, rw edge_symm,
end

theorem friendship_reg_adj_sq
  {d:ℕ} (pos : 0<d) (hd : regular_graph G d) :
(adjacency_matrix G R)^2 = (matrix_J V R) + (d-1:ℤ) • 1 :=
begin
  ext, by_cases h : i = j,
  { cases h, rw [pow_two, adj_mat_sq_apply_eq, hd], simp, },
  rw friendship_adj_sq_off_diag_eq_one R hG h, simp [h],
end
variable {R}

lemma friendship_reg_adj_sq_mod_p
  {dpos:0<d} (hd : regular_graph G d)
  {p:ℕ} (hp : ↑p ∣ (d: ℤ ) - 1) :
(adjacency_matrix G $ zmod p)^2 = matrix_J V (zmod p) :=
begin
  rw friendship_reg_adj_sq (zmod p) hG dpos hd,
  have h : (d - 1 : ℤ) • (1 : matrix V V (zmod p)) = 0, swap, rw [h, add_zero],
  rw ← char_p.int_cast_eq_zero_iff (matrix V V (zmod p)) at hp, rw ← hp,
  simp [algebra.smul_def'],
end

lemma friendship_reg_adj_mul_J
  {dpos:0<d} (hd : regular_graph G d)
  :
(adjacency_matrix G R) * (matrix_J V R) = (d : ℤ) • matrix_J V R :=
by { ext, unfold matrix_J, rw ← hd i, unfold degree, simp, }

lemma friendship_reg_adj_mul_J_mod_p
  {dpos:0<d} (hd : regular_graph G d)
  {p:ℕ} (hp : ↑p ∣ (d: ℤ ) - 1) :
(adjacency_matrix G $ zmod p) * (matrix_J V $ zmod p) = matrix_J V (zmod p) :=
begin
  ext, symmetry, simp only [adjacency_matrix_mul_apply, finset.sum_apply, mul_one, matrix_J_apply, finset.sum_const, nsmul_eq_mul],
  rw [← degree, hd, ← nat.cast_one, zmod.eq_iff_modeq_nat, ← int.modeq.coe_nat_modeq_iff, int.modeq.modeq_iff_dvd], apply hp,
end

lemma friendship_reg_adj_pow_mod_p
  {dpos:0<d} (hd : regular_graph G d)
  {p:ℕ} (hp : ↑p ∣ (d: ℤ ) - 1) {k : ℕ} (hk : 2 ≤ k):
(adjacency_matrix G (zmod p)) ^ k = matrix_J V (zmod p) :=
begin
  iterate 2 {cases k with k, { exfalso, linarith,},},
  induction k with k hind,
  { apply friendship_reg_adj_sq_mod_p hG hd hp,
    exact dpos},
  { rw pow_succ,
    have h2 : 2 ≤ k.succ.succ := by omega,
    have hind2 := hind h2,
    rw hind2,
    apply friendship_reg_adj_mul_J_mod_p hG hd hp,
    exact dpos }
end

lemma tr_pow_p_mod_p {p:ℕ} [fact p.prime] (M : matrix V V (zmod p)) :
matrix.trace V (zmod p) (zmod p) (M ^ p) = (matrix.trace V (zmod p) (zmod p) M)^p :=
by rw [trace_from_char_poly, trace_from_char_poly, char_poly_pow_p_char_p, frobenius_fixed]

-- this is the main proof
lemma three_le_deg_friendship_contra
  (hd : regular_graph G d) (h : 3 ≤ d) : false :=
begin
  -- first, we pull in many background facts
  have cardV := friendship_reg_card' hG hd,
  have dpos : 0 < d := by linarith,
  have d_cast : coe (d - 1) = (d : ℤ) - 1 := by norm_cast,
  let p : ℕ := (d - 1).min_fac,
  have p_dvd_d_pred := (d - 1).min_fac_dvd,
  have p_dvd_V_pred : ↑p ∣ (fintype.card V - 1 : ℤ),
  { transitivity ↑(d-1), { rwa int.coe_nat_dvd },
    use d, rw cardV, norm_cast, simp; ring },
  haveI : fact p.prime := nat.min_fac_prime (by linarith),
  have hp2 : 2 ≤ p, { apply nat.prime.two_le, assumption },
  -- now we reduce to a trace calculation
  have := tr_pow_p_mod_p hG (adjacency_matrix G (zmod p)), contrapose! this, clear this,
  -- the trace is 0 mod p when computed one way
  have eq_J : (adjacency_matrix G (zmod p)) ^ p = (matrix_J V (zmod p)),
  { apply friendship_reg_adj_pow_mod_p hG hd; assumption_mod_cast },
  rw [eq_J, trace_J V], norm_num,
  rw zero_pow, swap, { linarith },
  -- but the trace is 1 mod p when computed the other way
  suffices : ↑(fintype.card V) = (1 : zmod p), { simp [this] },
  cases p_dvd_V_pred with k hk,
  apply_fun (coe : ℤ → zmod p) at hk,
  rw [← zero_add (1 : zmod p), ← sub_eq_iff_eq_add],
  simp at hk, exact hk,
end

lemma deg_le_one_friendship_has_pol
  (hd : regular_graph G d) (hd1 : d ≤ 1) :
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

lemma deg_two_friendship_has_pol (hd : regular_graph G 2) :
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

  have h':neighbors G v = finset.univ.erase v,
  apply finset.eq_of_subset_of_card_le,
  { rw finset.subset_iff,
    intro x,
    rw neighbor_iff_adjacent,
    rw finset.mem_erase,
    intro h,
    split, { symmetry, exact G.ne_of_edge h },
    apply finset.mem_univ },

  { rw herase,
    unfold regular_graph at hd, unfold degree at hd,
    rw hd },

  rw [← neighbor_iff_adjacent, h', finset.mem_erase],
  split, { symmetry, exact hvw },
  apply finset.mem_univ
end

lemma deg_le_two_friendship_has_pol (hd : regular_graph G d) :
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
  have regG : ∃ (d:ℕ), regular_graph G d,
  { apply counter_reg; assumption },
  cases regG with d dreg,

  have : d ≤ 2 ∨ 3 ≤ d := by omega, cases this,
  { have : exists_politician G, { apply deg_le_two_friendship_has_pol hG dreg, linarith },
    rw ← exists_pol_of_not_no_pol at this, contradiction },

  apply three_le_deg_friendship_contra hG dreg, assumption,
end
