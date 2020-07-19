import .adjacency_matrix
import .double_counting
import .char_poly
import data.int.modeq
import data.zmod.basic
import number_theory.quadratic_reciprocity
import tactic

open_locale classical
noncomputable theory

open simple_graph
universes u

variables {V : Type u} [fintype V] [inhabited V] (G : simple_graph V)


def is_friend (v w : V) (u : V) : Prop :=
G.E v u ∧ G.E w u

def friendship : Prop :=
∀ v w : V, v ≠ w → ∃!(u : V), is_friend G v w u

-- lemma friend_symm (u v w : V) :
--   G.E v u ∧ G.E u w ↔ G.E v u ∧ G.E w u :=
-- begin
--   split; try { intro a, cases a, split };
--   try {assumption};
--   { apply G.undirected, assumption },
-- end

-- def find_friend (G:simple_graph V)(friendG: friendship G)(v w:V)(vneqw:v ≠ w):V:=
--   fintype.choose (is_friend G v w) (friendG v w vneqw)

-- lemma find_friend_spec (G:simple_graph V)(friendG: friendship G)(v w:V)(vneqw: v ≠ w):
--   is_friend G v w (find_friend G friendG v w vneqw):= by apply fintype.choose_spec

-- lemma find_friend_unique (G:simple_graph V)(friendG: friendship G)(v w:V)(vneqw: v ≠ w):
--   ∀ y:V, is_friend G v w y → y=(find_friend G friendG v w vneqw):=
-- begin
--   intros y hy,
--   apply exists_unique.unique(friendG v w vneqw),
--   apply hy,
--   apply (find_friend_spec G friendG v w vneqw),
-- end

lemma friendship' {G : simple_graph V} (friendG : friendship G) {v w : V} (hvw : v ≠ w) :
exists_unique (is_friend G v w) :=
begin
  use fintype.choose (is_friend G v w) (friendG v w hvw),
  split, { apply fintype.choose_spec },
  intros x hx,
  apply exists_unique.unique (friendG v w hvw) hx,
  apply fintype.choose_spec,
end

def exists_politician (G:simple_graph V) : Prop :=
  ∃ v:V, ∀ w:V, v=w ∨ G.E v w

def no_pol (G : simple_graph V) : Prop :=
  ∀ v : V, ∃ w : V, v ≠ w ∧ ¬ G.E v w

lemma exists_pol_of_not_no_pol {G : simple_graph V}:
  (¬ no_pol G) ↔ exists_politician G:=
begin
  unfold no_pol exists_politician, simp only [not_exists, not_and, classical.not_forall, ne.def, classical.not_not],
  apply exists_congr, intro v, apply forall_congr, intro w, tauto,
end

def path_bigraph (G : simple_graph V) (A B:finset V) : bigraph V V:=
  bigraph.mk A B G.E

lemma path_bigraph_swap {G : simple_graph V} {A B : finset V} :
  (path_bigraph G A B).swap = path_bigraph G B A:=
begin
  ext, {refl}, {refl},
  split; apply G.undirected,
end

def friends (G : simple_graph V)(v w : V) : finset V :=
  finset.filter (is_friend G v w) (finset.univ:finset V)

lemma friends_eq_inter_neighbors {G : simple_graph V} {v w : V} :
  friends G v w = neighbors G v ∩ neighbors G w:=
begin
  ext,
  rw finset.mem_inter, erw finset.mem_filter,
  unfold is_friend, simp,
end

lemma card_friends {G : simple_graph V} (friendG : friendship G) {v w : V} (hvw : v ≠ w) :
  (friends G v w).card = 1 :=
begin
  rw finset.card_eq_one,
  rw finset.singleton_iff_unique_mem,
  unfold friends, simp [friendship' friendG hvw],
end

lemma left_fiber_eq_nbrs_inter_A {G : simple_graph V} {A B : finset V} {v : V} :
  v ∈ B → left_fiber (path_bigraph G A B) v = A ∩ (neighbors G v):=
begin
  intro vB, ext,
  simp only [neighbor_iff_adjacent, mem_left_fiber, finset.mem_inter],
  change a ∈ A ∧ G.E a v ↔ a ∈ A ∧ G.E v a,
  have h : G.E a v ↔ G.E v a, {split; apply G.undirected},
  rw h,
end

lemma right_fiber_eq_nbrs_inter_B {G : simple_graph V} {A B : finset V} {v : V} (hv : v ∈ A):
right_fiber (path_bigraph G A B) v = B ∩ (neighbors G v):=
begin
  rw [← left_fiber_swap, path_bigraph_swap],
  exact left_fiber_eq_nbrs_inter_A hv,
end

lemma lunique_paths {G : simple_graph V} {v : V} {B : finset V} (hG : friendship G) (hv : v ∉ B):
left_unique (path_bigraph G (neighbors G v) B) :=
begin
  rw left_unique_one_reg,
  unfold left_regular,
  intros b hb,
  have hsub : left_fiber (path_bigraph G (neighbors G v) B) b = (neighbors G v) ∩ (neighbors G b),
  apply left_fiber_eq_nbrs_inter_A hb,
  rw [hsub, ← friends_eq_inter_neighbors],
  apply card_friends hG,
  intro veqb, rw veqb at hv,
  contradiction,
end

lemma runique_paths {G:simple_graph V} {v : V} {A : finset V} (hG : friendship G) (hv : v ∉ A):
right_unique (path_bigraph G A (neighbors G v)):=
begin
  rw [← path_bigraph_swap, right_unique_swap],
  exact lunique_paths hG hv,
end

lemma counter_non_adj_deg_eq
  {G : simple_graph V} (hG : friendship G)  (hG' : no_pol G)
  {v w : V} (hvw : ¬ G.E v w ):
degree G v = degree G w:=
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



theorem counter_reg {G:simple_graph V} (hG : friendship G) (hG' : no_pol G) :
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

variables {R : Type*} [ring R]

theorem friendship_adj_sq_off_diag_eq_one
  (G:simple_graph V) (hG : friendship G) {v w : V} (hvw : v ≠ w) :
((adjacency_matrix G R)^2) v w = 1 :=
begin
  rw [pow_two, adjacency_matrix_mul_apply, ← nat.cast_one, ← card_friends hG hvw, friends_eq_inter_neighbors],
  unfold neighbors, simp [finset.inter_filter],
  congr, ext, rw edge_symm,
end

def two_path_from_v (G:simple_graph V) (v:V):(V × V → Prop):=
  λ x:V × V, G.E v x.fst ∧ G.E x.fst x.snd

lemma friendship_reg_card_count_1
  {G:simple_graph V} (hG : friendship G) (v:V) :
card_edges (path_bigraph G (neighbors G v) (finset.erase finset.univ v))=(finset.erase finset.univ v).card:=
begin
  apply card_edges_of_lunique,
  apply lunique_paths hG,
  apply finset.not_mem_erase,
end

lemma friendship_reg_card_count_2
  {G:simple_graph V} {d:ℕ} (hd : regular_graph G d) (v:V) :
card_edges (path_bigraph G (neighbors G v) {v}) = d :=
begin
  unfold regular_graph at hd,
  rw ← hd v,
  apply card_edges_of_runique,
  rw right_unique_one_reg,
  unfold right_regular,
  intros a ha,
  change a ∈ neighbors G v at ha,
  rw right_fiber_eq_nbrs_inter_B ha,
  have h:neighbors G a∩ {v} = {v},
  { apply finset.inter_singleton_of_mem,
    rw neighbor_iff_adjacent,
    rw neighbor_iff_adjacent at ha,
    exact G.undirected ha },
  rw [finset.inter_comm, h], simp,
end

lemma reg_card_count_3
  {G:simple_graph V} {d:ℕ} (hd : regular_graph G d) (v:V) :
card_edges (path_bigraph G (neighbors G v) finset.univ) = d * d :=
begin
  unfold regular_graph at hd,
  unfold degree at hd,

  transitivity d * (neighbors G v).card,
  swap, { rw hd v },
  apply card_edges_of_rreg,
  intros a ha,
  rw right_fiber_eq_nbrs_inter_B,
  { rw [finset.univ_inter, hd a] },
  { exact ha },
end

lemma finset.erase_disj_sing {α:Type*}{s:finset α}{a:α}:
  disjoint (s.erase a) {a}:=
begin
  rw finset.disjoint_singleton,
  apply finset.not_mem_erase,
end

lemma finset.erase_union_sing {α:Type*}{s:finset α}{a:α}:
  a ∈ s → s.erase a ∪ {a}=s:=
begin
  intro h,
  rw finset.union_comm,
  rw ← finset.insert_eq,
  apply finset.insert_erase h,
end

theorem friendship_reg_card
  {G:simple_graph V} {d:ℕ} (hG : friendship G) (hd : regular_graph G d) :
(fintype.card V) - 1 + d = d * d :=
begin
  have v:=arbitrary V,
  have hv : v ∈ finset.univ,
    {apply finset.mem_univ}, swap, {apply_instance},

  have un:(finset.erase finset.univ v)∪ {v}=finset.univ,
  { apply finset.erase_union_sing hv},

  rw ← reg_card_count_3 hd v,
  rw ← un,

  rw ← finset.card_univ,
  rw ← nat.pred_eq_sub_one,
  rw ← finset.card_erase_of_mem hv,

  rw ← friendship_reg_card_count_1 hG v,

  rw ← friendship_reg_card_count_2 hd v,

  symmetry,
  apply card_edges_add_of_eq_disj_union_eq,
  apply finset.erase_disj_sing,
end

theorem friendship_reg_card'
  {G : simple_graph V} {d : ℕ} (hG : friendship G) (hd : regular_graph G d) :
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
  {G : simple_graph V} {d : ℕ} (hG : friendship G) (hd : regular_graph G d)
  {p : ℕ} (hp : p ∣ d - 1) (d_pos : 0 < d) :
(p:ℤ) ∣ fintype.card V - 1 :=
begin
  rw friendship_reg_card' hG hd, ring,
  cases hp with k hk,
  use d * k, norm_cast, rw hk, ring,
end



lemma le_one_of_pred_zero {n:ℕ}:
  n-1=0 → n ≤ 1:= by omega


local attribute [simp]
lemma nat.smul_one (d : ℕ) (R : Type*) [ring R] : d • (1 : R) = (d : R) :=
begin
  induction d with k hk, simp,
  rw nat.succ_eq_add_one, push_cast,
  rw ← hk, rw add_smul, simp,
end

local attribute [simp]
lemma int.smul_one (d : ℤ) (R : Type*) [ring R] : d • (1 : R) = (d : R) :=
begin
  apply gsmul_one,
end

variable (R)
theorem friendship_reg_adj_sq
  (G:simple_graph V) (d:ℕ) (pos : 0<d) (hG : friendship G) (hd : regular_graph G d) :
(adjacency_matrix G R)^2 = (matrix_J V R) + (d-1:ℤ) • 1 :=
begin
  ext,
  by_cases i=j,
  { rw [← h, pow_two],
    rw adj_mat_sq_apply_eq,
    rw hd i,
    unfold matrix_J,
    simp only [matrix.one_val_eq, nat.smul_one, matrix.add_val, pi.smul_apply],
    cases d, {norm_num at pos}, {simp, rw add_comm,} },

  rw friendship_adj_sq_off_diag_eq_one G hG h,
  unfold matrix_J,
  simp [matrix.one_val_ne h],
end
variable {R}

lemma subsingleton_graph_has_pol (G : simple_graph V) :
  fintype.card V ≤ 1 → exists_politician G:=
begin
  intro subsing,
  rw fintype.card_le_one_iff at subsing,
  use arbitrary V, intro w,
  left, apply subsing,
end

lemma deg_le_one_friendship_has_pol
  {G:simple_graph V} {d:ℕ} (hG : friendship G) (hd : regular_graph G d) :
d ≤ 1 → exists_politician G :=
begin
  intro d_le_one,
  have sq : d * d = d := by {interval_cases d; norm_num},

  have hfr := friendship_reg_card hG hd,
  rw sq at hfr,
  apply subsingleton_graph_has_pol,
  apply le_one_of_pred_zero,
  linarith,
end

lemma ne_of_edge {G : simple_graph V} {a b : V} (hab : G.E a b) : a ≠ b :=
begin
  intro h, rw h at hab, apply G.loopless b, exact hab,
end

lemma deg_two_friendship_has_pol
  {G:simple_graph V} {d:ℕ}  (hG : friendship G) (hd : regular_graph G d) :
d = 2 → exists_politician G :=
begin
  intro deq2,
  rw deq2 at hd,
  have v := arbitrary V,
  have hfr:=friendship_reg_card hG hd,
  have h2 : fintype.card V - 1 = 2 := by linarith, clear hfr,
  -- now we have a degree two graph with three vertices
  -- the math thing to do would be to replace it with the triangle graph

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
    split, { symmetry, exact ne_of_edge h },
    apply finset.mem_univ },

  { rw herase,
    unfold regular_graph at hd, unfold degree at hd,
    rw hd },

  rw [← neighbor_iff_adjacent, h', finset.mem_erase],
  split, { symmetry, exact hvw },
  apply finset.mem_univ
end

lemma deg_le_two_friendship_has_pol
  {G:simple_graph V} {d:ℕ} (hG : friendship G) (hd : regular_graph G d) :
d ≤ 2 → exists_politician G:=
begin
  intro d_le_2,
  interval_cases d,
  iterate 2 { apply deg_le_one_friendship_has_pol hG hd, norm_num },
  { apply deg_two_friendship_has_pol hG hd, refl },
end

lemma matrix_J_sq :
(matrix_J V R)^2 = (fintype.card V : R) • matrix_J V R :=
begin
  rw pow_two,
  rw matrix.mul_eq_mul, ext, rw matrix.mul_val,
  unfold matrix_J,
  simp; refl,
end

lemma matrix_J_mod_p_idem
  {p:ℕ} [char_p R p] (hp : ↑p ∣ (fintype.card V : ℤ ) - 1) :
(matrix_J V (zmod p)) ^ 2 = matrix_J V (zmod p) :=
begin
  rw matrix_J_sq,
  have : (fintype.card V : zmod p) = 1, swap, simp [this], symmetry,
  rw [← nat.cast_one, zmod.eq_iff_modeq_nat, ← int.modeq.coe_nat_modeq_iff, int.modeq.modeq_iff_dvd], apply hp,
end

lemma friendship_reg_adj_sq_mod_p
  {G:simple_graph V} {d:ℕ} {dpos:0<d} (hG : friendship G) (hd : regular_graph G d)
  {p:ℕ} (hp : ↑p ∣ (d: ℤ ) - 1) :
(adjacency_matrix G $ zmod p)^2 = matrix_J V (zmod p) :=
begin
  rw friendship_reg_adj_sq (zmod p) G d dpos hG hd,
  have h : (d - 1 : ℤ) • (1 : matrix V V (zmod p)) = 0, swap, rw [h, add_zero],
  rw ← char_p.int_cast_eq_zero_iff (matrix V V (zmod p)) at hp, rw ← hp,
  simp [algebra.smul_def'],
end

lemma friendship_reg_adj_mul_J
  {G:simple_graph V} {d:ℕ} {dpos:0<d} (hG : friendship G) (hd : regular_graph G d)
  :
(adjacency_matrix G R) * (matrix_J V R) = (d : ℤ) • matrix_J V R :=
by { ext, unfold matrix_J, rw ← hd i, unfold degree, simp, }

lemma friendship_reg_adj_mul_J_mod_p
  {G:simple_graph V} {d:ℕ} {dpos:0<d} (hG : friendship G) (hd : regular_graph G d)
  {p:ℕ} (hp : ↑p ∣ (d: ℤ ) - 1) :
(adjacency_matrix G $ zmod p) * (matrix_J V $ zmod p) = matrix_J V (zmod p) :=
begin
  ext, symmetry, simp only [adjacency_matrix_mul_apply, finset.sum_apply, mul_one, matrix_J_apply, finset.sum_const, nsmul_eq_mul],
  rw [← degree, hd, ← nat.cast_one, zmod.eq_iff_modeq_nat, ← int.modeq.coe_nat_modeq_iff, int.modeq.modeq_iff_dvd], apply hp,
end

lemma friendship_reg_adj_pow_mod_p
  {G:simple_graph V} {d:ℕ} {dpos:0<d} (hG : friendship G) (hd : regular_graph G d)
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

lemma three_le_deg_friendship_contra
  {G:simple_graph V} {d:ℕ} (hG : friendship G) (hd : regular_graph G d) :
3 ≤ d → false :=
begin
  intro h,
  have dpos : 0<d := by linarith,
  let p:ℕ:=(d-1).min_fac,
  have hadj:=friendship_reg_adj_sq (zmod p) G d dpos hG,
  have traceless := adj_mat_traceless G (zmod p),
  have cardV:=friendship_reg_card' hG hd,
  have p_dvd_d_pred:p ∣ d-1:=(d-1).min_fac_dvd,
  have d_cast : coe (d - 1) = (d : ℤ) - 1 := by norm_cast,
  have p_dvd_V_pred:↑p ∣ ((fintype.card V:ℤ)-1),
  { transitivity ↑(d-1), {rwa int.coe_nat_dvd},
    use d, rw [d_cast, cardV], ring },
  have neq1 : d-1 ≠ 1 := by linarith,
  have pprime : p.prime := nat.min_fac_prime neq1,
  haveI : fact p.prime := pprime,
  have trace_0:= tr_pow_p_mod_p (adjacency_matrix G (zmod p)),
  have eq_J : (adjacency_matrix G (zmod p)) ^ p = (matrix_J V (zmod p)),
  { apply friendship_reg_adj_pow_mod_p hG hd,
    { rw [← d_cast, int.coe_nat_dvd],
      apply p_dvd_d_pred },
    { apply nat.prime.two_le pprime },
    assumption },
  contrapose! trace_0, clear trace_0,
  rw eq_J,
  rw trace_J V,
  norm_num,
  have p_pos : 0 < p,
  linarith [nat.prime.two_le pprime],
  rw zero_pow p_pos,
  suffices key :  ↑(fintype.card V) = (1 : zmod p),
  { rw key, simp },
  cases p_dvd_V_pred with k hk,

  lift k to ℕ,
  { rw sub_eq_iff_eq_add at hk, norm_cast at hk, rw hk, simp },
  have p_pos' : (0 : ℤ) < p := by exact_mod_cast p_pos,
  apply nonneg_of_mul_nonneg_left _ p_pos',
  rw [← hk, cardV, add_sub_cancel], norm_cast,
  simp,
end


theorem friendship_theorem {G:simple_graph V} (hG : friendship G):
  exists_politician G:=
begin
  rw ← exists_pol_of_not_no_pol,
  intro npG,
  have regG : ∃ (d:ℕ), regular_graph G d,
  { apply counter_reg; assumption },
  cases regG with d dreg,

  have : d ≤ 2 ∨ 3 ≤ d := by omega, cases this,
  { have ex_pol : exists_politician G,
    apply deg_le_two_friendship_has_pol hG dreg,
    linarith,
    apply exists_pol_of_not_no_pol.2 ex_pol npG },

  apply three_le_deg_friendship_contra hG dreg, assumption,
end
