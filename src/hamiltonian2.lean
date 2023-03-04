import combinatorics.simple_graph.matching
import combinatorics.simple_graph.connectivity

noncomputable theory

namespace simple_graph

variables {V : Type*} {G : simple_graph V}

/-- The vertices in the same connected component. -/
def connected_component.supp (c : G.connected_component) : set V :=
{v | G.connected_component_mk v = c}

@[simp] lemma connected_component.mem_supp {v : V} {c : G.connected_component} :
  v ∈ c.supp ↔ G.connected_component_mk v = c := iff.rfl

/-- The graph consisting of all the edges in the connected component for `c`. -/
def connected_component.induce (c : G.connected_component) : simple_graph V :=
(G.induce c.supp).spanning_coe

@[simp] lemma connected_component.induce_adj_left (c : G.connected_component) {v w : V} :
  c.induce.adj v w ↔ G.connected_component_mk v = c ∧ G.adj v w :=
begin
  simp only [connected_component.induce, map_adj, comap_adj, function.embedding.coe_subtype,
    set_coe.exists, connected_component.mem_supp, subtype.coe_mk, exists_prop],
  split,
  { rintro ⟨a, hrab, b, rfl, hab, rfl, rfl⟩,
    exact ⟨hrab, hab⟩, },
  { rintro ⟨hc, hvw⟩,
    refine ⟨v, hc, w, _, hvw, rfl, rfl⟩,
    rw [← hc, connected_component.eq],
    exact hvw.symm.reachable, }
end

lemma connected_component.induce_le (c : G.connected_component) : c.induce ≤ G :=
spanning_coe_induce_le _ _

lemma connected_component.mem_supp_of_adj (c : G.connected_component) {v w : V}
  (hvw : c.induce.adj v w) : v ∈ c.supp :=
begin
  simp only [connected_component.induce_adj_left] at hvw,
  simpa using hvw.1,
end

lemma connected_component.not_adj_of_not_mem_supp (c : G.connected_component) {v w : V}
  (hv : ¬ v ∈ c.supp) : ¬ c.induce.adj v w :=
mt (c.mem_supp_of_adj) hv

-- Note: it might not be that `c.induce.support.nonempty` since the connected component
-- might have just a single vertex.

lemma connected_component.induce_support_le (c : G.connected_component) :
  c.induce.support ≤ c.supp :=
begin
  rintro v ⟨w, hvw⟩,
  exact c.mem_supp_of_adj hvw,
end

lemma connected_component.induce.mem_of_reachable (c : G.connected_component)
  {v w : V} (hv : v ∈ c.induce.support) (hvw : G.adj v w) :
  w ∈ c.induce.support :=
begin
  refine connected_component.ind (λ u hv, _) c hv,
  simp only [mem_support, connected_component.induce_adj_left, connected_component.eq,
    exists_and_distrib_left] at hv ⊢,
  exact ⟨hvw.symm.reachable.trans hv.1, ⟨v, hvw.symm⟩⟩,
end

/-- A graph is a *matching* if every vertex has at most one neighbor. -/
def is_matching (G : simple_graph V) : Prop := ∀ v, (G.neighbor_set v).subsingleton

/-- A graph is a *perfect matching* if every vertex has exactly one neighbor. -/
def is_perfect_matching (G : simple_graph V) : Prop := ∀ v, ∃! w, G.adj v w

section matchings

variables {G}

namespace is_matching

lemma adj_unique (hm : G.is_matching) {v w w' : V} (h : G.adj v w) (h' : G.adj v w') : w = w' :=
hm v h h'

end is_matching

namespace is_perfect_matching
variables (hp : G.is_perfect_matching)

/-- The unique vertex incident to `v` in the perfect matching. -/
protected def other (v : V) : V := (hp v).some

lemma adj_other (v : V) : G.adj v (hp.other v) := (hp v).some_spec.1

lemma other_unique {v w : V} (ha : G.adj v w) : w = hp.other v := (hp v).some_spec.2 w ha

lemma adj_iff_eq {v w : V} : G.adj v w ↔ w = hp.other v :=
⟨hp.other_unique, by { rintro rfl, exact hp.adj_other v }⟩

lemma other_involutive : function.involutive hp.other :=
λ v, (hp.other_unique (hp.adj_other v).symm).symm

@[simp] lemma other_other (v : V) : hp.other (hp.other v) = v :=
hp.other_involutive v

lemma neighbor_set_eq (v : V) : G.neighbor_set v = {hp.other v} :=
by { ext w, simp [hp.adj_iff_eq] }

def locally_finite (hp : G.is_perfect_matching) : G.locally_finite :=
λ v, by { rw [hp.neighbor_set_eq], exact unique.fintype }

protected
lemma is_matching (hp : G.is_perfect_matching) : G.is_matching :=
begin
  intro v,
  rw [set.subsingleton_iff_singleton],
  apply hp.neighbor_set_eq,
  simp [hp.adj_other],
end

lemma support_eq_univ (hp : G.is_perfect_matching) : G.support = set.univ :=
begin
  ext v,
  simp [mem_support],
  existsi hp.other v,
  apply adj_other,
end

end is_perfect_matching

lemma is_perfect_matching_iff :
  G.is_perfect_matching ↔ G.is_matching ∧ G.support = set.univ :=
begin
  split,
  { intro hp,
    exact ⟨hp.is_matching, hp.support_eq_univ⟩, },
  { rintro ⟨hm, hs⟩,
    intro v,
    have := set.ext_iff.mp hs v,
    simp only [set.mem_univ, iff_true] at this,
    obtain ⟨w, hvw⟩ := this,
    refine ⟨w, hvw, _⟩,
    intros w' hvw',
    exact hm.adj_unique hvw' hvw, }
end

lemma is_perfect_matching_iff_forall_degree [G.locally_finite] :
  G.is_perfect_matching ↔ ∀ (v : V), G.degree v = 1 :=
begin
  rw [is_perfect_matching],
  refine forall_congr (λ v, _),
  simp_rw [degree, finset.card_eq_one, finset.singleton_iff_unique_mem, mem_neighbor_finset],
end

lemma is_perfect_matching_iff_one_regular [G.locally_finite] :
  G.is_perfect_matching ↔ G.is_regular_of_degree 1 :=
by rw [is_perfect_matching_iff_forall_degree, is_regular_of_degree]

end matchings

theorem neighbor_set_sup {G H : simple_graph V} {v : V} :
  (G ⊔ H).neighbor_set v = G.neighbor_set v ∪ H.neighbor_set v :=
by { ext w, simp }

theorem neighbor_set_inf {G H : simple_graph V} {v : V} :
  (G ⊓ H).neighbor_set v = G.neighbor_set v ∩ H.neighbor_set v :=
by { ext w, simp }

theorem neighbor_finset_sup {G H : simple_graph V} {v : V} [decidable_eq V]
  [fintype ((G ⊔ H).neighbor_set v)] [fintype (G.neighbor_set v)] [fintype (H.neighbor_set v)] :
  (G ⊔ H).neighbor_finset v = G.neighbor_finset v ∪ H.neighbor_finset v :=
by { ext w, simp }

noncomputable
instance (G H : simple_graph V) {v : V} [fintype (G.neighbor_set v)] [fintype (H.neighbor_set v)] :
  fintype ((G ⊔ H).neighbor_set v) :=
by { rw [neighbor_set_sup], exact fintype.of_finite ↥(neighbor_set G v ∪ neighbor_set H v) }

lemma disjoint_neighbor_set_of_disjoint {G H : simple_graph V} (hd : disjoint G H) {v : V} :
  disjoint (G.neighbor_set v) (H.neighbor_set v) :=
begin
  rw [set.disjoint_iff],
  rintro w ⟨hg, hh⟩,
  exfalso,
  rw [disjoint] at hd,
  have : (G ⊓ H).adj v w,
  { simp only [mem_neighbor_set] at hg hh,
    simp [hg, hh], },
  exact hd inf_le_left inf_le_right this,
end

lemma disj_union_regular {G H : simple_graph V} [G.locally_finite] [H.locally_finite]
  (hd : disjoint G H)
  {m n : ℕ}
  (hg : G.is_regular_of_degree m) (hh : H.is_regular_of_degree n) :
  (G ⊔ H).is_regular_of_degree (m + n) :=
begin
  intro v,
  specialize hg v,
  specialize hh v,
  classical,
  rw [degree, neighbor_finset_sup, finset.card_union_eq, ← degree, ← degree, hg, hh],
  apply set.disjoint_to_finset.mpr,
  apply disjoint_neighbor_set_of_disjoint hd,
end

lemma disj_union_perfect_matchings {G H : simple_graph V} [G.locally_finite] [H.locally_finite]
  (hd : disjoint G H)
  (hg : G.is_perfect_matching) (hh : H.is_perfect_matching) :
  (G ⊔ H).is_regular_of_degree 2 :=
begin
  rw [is_perfect_matching_iff_one_regular] at hg hh,
  exact disj_union_regular hd hg hh,
end

lemma disj_union_three_perfect_matchings {G₁ G₂ G₃ : simple_graph V}
  [G₁.locally_finite] [G₂.locally_finite] [G₃.locally_finite]
  (hd₁₂ : disjoint G₁ G₂) (hd₁₃ : disjoint G₁ G₃) (hd₂₃ : disjoint G₂ G₃)
  (hg₁ : G₁.is_perfect_matching) (hg₂ : G₂.is_perfect_matching) (hg₃ : G₃.is_perfect_matching) :
  (G₁ ⊔ G₂ ⊔ G₃).is_regular_of_degree 3 :=
begin
  rw [is_perfect_matching_iff_one_regular] at hg₃,
  have := disj_union_perfect_matchings hd₁₂ hg₁ hg₂,
  refine disj_union_regular _ this hg₃,
  rw disjoint_sup_left,
  split; assumption,
end

/--
Given disjoint perfect matchings and a connected component, we can flip those edges of `m`
to those of `m'` in the connected component.
-/
lemma flip_part_of_disjoint
  {m m' : simple_graph V} (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  (hd : disjoint m m')
  (c : (m ⊔ m').connected_component) :
  (m ∆ c.induce).is_perfect_matching :=
begin
  intro v,
  by_cases hv : v ∈ c.supp,
  { simp only [connected_component.mem_supp] at hv,
    refine ⟨hm'.other v, _, _⟩,
    { simp only [symm_diff_def, sup_adj, sdiff_adj],
      right,
      split,
      { simp only [hv, connected_component.induce_adj_left, eq_self_iff_true, sup_adj, true_and],
        right,
        exact hm'.adj_other _, },
      { intro h,
        have := hm'.adj_other v,
        exact hd inf_le_left inf_le_right ⟨h, this⟩, }, },
    { intro w,
      simp only [symm_diff_def, sup_adj, sdiff_adj, connected_component.induce_adj_left, not_and],
      simp only [hv, eq_self_iff_true, forall_true_left, true_and],
      simp only [not_or_distrib, ←and_assoc, and_not_self, false_and, false_or, and_imp],
      simp only [or_imp_distrib, not_true, is_empty.forall_iff,
        implies_true_iff, true_and] {contextual := tt},
      intros hv hv',
      exact hm'.other_unique hv, } },
  { refine ⟨hm.other v, _, _⟩,
    { simp only [symm_diff_def, hm.adj_other, sup_adj, sdiff_adj, true_and,
        not_true, and_false, or_false],
      intro h,
      exact hv (c.mem_supp_of_adj h), },
    { intro w,
      simp only [symm_diff_def, sup_adj, sdiff_adj],
      simp only [c.not_adj_of_not_mem_supp hv, not_false_iff, and_true, false_and, or_false],
      exact hm.other_unique, } }
end

lemma flip_part_of_disjoint_le
  {m m' : simple_graph V}
  (c : (m ⊔ m').connected_component) :
  m ∆ c.induce ≤ m ⊔ m' :=
begin
  intros v w,
  simp only [symm_diff_def, sup_adj, sdiff_adj, connected_component.induce_adj_left, not_and,
    not_or_distrib],
  rintro (⟨h, _⟩ | ⟨⟨_, h⟩, _⟩),
  { exact or.inl h },
  { exact h }
end


/-- The predicate that every pair of distinct perfect matchings is disjoint. -/
def perfect_matchings_disjoint (G : simple_graph V) : Prop :=
∀ {m m' : simple_graph V}, m ≤ G → m' ≤ G →
  m.is_perfect_matching → m'.is_perfect_matching → m ≠ m' → disjoint m m'

namespace perfect_matchings_disjoint

lemma ne_symm_diff (hpmd : G.perfect_matchings_disjoint)
  {m m' : simple_graph V} (hm : m ≤ G) (hm' : m' ≤ G)
  (hpm : m.is_perfect_matching) (hpm' : m'.is_perfect_matching) (hne : m ≠ m') (v : V) :
  m ≠ m ∆ ((m ⊔ m').connected_component_mk v).induce :=
begin
  intro h,
  have hv := congr_fun (congr_fun (congr_arg simple_graph.adj h) v) (hpm.other v),
  simp only [hpm.adj_other v, eq_true_eq_id, id.def] at hv,
  simp only [symm_diff_def, hpm.adj_other v, sup_adj, sdiff_adj,
    connected_component.induce_adj_left, connected_component.eq,
    true_or, and_true, true_and, not_true, and_false, or_false] at hv,
  exact hv reachable.rfl,
end

/-- The union of two distinct perfect matchings in a graph with the property that all perfect
matchings are disjoint is connected. -/
theorem disj_union_connected (hpmd : G.perfect_matchings_disjoint)
  {m m' : simple_graph V} (hm : m ≤ G) (hm' : m' ≤ G)
  (hpm : m.is_perfect_matching) (hpm' : m'.is_perfect_matching) (hne : m ≠ m') :
  (m ⊔ m').connected :=
begin
  haveI hnonempty : nonempty V,
  { by_contra h,
    rw [not_nonempty_iff] at h,
    apply hne,
    ext v w,
    exact h.elim v },
  rw [connected_iff],
  refine ⟨_, hnonempty⟩,
  by_contra,
  simp only [preconnected, not_forall] at h,
  obtain ⟨v, v', h⟩ := h,
  have hdisj := hpmd hm hm' hpm hpm' hne,
  let c := (m ⊔ m').connected_component_mk v,
  have hperf := flip_part_of_disjoint hpm hpm' hdisj c,
  have hsup_le : m ⊔ m' ≤ G := sup_le hm hm',
  have : m ≠ m ∆ c.induce := ne_symm_diff @hpmd hm hm' hpm hpm' hne v,
  have := hpmd hm (le_trans (flip_part_of_disjoint_le c) hsup_le) hpm hperf this,
  have h1 : m \ c.induce ≤ m,
  { intros v w,
    simp only [sdiff_adj, implies_true_iff] {contextual := tt}, },
  have h2 : m \ c.induce ≤ m ∆ c.induce,
  { intros v w,
    simp only [symm_diff_def, sdiff_adj, connected_component.induce_adj_left,
      connected_component.eq, sup_adj, not_and, and_imp],
    simp { contextual := tt}, },
  have h3 : (m \ c.induce).adj v' (hpm.other v'),
  { simp only [hpm.adj_other v', sdiff_adj, connected_component.induce_adj_left,
      connected_component.eq, sup_adj, true_or, and_true, true_and],
    contrapose! h,
    exact h.symm, },
  exact this h1 h2 h3,
end

end perfect_matchings_disjoint

theorem neighbor_set_from_edge_set_insert [decidable_eq V] (s : set (sym2 V)) (u v w : V)
  (h : u ≠ v) :
  (from_edge_set (insert ⟦(u, v)⟧ s)).neighbor_set w =
    (if u = w then {v} else ∅) ∪ (if v = w then {u} else ∅) ∪ (from_edge_set s).neighbor_set w :=
begin
  ext x,
  simp only [mem_neighbor_set, from_edge_set_adj, set.mem_insert_iff, quotient.eq, sym2.rel_iff,
    ne.def, set.mem_union, set.mem_ite_empty_right, set.mem_singleton_iff],
  simp only [eq_comm, or_assoc],
  split,
  { rintro ⟨h', h⟩,
    simp [h, h'], },
  { rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h'),
    simp [h],
    simp [h.symm],
    simp [h'.1, h'.2], }
end

@[simp] theorem neighbor_set_bot (v : V) : (⊥ : simple_graph V).neighbor_set v = ∅ :=
begin
  ext w,
  simp,
end

theorem neighbor_set_from_edge_set_singleton [decidable_eq V] (u v w : V) (h : u ≠ v) :
  (from_edge_set {⟦(u, v)⟧}).neighbor_set w = (if u = w then {v} else ∅) ∪ (if v = w then {u} else ∅) :=
begin
  have := neighbor_set_from_edge_set_insert ∅ u v w h,
  simp only [insert_emptyc_eq] at this,
  rw [this],
  simp,
end

theorem neighbor_finset_from_edge_set_insert [decidable_eq V]
  (s : set (sym2 V)) (u v w : V)
  [fintype ((from_edge_set (insert ⟦(u, v)⟧ s)).neighbor_set w)]
  [fintype ((from_edge_set s).neighbor_set w)]
  (h : u ≠ v) :
  (from_edge_set (insert ⟦(u, v)⟧ s)).neighbor_finset w =
    (if u = w then {v} else ∅) ∪ (if v = w then {u} else ∅) ∪ (from_edge_set s).neighbor_finset w :=
begin
  ext x,
  rw [mem_neighbor_finset, ← mem_neighbor_set, neighbor_set_from_edge_set_insert _ _ _ _ h],
  obtain (h1 | h1) := eq_or_ne u w; obtain (h2 | h2) := eq_or_ne v w; simp [h1, h2],
end

theorem neighbor_finset_from_edge_set_singleton [decidable_eq V]
  (u v w : V)
  [fintype ((from_edge_set {⟦(u, v)⟧}).neighbor_set w)]
  (h : u ≠ v) :
  (from_edge_set {⟦(u, v)⟧}).neighbor_finset w = (if u = w then {v} else ∅) ∪ (if v = w then {u} else ∅) :=
begin
  ext x,
  rw [mem_neighbor_finset, ← mem_neighbor_set, neighbor_set_from_edge_set_singleton _ _ _ h],
  obtain (h1 | h1) := eq_or_ne u w; obtain (h2 | h2) := eq_or_ne v w; simp [h1, h2],
end

noncomputable
instance [fintype V] (G : simple_graph V) :
  fintype {m : simple_graph V | m ≤ G ∧ m.is_perfect_matching} :=
fintype.of_finite _

/-- A finite graph is *bognadov* if it has at least three perfect matchings and if every
pair of distinct perfect matchings are disjoint. -/
structure bogdanov [fintype V] (G : simple_graph V) : Prop :=
(suff_matchings : fintype.card {m : simple_graph V | m ≤ G ∧ m.is_perfect_matching} ≥ 3)
(disjointness : ∀ (m m' : simple_graph V), m ≤ G ∧ m' ≤ G ∧
  m.is_perfect_matching → m'.is_perfect_matching → m ≠ m' → disjoint m m')

def k4_matching_1 : simple_graph (fin 4) :=
from_edge_set {⟦(0,1)⟧, ⟦(2,3)⟧}

lemma fin4_aux (i : fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 :=
begin
  fin_cases i; dec_trivial
end

theorem k4_matching_1_is_matching : k4_matching_1.is_perfect_matching :=
begin
  classical,
  simp only [k4_matching_1, is_perfect_matching_iff_forall_degree],
  intro v,
  obtain (rfl | rfl | rfl | rfl) := fin4_aux v,
  simp only [degree, neighbor_finset_from_edge_set_insert, neighbor_finset_from_edge_set_singleton] {discharger := `[simp]},
  rw [neighbor_finset_from_edge_set_singleton], simp,
end

def k4_matching_2 : simple_graph (fin 4) :=
from_edge_set {⟦(0,2)⟧, ⟦(1,3)⟧}

def k4_matching_3 : simple_graph (fin 4) :=
from_edge_set {⟦(0,3)⟧, ⟦(1,2)⟧}

lemma k4_matchings_eq :
  {m : simple_graph (fin 4) | m.is_perfect_matching}
    = {k4_matching_1, k4_matching_2, k4_matching_3} :=
begin
  ext m,
  simp only [set.mem_set_of_eq, set.mem_insert_iff, set.mem_singleton_iff],
  split,
  sorry,
  { rintro (rfl | rfl | rfl);
      simp only [is_perfect_matching, k4_matching_1, k4_matching_2, k4_matching_3,
        from_edge_set_adj, set.mem_insert_iff, quotient.eq, sym2.rel_iff, set.mem_singleton_iff, ne.def];
      simp only [exists_unique],
    intro v, obtain (rfl | rfl | rfl | rfl) := fin4_aux v, simp,

  }
end

theorem k4_bognadov : (⊤ : simple_graph (fin 4)).bogdanov :=
begin
  split,
  {

  },
end

-- https://mathoverflow.net/questions/267002/graphs-with-only-disjoint-perfect-matchings
lemma k4_if_perfect_matchings_disjoint {V : Type*} [fintype V]
  (G : simple_graph V)
  (hc : fintype.card {m : simple_graph V | m ≤ G ∧ m.is_perfect_matching} ≥ 3)
  (hd : ∀ (m m' : simple_graph V), m ≤ G ∧ m' ≤ G ∧
    m.is_perfect_matching → m'.is_perfect_matching → m ≠ m' → disjoint m m') :
  fintype.card V = 4 ∧ G = ⊤ :=
sorry

end simple_graph
