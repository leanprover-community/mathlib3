import combinatorics.simple_graph.matching
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.coloring
import combinatorics.simple_graph.metric

noncomputable theory

namespace simple_graph
universes u
variables {V : Type u} {G : simple_graph V}

theorem disjoint_iff (G G' : simple_graph V) :
  disjoint G G' ↔ ∀ v w, G.adj v w → G'.adj v w → false :=
begin
  split,
  { intros hd v w h h',
    exact hd inf_le_left inf_le_right ⟨h, h'⟩, },
  { intros h H hH hH' v w hvw,
    exact h _ _ (hH hvw) (hH' hvw), }
end

/-- A recursor that is kinder to `v` in `G.walk u v`. -/
@[elab_as_eliminator]
protected def walk.rec' {v : V} {motive : Π (u : V), G.walk u v → Sort*}
  (hnil : motive v walk.nil)
  (hcons : Π {u w : V} (h : G.adj u w) (p : G.walk w v), motive w p → motive u (walk.cons h p)) :
  Π {u : V} (p : G.walk u v), motive u p
| _ walk.nil := hnil
| _ (walk.cons h p) := hcons h p (walk.rec' p)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.snd.length)⟩]}

lemma walk.drop_until_eq_of_length_eq [decidable_eq V]
  {u v w : V} (p : G.walk u v) (hw : w ∈ p.support)
  (h : (p.drop_until w hw).length = p.length) :
  ∃ (h : w = u), (p.drop_until w hw).copy h rfl = p :=
begin
  have := congr_arg walk.length (walk.take_spec p hw),
  rw [walk.length_append, h, add_left_eq_self] at this,
  cases walk.eq_of_length_eq_zero this,
  refine ⟨rfl, _⟩,
  have key := walk.take_spec p hw,
  rw [walk.length_eq_zero_iff] at this,
  rw [this, walk.nil_append] at key,
  exact key,
end

lemma walk.bypass_eq_of_length_le [decidable_eq V]
  {u v : V} (p : G.walk u v) (h : p.length ≤ p.bypass.length) :
  p.bypass = p :=
begin
  induction p with a b c d he p ih,
  { simp only [walk.bypass], },
  { simp only [walk.bypass],
    split_ifs with hb,
    { exfalso,
      simp only [hb, walk.bypass, walk.length_cons, dif_pos] at h,
      have := h.trans ((walk.length_drop_until_le p.bypass hb).trans (walk.length_bypass_le p)),
      exact nat.not_succ_le_self _ this, },
    { simp only [hb, walk.bypass, walk.length_cons, not_false_iff, dif_neg, add_le_add_iff_right] at h,
      simp [ih h], } }
end

protected
lemma reachable.exists_path_of_dist {u v : V} (hr : G.reachable u v) :
  ∃ (p : G.walk u v), p.is_path ∧ p.length = G.dist u v :=
begin
  classical,
  obtain ⟨p, h⟩ := hr.exists_walk_of_dist,
  refine ⟨p, _, h⟩,
  have : p.bypass = p,
  { have := calc p.length = G.dist u v : h
                      ... ≤ p.bypass.length : dist_le p.bypass,
    exact walk.bypass_eq_of_length_le p this },
  rw [← this],
  apply walk.bypass_is_path,
end

lemma dist_eq_one_of_adj {u v : V} (h : G.adj u v) :
  G.dist u v = 1 :=
begin
  apply le_antisymm (dist_le h.to_walk),
  obtain (hd | hd) := eq_or_ne (G.dist u v) 0,
  { rw hd,
    rw [h.reachable.dist_eq_zero_iff] at hd,
    cases hd,
    cases h.ne rfl },
  { rw [← nat.one_le_iff_ne_zero] at hd,
    exact hd, },
end

protected
lemma reachable.dist_triangle {u v w : V} (huv : G.reachable u v) (hvw : G.reachable v w) :
  G.dist u w ≤ G.dist u v + G.dist v w :=
begin
  obtain ⟨p, hp⟩ := huv.exists_walk_of_dist,
  obtain ⟨q, hq⟩ := hvw.exists_walk_of_dist,
  rw [← hp, ← hq, ← walk.length_append],
  apply dist_le,
end

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
  rw [disjoint_iff] at hd,
  exact hd _ _ hg hh,
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

section colorings
/-! ### Colorings and matchings

In this section we prove that the union of two perfect matchings is two-colorable (i.e., bipartite).
-/

def connected_component.out (c : G.connected_component) : V := c.out

lemma connected_component.out_eq (c : G.connected_component) :
  G.connected_component_mk c.out = c := quot.out_eq _

lemma reachable_out_connected_component_mk (G : simple_graph V) (v : V) :
  G.reachable (G.connected_component_mk v).out v :=
begin
  rw [← connected_component.eq, connected_component.out_eq],
end

/-- The distance from a vertex to an arbitrary basepoint in its connected component. -/
def basepoint_dist (G : simple_graph V) (v : V) : ℕ :=
G.dist v (G.connected_component_mk v).out

def basepoint_mod2dist (G : simple_graph V) (v : V) : bool := even (G.basepoint_dist v)

/-- A walk whose edges alternate between two graphs. A `p : alt_graph G G' s e v w` is
a walk where if `s` is true it starts incident to `G` and if `e` is true ends incident to `G'`.
This way if the inner bools match up they can be appended. -/
inductive alt_walk (G G' : simple_graph V) : bool → bool → V → V → Type u
| nil (b : bool) (v : V) : alt_walk b b v v
| cons1 (e : bool) (u v w : V) (h : G.adj u v) (p : alt_walk ff e v w) : alt_walk tt e u w
| cons2 (e : bool) (u v w : V) (h : G'.adj u v) (p : alt_walk tt e v w) : alt_walk ff e u w

/-- Converts an alternating walk to a walk on `G ⊔ G'`. -/
def alt_walk.to_walk {G G' : simple_graph V} :
  Π {s e : bool} {u v : V}, alt_walk G G' s e u v → (G ⊔ G').walk u v
| _ _ _ _ (alt_walk.nil _ _) := walk.nil
| _ _ _ _ (alt_walk.cons1 _ _ _ _ h p) := walk.cons (or.inl h) (alt_walk.to_walk p)
| _ _ _ _ (alt_walk.cons2 _ _ _ _ h p) := walk.cons (or.inr h) (alt_walk.to_walk p)

def alt_walk.append {G G' : simple_graph V} :
  Π {s e e' : bool} {u v w : V},
    alt_walk G G' s e u v → alt_walk G G' e e' v w → alt_walk G G' s e' u w
| _ _ _ _ _ _ (alt_walk.nil _ _) q := q
| _ _ _ _ _ _ (alt_walk.cons1 _ _ _ _ h p) q :=
  alt_walk.cons1 _ _ _ _ h (alt_walk.append p q)
| _ _ _ _ _ _ (alt_walk.cons2 _ _ _ _ h p) q :=
  alt_walk.cons2 _ _ _ _ h (alt_walk.append p q)

lemma alt_walk.to_walk_append {G G' : simple_graph V}
  {s e e' : bool} {u v w : V}
  (p : alt_walk G G' s e u v) (q : alt_walk G G' e e' v w) :
  (p.append q).to_walk = p.to_walk.append q.to_walk :=
by induction p; simp! [*]


/-- The concatenation of the reverse of the first walk with the second walk. -/
protected def alt_walk.reverse_aux {G G' : simple_graph V} :
  Π {s e e' : bool} {u v w : V},
    alt_walk G G' s e u v → alt_walk G G' (!s) e' u w → alt_walk G G' (!e) e' v w
| _ _ _ _ _ _ (alt_walk.nil _ _) q := q
| _ _ _ _ _ _ (alt_walk.cons1 _ _ _ _ h p) q :=
  alt_walk.reverse_aux p (alt_walk.cons1 _ _ _ _ h.symm q)
| _ _ _ _ _ _ (alt_walk.cons2 _ _ _ _ h p) q :=
  alt_walk.reverse_aux p (alt_walk.cons2 _ _ _ _ h.symm q)

/-- The walk in reverse. -/
def alt_walk.reverse {G G' : simple_graph V} {u v : V} {s e : bool}
  (p : alt_walk G G' s e u v) : alt_walk G G' (!e) (!s) v u := p.reverse_aux (alt_walk.nil _ _)

lemma alt_walk.reverse_aux_to_walk {G G' : simple_graph V}
  {s e e' : bool} {u v w : V}
  (p : alt_walk G G' s e u v) (q : alt_walk G G' (!s) e' u w) :
  (alt_walk.reverse_aux p q).to_walk = walk.reverse_aux p.to_walk q.to_walk :=
begin
  induction p generalizing q,
  refl,
  simp! [p_ih], refl,
  simp! [p_ih], refl,
end

lemma alt_walk.to_walk_reverse {G G' : simple_graph V} {u v : V} {s e : bool}
  (p : alt_walk G G' s e u v) :
  p.reverse.to_walk = p.to_walk.reverse :=
begin
  rw [alt_walk.reverse, alt_walk.reverse_aux_to_walk],
  refl,
end

/-- Since we're keeping track of incidences, we can tell whether the length of
an alternating walk is even. -/
theorem even_alt_walk_length {G G' : simple_graph V} {s e : bool} {u v : V}
  (p : alt_walk G G' s e u v) : even p.to_walk.length ↔ s = e :=
begin
  induction p,
  { simp [alt_walk.to_walk], },
  { simp only [alt_walk.to_walk, nat.even_add_one, p_ih, walk.length_cons],
    cases p_e; simp, },
  { simp only [alt_walk.to_walk, nat.even_add_one, p_ih, walk.length_cons],
    cases p_e; simp, },
end

/-- Whether the walk is nil or whose first edge is in G. -/
def walk.starts_with_fst {G G' : simple_graph V} :
  Π {u v : V}, (G ⊔ G').walk u v → Prop
| _ _ walk.nil := tt
| _ _ (walk.cons' u v w h p) := G.adj u v

/-- Whether the walk is nil or whose first edge is in G'. -/
def walk.starts_with_snd {G G' : simple_graph V} :
  Π {u v : V}, (G ⊔ G').walk u v → Prop
| _ _ walk.nil := tt
| _ _ (walk.cons' u v w h p) := G'.adj u v

lemma walk.starts_with_fst_or_snd
  {G G' : simple_graph V}
  {u v : V} (p : (G ⊔ G').walk u v) :
  p.starts_with_fst ∨ p.starts_with_snd :=
begin
  cases p;
    simp [walk.starts_with_fst, walk.starts_with_snd],
  assumption,
end

/-- A boolean-controlled version of `walk.starts_with_fst` and `walk.starts_with_end`. -/
def walk.starts_with_opt {G G' : simple_graph V}
  {u v : V} (p : (G ⊔ G').walk u v) (b : bool) : Prop :=
  if b then walk.starts_with_fst p else walk.starts_with_snd p

lemma walk.starts_with_opt_append_of_ne_nil
  {G G' : simple_graph V}
  {u v w : V} (p : (G ⊔ G').walk u v) (q : (G ⊔ G').walk v w) (b : bool)
  (hne : p.length ≠ 0) :
  (p.append q).starts_with_opt b ↔ p.starts_with_opt b :=
begin
  cases p,
  { exfalso, simpa using hne, },
  { simp! [walk.starts_with_opt], }
end

lemma walk.start_with_opt_tail
  {m m' : simple_graph V}
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  {u w v : V} (huv : (m ⊔ m').adj u v) (p : (m ⊔ m').walk v w)
  (hp : (walk.cons huv p).is_path)
  (s : bool)
  (hs : (walk.cons huv p).starts_with_opt s) :
  p.starts_with_opt (!s) :=
begin
  cases p,
  { simp! [walk.starts_with_opt], },
  { simp only [walk.cons_is_path_iff, not_or_distrib, walk.support_cons, list.mem_cons_iff] at hp,
    simp! [walk.starts_with_opt],
    simp! [walk.starts_with_opt] at hs,
    cases s,
    { simp only [coe_sort_ff, is_empty.forall_iff, if_true],
      simp only [coe_sort_ff, if_false] at hs,
      cases p_h,
      { assumption },
      { exfalso,
        cases hm'.is_matching.adj_unique hs.symm p_h,
        simpa using hp, } },
    { simp only [coe_sort_tt, forall_true_left, if_false],
      simp only [coe_sort_tt, if_true] at hs,
      cases p_h,
      { exfalso,
        cases hm.is_matching.adj_unique hs.symm p_h,
        simpa using hp, },
      { assumption } } }
end

/-- Given a path in the sup of two perfect matchings, convert it into an alternating walk. -/
def walk.matchings_lift_alt_walk_of_path {m m' : simple_graph V}
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching) :
  Π {u v : V} (p : (m ⊔ m').walk u v) (hp : p.is_path)
    (s : bool) (hs : p.starts_with_opt s),
    Σ (e : bool), alt_walk m m' s e u v
| _ _ walk.nil _ s _ := ⟨s, alt_walk.nil _ _⟩
| _ _ (walk.cons' u v w huv p) hp tt hs :=
  let r := walk.matchings_lift_alt_walk_of_path p
            (by { rw [walk.cons_is_path_iff] at hp, exact hp.1 })
            ff (walk.start_with_opt_tail hm hm' huv p hp tt hs)
  in ⟨r.1, alt_walk.cons1 _ _ _ _ hs r.2⟩
| _ _ (walk.cons' u v w huv p) hp ff hs :=
  let r := walk.matchings_lift_alt_walk_of_path p
            (by { rw [walk.cons_is_path_iff] at hp, exact hp.1 })
            tt (walk.start_with_opt_tail hm hm' huv p hp ff hs)
  in ⟨r.1, alt_walk.cons2 _ _ _ _
            begin simpa [walk.starts_with_opt, walk.starts_with_snd] using hs end r.2⟩

theorem walk.matchings_lift_alt_walk_of_path_to_walk {m m' : simple_graph V}
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  {u v : V} (p : (m ⊔ m').walk u v) (hp : p.is_path)
  (s : bool) (hs : p.starts_with_opt s) :
  (p.matchings_lift_alt_walk_of_path hm hm' hp s hs).2.to_walk = p :=
begin
  induction p with _ u v w huv p ih generalizing s,
  { simp! },
  { have := walk.start_with_opt_tail hm hm' huv p hp s hs,
    rw [walk.cons_is_path_iff] at hp,
    have := ih hp.1 (!s) this,
    cases s; simp! [*], },
end

theorem walk.reverse_starts_with_opt_fst {m m' : simple_graph V}
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  {u v : V} (p : (m ⊔ m').walk u v) (hp : p.is_path)
  (s : bool) (hs : p.starts_with_opt s) :
  p.reverse.starts_with_opt (!(p.matchings_lift_alt_walk_of_path hm hm' hp s hs).1) :=
begin
  induction p generalizing s,
  { simp! [walk.starts_with_opt], },
  { simp only [walk.reverse_cons],
    by_cases hne : p_p.length = 0,
    { cases p_p, cases s; simp! [walk.starts_with_opt]; simp! [walk.starts_with_opt] at hs,
      exact hs.symm, exact hs.symm,
      exfalso, simpa using hne, },
    rw [walk.starts_with_opt_append_of_ne_nil], swap, simp [hne],
    cases s; rw [walk.matchings_lift_alt_walk_of_path],
    dsimp, apply p_ih,
    dsimp, apply p_ih, }
end

theorem walk.matchings_paths_unique_of_starts_with {m m' : simple_graph V}
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  {u v : V} (p q : (m ⊔ m').walk u v) (hp : p.is_path) (hq : q.is_path)
  (s : bool) (hsp : p.starts_with_opt s) (hsq : q.starts_with_opt s) :
  p = q :=
begin
  induction p generalizing q s,
  { rw [walk.is_path_iff_eq_nil] at hq,
    exact hq.symm, },
  { have keyp := walk.start_with_opt_tail hm hm' p_h p_p hp _ hsp,
    cases q,
    { rw [walk.is_path_iff_eq_nil] at hp,
      exact hp },
    { have keyq := walk.start_with_opt_tail hm hm' q_h q_p hq _ hsq,
      simp only [walk.cons_is_path_iff] at hp hq,
      have : p_v = q_v,
      { cases s; simp [walk.starts_with_opt, walk.starts_with_fst, walk.starts_with_snd] at hsp hsq,
        exact hm'.is_matching.adj_unique hsp hsq,
        exact hm.is_matching.adj_unique hsp hsq, },
      cases this,
      simp,
      exact p_ih hp.1 q_p (!s) hq.1 keyp keyq, } }
end

/-| _ _ (walk.nil) _ := ⟨tt, alt_walk.nil tt _⟩
-- Since nil can't really decide what the endpoint bools should be, we need another base case:
| _ _ (walk.cons' u v _ h walk.nil) _ :=
  if ha : m.adj u v then
    ⟨tt, ff, alt_walk.cons1 _ _ _ _ ha (alt_walk.nil _ _)⟩
  else
    have ha : m'.adj u v := by simpa [ha] using h,
    ⟨ff, tt, alt_walk.cons2 _ _ _ _ ha (alt_walk.nil _ _)⟩
| _ _ (walk.cons' u v w h p) hp :=
  let r := walk.matchings_lift_alt_walk_of_path p
    (by { rw [walk.cons_is_path_iff] at hp, exact hp.1 }) in
  match r with
  | ⟨tt, e, r'⟩ :=
    have ha : m'.adj u v := by {  },
    sorry
  | ⟨ff, e, r'⟩ := sorry-/


/--
Main idea of proof: given two paths between the same vertices, they're either the same
or they start and end in different matchings.
-/
lemma parity_path_sup_matchings (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  {v w : V} (p q : (m ⊔ m').walk v w) (hp : p.is_path) (hq : q.is_path) :
  even p.length ↔ even q.length :=
begin
  classical,
  have Pstartfst : p.starts_with_opt p.starts_with_fst,
  { cases p.starts_with_fst_or_snd with hpfst hpfst;
      simp [hpfst, walk.starts_with_opt, em'], },
  cases hP : p.matchings_lift_alt_walk_of_path hm hm' hp p.starts_with_fst Pstartfst with Pe P,
  have Qstartfst : q.starts_with_opt q.starts_with_fst,
  { cases q.starts_with_fst_or_snd with hpfst hpfst;
      simp [hpfst, walk.starts_with_opt, em'], },
  cases hQ : q.matchings_lift_alt_walk_of_path hm hm' hq q.starts_with_fst Qstartfst with Qe Q,
  obtain (h | h) := eq_or_ne p.starts_with_fst q.starts_with_fst,
  { rw walk.matchings_paths_unique_of_starts_with hm hm' _ _ hp hq p.starts_with_fst Pstartfst,
    rw [h], exact Qstartfst, },
  have Pre : p.reverse.starts_with_opt (!Pe),
  { convert (walk.reverse_starts_with_opt_fst hm hm' p hp _ Pstartfst),
    rw hP, },
  have Qre : q.reverse.starts_with_opt (!Qe),
  { convert (walk.reverse_starts_with_opt_fst hm hm' q hq _ Qstartfst),
    rw hQ, },
  obtain (rfl | hPQ) := eq_or_ne Pe Qe,
  { have := walk.matchings_paths_unique_of_starts_with hm hm' p.reverse q.reverse
      hp.reverse hq.reverse
      _ Pre Qre,
    apply_fun walk.length at this,
    simp only [walk.length_reverse] at this,
    rw [this], },
  { have hPlen : P.to_walk.length = p.length,
    { have := congr_arg walk.length
        (walk.matchings_lift_alt_walk_of_path_to_walk hm hm' p hp _ Pstartfst),
      rw [hP] at this,
      exact this, },
    have hQlen : Q.to_walk.length = q.length,
    { have := congr_arg walk.length
        (walk.matchings_lift_alt_walk_of_path_to_walk hm hm' q hq _ Qstartfst),
      rw [hQ] at this,
      exact this, },
    rw [← hPlen, ← hQlen, even_alt_walk_length, even_alt_walk_length],
    simp [not_iff] at h,
    cases Pe; cases Qe; simp at hPQ; try { exact false.elim hPQ }; simp [h.symm], },
end

lemma parity_path_sup_matchings_dist (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  {v w : V} (p : (m ⊔ m').walk v w) (hp : p.is_path) :
  even p.length ↔ even ((m ⊔ m').dist v w) :=
begin
  obtain ⟨q, hq, hd⟩ := p.reachable.exists_path_of_dist,
  rw [← hd],
  apply parity_path_sup_matchings _ _ hm hm' _ _ hp hq,
end

/-
lemma even_length_loop_sup_matchings (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  {v : V} (p : (m ⊔ m').walk v v) : even p.length :=
begin
  induction hn : p.length using nat.strong_induction_on with n ih generalizing p,
  by_cases hc : p.is_cycle,
  { sorry

  },
  cases p with _ _ w _ hvw p,
  { cases hn, exact even_zero, },
  { simp only [walk.cons_is_cycle_iff, not_and, not_not] at hc,

  }
end
-/

/-lemma even_length_loop_sup_matchings (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  {v : V} (p : (m ⊔ m').walk v v) : even p.length :=
begin
  induction hn : p.length using nat.strong_induction_on with n ih generalizing p,
  by_cases hc : p.is_cycle,
  { sorry

  },
  { rw [← hn],
    cases p,
    { simp only [walk.length_nil, even_zero], },
    --simp only [walk.length_cons] at hn,
    simp only [walk.cons_is_cycle_iff, not_and, not_not] at hc,
    by_cases hpp : p_p.is_path,
    { specialize hc hpp,

    },
  },
end-/

lemma even_basepoint_dist_sup_matchings (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  {v w : V} (hvw : (m ⊔ m').adj v w) :
  even ((m ⊔ m').basepoint_dist v) ↔ ¬even ((m ⊔ m').basepoint_dist w) :=
begin
  classical,
  let c := (m ⊔ m').connected_component_mk v,
  have : c = (m ⊔ m').connected_component_mk w,
  { exact connected_component.sound hvw.reachable, },
  have hvr : (m ⊔ m').reachable v c.out := (reachable_out_connected_component_mk (m ⊔ m') v).symm,
  have hwr : (m ⊔ m').reachable w c.out := hvw.reachable.symm.trans hvr,
  obtain ⟨p, hp, hpw⟩ := hvr.exists_path_of_dist,
  obtain ⟨q, hq, hqw⟩ := hwr.exists_path_of_dist,
  simp only [basepoint_dist, ← this, ← hpw, ← hqw],
  have htri1 := reachable.dist_triangle hvw.reachable hwr,
  have htri2 := reachable.dist_triangle hvw.symm.reachable hvr,
  simp [hvw, hvw.symm, dist_eq_one_of_adj] at htri1 htri2,
  clear hvr hwr this,
  by_cases hq' : (walk.cons hvw q).is_path,
  { rw parity_path_sup_matchings m m' hm hm' _ _ hp hq',
    simp only [nat.even_add_one, walk.length_cons], },
  { simp only [walk.cons_is_path_iff, not_and, not_not, hq, true_implies_iff] at hq',
    induction q using simple_graph.walk.rec',
    { exfalso, simp at hq', simp [hq'] at hvw, exact hvw, },
    { simp only [walk.support_cons, list.mem_cons_iff] at hq',
      obtain (rfl | hq') := hq',
      { cases hvw.ne rfl, },
      { simp [← hpw, ← hqw] at htri1 htri2,
        simp only [add_comm, add_le_add_iff_left] at htri2,
        have := walk.length_drop_until_le _ hq',
        have := (this.trans htri2).trans hpw.le,
        have := le_antisymm this (dist_le _),
        rw [hpw, ← this] at htri2,
        obtain ⟨rfl, hq'⟩ := walk.drop_until_eq_of_length_eq _ hq'
          (le_antisymm (walk.length_drop_until_le _ hq') htri2),
        simp only [walk.copy_rfl_rfl] at hq',
        rw [hq', ← hpw] at this,
        simp [this, nat.even_add_one], } } },
end

/-
lemma even_basepoint_dist_sup_matchings (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  {v w : V} (hvw : (m ⊔ m').adj v w) :
  even ((m ⊔ m').basepoint_dist v) ↔ ¬even ((m ⊔ m').basepoint_dist w) :=
begin
  have : (m ⊔ m').connected_component_mk v = (m ⊔ m').connected_component_mk w,
  { exact connected_component.sound hvw.reachable, },
  simp only [basepoint_dist, this],
  obtain ⟨pw, hpw⟩ := (reachable_out_connected_component_mk (m ⊔ m') w).exists_walk_of_dist,
  have h := (reachable_out_connected_component_mk (m ⊔ m') w).trans hvw.symm.reachable,
  obtain ⟨pv, hpv⟩ := h.exists_walk_of_dist,
  rw [← hpw, ← hpv],
  have : even (walk.cons hvw.symm (pv.reverse.append pw)).length :=
    even_length_loop_sup_matchings m m' hm hm' _,
  simp only [nat.even_add, not_iff, walk.length_cons, walk.length_append, walk.length_reverse,
    nat.not_even_one, iff_false] at this,
  simp [← this],
end
-/

lemma basepoint_mod2dist_sup_matchings (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  {v w : V} (hvw : (m ⊔ m').adj v w) :
  (m ⊔ m').basepoint_mod2dist v ≠ ((m ⊔ m').basepoint_mod2dist w) :=
begin
  simp only [basepoint_mod2dist, even_basepoint_dist_sup_matchings m m' hm hm' hvw,
    bool.to_bool_not, ne.def, bool.bnot_not_eq],
end

/-- The union of two perfect matchings is a bipartite graph. -/
def mod2dist_coloring (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching) :
  (m ⊔ m').coloring bool :=
coloring.mk (m ⊔ m').basepoint_mod2dist
begin
  intros v w hvw,
  exact basepoint_mod2dist_sup_matchings m m' hm hm' hvw,
end

end colorings

/-- Given two perfect matchings, alternately follow one then the other to create
a sequence of vertices. -/
noncomputable!
def ham_cycle_aux (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching) (v : V) : Π (n : ℕ), V
| 0 := v
| (n+1) := if even n then hm.other (ham_cycle_aux n) else hm'.other (ham_cycle_aux n)

@[simp]
lemma ham_cycle_aux_odd (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching) (v : V) (k : ℕ) :
  ham_cycle_aux m m' hm hm' v (2 * k + 1) = hm.other (ham_cycle_aux m m' hm hm' v (2 * k)) :=
by simp [ham_cycle_aux]

@[simp]
lemma ham_cycle_aux_even_succ (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching) (v : V) (k : ℕ) :
  ham_cycle_aux m m' hm hm' v (2 * (k + 1))
    = hm'.other (hm.other (ham_cycle_aux m m' hm hm' v (2 * k))) :=
by simp [nat.mul_succ, ham_cycle_aux, nat.even_add_one]

lemma ham_cycle_aux_prop_even (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching) (v : V) (n : ℕ) (hn : even n) :
  m.adj (ham_cycle_aux m m' hm hm' v n) (ham_cycle_aux m m' hm hm' v (n + 1)) :=
begin
  simp [ham_cycle_aux, hn, hm.adj_other],
end

lemma ham_cycle_aux_prop_not_even (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching) (v : V) (n : ℕ) (hn : ¬even n) :
  m'.adj (ham_cycle_aux m m' hm hm' v n) (ham_cycle_aux m m' hm hm' v (n + 1)) :=
begin
  simp [ham_cycle_aux, hn, hm'.adj_other],
end

-- lemma ham_cycle_aux_prop (m m' : simple_graph V)
--   (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
--   (k : ℕ) (v : V) :
--   m.adj (ham_cycle_aux m m' hm hm' v (2 * k)) (ham_cycle_aux m m' hm hm' v (2 * k + 1))
--     ∧ m'.adj (ham_cycle_aux m m' hm hm' v (2 * k + 1)) (ham_cycle_aux m m' hm hm' v (2 * k + 2)) :=
-- begin
--   induction k with k ih generalizing v,
--   { simp [ham_cycle_aux, hm.adj_other, hm'.adj_other], },
--   { simp [ham_cycle_aux, nat.even_add_one] at ih,
--     simp [nat.mul_succ, ham_cycle_aux, (ih _).1, (ih _).2, nat.even_add_one], },
-- end

lemma adj_ham_cycle_aux (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching) (v : V) (n : ℕ) :
  (m ⊔ m').adj (ham_cycle_aux m m' hm hm' v n) (ham_cycle_aux m m' hm hm' v (n + 1)) :=
begin
  cases n,
  { simp [ham_cycle_aux, hm.adj_other, hm'.adj_other], },
  { simp only [ham_cycle_aux],
    by_cases he : even n,
    { simp [he, nat.even_add_one],
      right,
      apply hm'.adj_other },
    { simp [he, nat.even_add_one],
      left,
      apply hm.adj_other }, }
end

/--
Given two perfect matchings, the walk associated to `ham_cycle_aux`.
-/
noncomputable!
def ham_cycle_aux_walk (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching) (v : V) :
  Π (n : ℕ), (m ⊔ m').walk v (ham_cycle_aux m m' hm hm' v n)
| 0 := walk.nil
| (n+1) := (ham_cycle_aux_walk n).concat (adj_ham_cycle_aux m m' hm hm' v n)

lemma ham_cycle_aux_not_injective (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching) (v : V) [finite V] :
  ¬ function.injective (ham_cycle_aux m m' hm hm' v) :=
not_injective_infinite_finite _

lemma _root_.nat.not_injective {α : Type*} (f : ℕ → α) (hf : ¬ function.injective f) :
  ∃ a b, a < b ∧ f a = f b :=
begin
  rw [function.injective] at hf,
  push_neg at hf,
  obtain ⟨a, b, h, hn⟩ := hf,
  cases ne.lt_or_lt hn with hn hn,
  { exact ⟨a, b, hn, h⟩, },
  { exact ⟨b, a, hn, h.symm⟩, }
end

lemma ham_cycle_aux_even_periodic' (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  (hd : disjoint m m')
  (v : V) (a b : ℕ)
  (h : ham_cycle_aux m m' hm hm' v (a + b) = ham_cycle_aux m m' hm hm' v a) :
  even b :=
begin
  obtain (rfl | hpos) := nat.eq_zero_or_pos b,
  { exact even_zero },
  let b' := Inf { b' | 0 < b' ∧
    ham_cycle_aux m m' hm hm' v (a + b') = ham_cycle_aux m m' hm hm' v a },
  suffices : even b',
  {

  },
end

lemma ham_cycle_aux_eq_of_twosucc_eq (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  (v : V) (a b : ℕ)
  (h : ham_cycle_aux m m' hm hm' v (a + 2 * b) = ham_cycle_aux m m' hm hm' v a) :
  ham_cycle_aux m m' hm hm' v (2 * b) = ham_cycle_aux m m' hm hm' v 0 :=
begin
  induction a with a ih,
  { simpa only [mul_zero, zero_add] using h},
  { simp only [nat.mul_succ, nat.succ_add, ham_cycle_aux, nat.even_add_one, nat.even_add,
      even.mul_right, even_zero, not_true,
      not_false_iff, iff_self, if_true, if_false, iff_false, iff_true] at h,
    by_cases hea : even a,
    { simp only [hea, if_true] at h,
      replace h := hm.other_involutive.injective h,
      exact ih h, },
    { simp only [hea, if_false] at h,
      replace h := hm'.other_involutive.injective h,
      exact ih h, } }
end

lemma ham_cycle_aux_fwd_periodic (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  (v : V) (a b c : ℕ) (he : even a ↔ even b)
  (h : ham_cycle_aux m m' hm hm' v a = ham_cycle_aux m m' hm hm' v b) :
  ham_cycle_aux m m' hm hm' v (a + c) = ham_cycle_aux m m' hm hm' v (b + c) :=
begin
  induction c with c ih,
  exact h,
  simp [nat.add_succ, ham_cycle_aux, ih, nat.even_add, he],
end

lemma ham_cycle_aux_eq_of_twosucc_eq' (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  (v : V) (a b : ℕ)
  (h : ham_cycle_aux m m' hm hm' v (a + b) = ham_cycle_aux m m' hm hm' v a) :
  ham_cycle_aux m m' hm hm' v (2 * b) = ham_cycle_aux m m' hm hm' v 0 :=
begin
  apply ham_cycle_aux_eq_of_twosucc_eq m m' hm hm' v a,
  have := ham_cycle_aux_fwd_periodic m m' hm hm' v (a + b) a b _ h,
  rw [two_mul, ← add_assoc, this, h],
  simp [nat.even_add],
end

lemma ham_cycle_aux_eq_of_succ_eq (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  (hd : disjoint m m')
  (v : V) (a b : ℕ)
  (h : ham_cycle_aux m m' hm hm' v (a + b) = ham_cycle_aux m m' hm hm' v a) :
  ham_cycle_aux m m' hm hm' v b = ham_cycle_aux m m' hm hm' v 0 :=
begin
  induction a with a ih generalizing b,
  { simpa using h },
  { simp [nat.succ_add, ham_cycle_aux] at h,
    by_cases hea : even a,
    { by_cases heb : even b,
      { simp [nat.even_add, hea, heb] at h,
        exact ih _ (hm.other_involutive.injective h), },
      { cases b,
        { simp [nat.even_add, hea, heb] at h, },
        { simp [nat.even_add_one] at heb,
          simp [nat.even_add, hea, heb, ham_cycle_aux, nat.add_succ, nat.even_add_one] at h,

        }
      }
    }
  }
end

lemma ham_cycle_aux_eq_of_succ_eq' (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching)
  (hd : disjoint m m')
  (v : V) (a b : ℕ)
  (h : ham_cycle_aux m m' hm hm' v (a + 1) = ham_cycle_aux m m' hm hm' v (b + 1)) :
  ham_cycle_aux m m' hm hm' v a = ham_cycle_aux m m' hm hm' v b :=
begin
  rw disjoint_iff at hd,
  simp [ham_cycle_aux] at h,
  by_cases hea : even a,
  { by_cases heb : even b,
    { simp only [hea, heb, if_true] at h,
      exact hm.other_involutive.injective h, },
    { exfalso,
      simp only [hea, heb, if_true, if_false] at h,
      have k1 := ham_cycle_aux_prop_even m m' hm hm' v a hea,
      simp [ham_cycle_aux, hea, h] at k1,
      have k2 := ham_cycle_aux_prop_not_even m m' hm hm' v _ heb,
      simp [ham_cycle_aux, heb, ← h] at k2,
    },

  }
end

lemma aoeu (m m' : simple_graph V)
  (hm : m.is_perfect_matching) (hm' : m'.is_perfect_matching) (v : V) [fintype V] :
  ∃ n, 0 < n ∧ ham_cycle_aux m m' hm hm' v n = v :=
begin
  obtain ⟨a, b, hab, h⟩ := nat.not_injective _ (ham_cycle_aux_not_injective m m' hm hm' v),
  use [b - a, nat.sub_pos_of_lt hab],
end


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
