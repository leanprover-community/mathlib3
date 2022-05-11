/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.connectivity_to_merge
import data.nat.parity
import tactic.derive_fintype
import tactic.fin_cases
/-!

# Eulerian trails

## Main definitions

* `simple_graph.walk.is_eulerian`

## Tags

Eulerian circuits

-/

namespace simple_graph
variables {V : Type*} {G : simple_graph V}

namespace walk
variables [decidable_eq V]

/-- An *Eulerian trail* (also known as an "Eulerian path") is a walk
`p` that visits every edge exactly once.  The lemma
`simple_graph.walk.is_eulerian.is_trail` shows these are trails.

Combine with `p.is_circuit` to get an Eulerian circuit (also known as an "Eulerian cycle"). -/
def is_eulerian {u v : V} (p : G.walk u v) : Prop :=
∀ e, e ∈ G.edge_set → p.edges.count e = 1

lemma is_eulerian.is_trail {u v : V} {p : G.walk u v}
  (h : p.is_eulerian) : p.is_trail :=
begin
  rw [is_trail_def, list.nodup_iff_count_le_one],
  intro e,
  by_cases he : e ∈ p.edges,
  { specialize h e (edges_subset_edge_set _ he),
    rw h, },
  { simp [he], },
end

lemma length_of_eulerian [fintype V] [decidable_rel G.adj]
  {u v : V} (p : G.walk u v) (h : p.is_eulerian) :
  p.length = G.edge_finset.card :=
begin
  rw [←length_edges, ←multiset.coe_card],
  have hnd := h.is_trail,
  rw is_trail_def at hnd,
  let f := finset.mk (p.edges : multiset (sym2 V)) hnd,
  change f.card = _,
  congr',
  ext e,
  simp,
  split,
  apply edges_subset_edge_set p,
  intro he,
  specialize h e he,
  rw ←list.count_pos,
  simp [h],
end

lemma is_eulerian_of_max_trail [fintype V] [decidable_rel G.adj]
  {u v : V} (p : G.walk u v) (h : p.is_trail) (hl : p.length = G.edge_finset.card) :
  p.is_eulerian :=
begin
  intros e he,
  apply list.count_eq_one_of_mem h.edges_nodup,
  rw [←length_edges, ←multiset.coe_card] at hl,
  let f := finset.mk (p.edges : multiset (sym2 V)) h.edges_nodup,
  change f.card = _ at hl,
  have : f ⊆ G.edge_finset,
  { intros e he,
    rw mem_edge_finset,
    simp at he,
    exact edges_subset_edge_set p he, },
  have : f = G.edge_finset,
  { apply finset.eq_of_subset_of_card_le this,
    rw hl, },
  rw [←mem_edge_finset, ←this] at he,
  exact he,
end

lemma is_eulerian_iff [fintype V] [decidable_rel G.adj]
  {u v : V} (p : G.walk u v) :
  p.is_eulerian ↔ p.is_trail ∧ p.length = G.edge_finset.card :=
begin
  split,
  { intro h,
    use h.is_trail,
    apply length_of_eulerian _ h, },
  { rintro ⟨h, hl⟩,
    exact is_eulerian_of_max_trail _ h hl, },
end

theorem list.countp_cons {α : Type*} (p : α → Prop) [decidable_pred p] (a : α) (l : list α) :
  list.countp p (a :: l) = list.countp p l + ite (p a) 1 0 :=
by { by_cases h : p a; simp [h] }

lemma is_trail.even_countp_edges {u v : V} {p : G.walk u v} (ht : p.is_trail) (x : V) :
  (u ≠ v → x ≠ u ∧ x ≠ v) ↔ even (p.edges.countp (λ e, x ∈ e)) :=
begin
  induction p with u u v w huv p ih,
  { simp, },
  { rw [cons_is_trail_iff] at ht,
    specialize ih ht.1,
    simp only [list.countp_cons, ne.def, edges_cons, sym2.mem_iff],
    split_ifs with h,
    { obtain (rfl | rfl) := h,
      { rw [nat.even_succ, ← ih],
        simp only [huv.ne, imp_false, eq_self_iff_true, not_true, false_and, not_not,
          ne.def, not_false_iff, true_and, not_forall, exists_prop, iff_and_self],
        rintro rfl rfl,
        exact G.loopless _ huv, },
      { rw [nat.even_succ, ← ih],
        simp only [huv.ne.symm, imp_false, ←imp_iff_not_or, not_false_iff, true_and,
          ne.def, eq_self_iff_true, not_true, false_and, not_not, imp_iff_right_iff],
        rintro rfl rfl,
        exact G.loopless _ huv, } },
    { rw not_or_distrib at h,
      simp only [h.1, h.2, not_false_iff, true_and, add_zero, ne.def] at ih ⊢,
      rw ← ih,
      split;
      { rintro h' h'' rfl,
        simp only [imp_false, eq_self_iff_true, not_true, not_not] at h',
        cases h',
        simpa using h } } },
end

lemma incidence_finset_eq_filter [fintype V] (x : V) [fintype (G.neighbor_set x)] [decidable_rel G.adj] :
  G.incidence_finset x = G.edge_finset.filter (has_mem.mem x) :=
begin
  ext e,
  refine sym2.ind (λ v w, _) e,
  simp [mk_mem_incidence_set_iff],
end

lemma is_eulerian.even_degree {x u v : V} {p : G.walk u v} (ht : p.is_eulerian)
  [fintype V] [decidable_rel G.adj] :
  (u ≠ v → x ≠ u ∧ x ≠ v) ↔ even (G.degree x) :=
begin
  convert ht.is_trail.even_countp_edges x,
  have := ht.is_trail.edges_nodup,
  rw ← multiset.coe_nodup at this,
  let edges : finset (sym2 V) := finset.mk ↑p.edges this,
  rw [← multiset.coe_countp, multiset.countp_eq_card_filter, ← card_incidence_finset_eq_degree],
  change multiset.card _ = _,
  congr' 1,
  convert_to _ = (edges.filter (has_mem.mem x)).val,
  congr' 1,
  rw [incidence_finset_eq_filter],
  congr,
  have h1 : edges ⊆ G.edge_finset,
  { intro e,
    simp only [finset.mem_mk, multiset.mem_coe, mem_edge_finset],
    intro he,
    exact edges_subset_edge_set p he, },
  have h2 : edges.card = G.edge_finset.card,
  { rw is_eulerian_iff at ht,
    simp [ht], },
  exact (finset.eq_of_subset_of_card_le h1 h2.ge).symm,
end

lemma is_eulerian.degrees [fintype V] [decidable_rel G.adj]
  {u v : V} {p : G.walk u v} (ht : p.is_eulerian) :
  ((finset.univ : finset V).filter (λ v, odd (G.degree v))).card ∈ ({0, 2} : set ℕ) :=
begin
  simp only [nat.odd_iff_not_even, set.mem_insert_iff, finset.card_eq_zero, set.mem_singleton_iff],
  simp only [←ht.even_degree, ne.def, not_forall, not_and, not_not, exists_prop],
  obtain (rfl | hn) := eq_or_ne u v,
  { left,
    simp, },
  { right,
    convert_to _ = ({u, v} : finset V).card,
    { simp [hn], },
    { congr',
      ext x,
      simp [hn, imp_iff_not_or], } },
end

end walk

namespace simple_example

@[derive [decidable_eq, fintype]]
inductive verts : Type
| V1 | V2 | V3

open verts

def adj (v w : verts) : bool := v ≠ w

/-- It's a complete graph on 3 vertices -/
@[simps]
def graph : simple_graph verts :=
{ adj := λ v w, adj v w,
  symm := λ v w, begin simp [adj, eq_comm] end,
  loopless := λ v, by simp [adj] }

def trail : graph.walk V1 V1 :=
begin
  refine walk.cons (_ : adj V1 V2) (walk.cons (_ : adj V2 V3) (walk.cons (_ : adj V3 V1) walk.nil));
  constructor
end

lemma trail_is_eulerian : trail.is_eulerian :=
begin
  intro e,
  refine sym2.ind (λ v w, _) e,
  simp [trail],
  cases v; cases w; dec_trivial,
end

end simple_example

namespace konigsberg

@[derive [decidable_eq, fintype]]
inductive verts : Type
| V1 | V2 | V3 | V4
| B1 | B2 | B3 | B4 | B5 | B6 | B7

open verts

def edges : list (verts × verts) :=
[ (V1, B1), (V1, B2), (V1, B3), (V1, B4), (V1, B5),
  (B1, V2), (B2, V2), (B3, V4), (B4, V3), (B5, V3),
  (V2, B6), (B6, V4),
  (V3, B7), (B7, V4)
]

def adj (v w : verts) : bool := ((v, w) ∈ edges) || ((w, v) ∈ edges)

@[simps]
def graph : simple_graph verts :=
{ adj := λ v w, adj v w,
  symm := begin
    dsimp [symmetric, adj],
    exact dec_trivial,
  end,
  loopless := begin
    dsimp [irreflexive, adj],
    exact dec_trivial
  end }
.

instance : decidable_rel graph.adj :=
λ a b,
if h : adj a b then decidable.is_true h else decidable.is_false h

/- Was trying to make a dec_trivial proof, but it didn't work.


instance : decidable (¬∃ (u v : verts) (p : graph.walk u v), p.is_eulerian) :=
infer_instance

--#eval graph.edge_finset.card
--#eval (graph.trail_of_len 14 V1 V1).card

/- don't work
theorem no_euler_trail' : ¬(graph.trail_of_len graph.edge_finset.card V1 V1).nonempty :=
begin
  dec_trivial,
end

theorem no_euler_trail : ¬∃ (u v : verts) (p : graph.walk u v), p.is_eulerian :=
begin
  haveI : decidable (¬∃ (u v : verts) (p : graph.walk u v), p.is_eulerian), apply_instance,
  dec_trivial,
end
-/
-/

def neighbor_sets : verts → finset verts
| V1 := {B1, B2, B3, B4, B5}
| V2 := {B1, B2, B6}
| V3 := {B4, B5, B7}
| V4 := {B3, B6, B7}
| B1 := {V1, V2}
| B2 := {V1, V2}
| B3 := {V1, V4}
| B4 := {V1, V3}
| B5 := {V1, V3}
| B6 := {V2, V4}
| B7 := {V3, V4}

lemma neighbor_sets_ok (v : verts) : graph.neighbor_finset v = neighbor_sets v :=
begin
  cases v; refl,
/-  apply finset.ext;
  intro w;
  simp only [neighbor_sets, adj, mem_neighbor_finset, graph_adj, bor_coe_iff, bool.of_to_bool_iff, finset.mem_insert,
    finset.mem_singleton];
  simp only [edges, list.mem_cons_iff, prod.mk.inj_iff, false_and, eq_self_iff_true, true_and, list.not_mem_nil, or_false,
    false_or, and_false, and_true];
  cases w; simp,-/
end
.

def degrees : verts → ℕ
| V1 := 5
| V2 := 3
| V3 := 3
| V4 := 3
| B1 := 2
| B2 := 2
| B3 := 2
| B4 := 2
| B5 := 2
| B6 := 2
| B7 := 2

lemma degrees_ok (v : verts) : graph.degree v = degrees v :=
begin
  cases v; refl,
end

theorem no_euler_trail {u v : verts} (p : graph.walk u v) (h : p.is_eulerian) : false :=
begin
  have : finset.filter (λ (v : verts), odd (graph.degree v)) finset.univ = {verts.V1, verts.V2, verts.V3, verts.V4},
  { ext w,
    simp,
    cases w; simp [degrees_ok, degrees], },
  have h := h.degrees,
  rw [this] at h,
  simp at h,
  norm_num at h,
end

end konigsberg


@[simp]
lemma edges_to_delete_edges {u v : V} {p : G.walk u v} (s : set (sym2 V))
  (hs : ∀ e, e ∈ p.edges → ¬ e ∈ s) :
  (p.to_delete_edges s hs).edges = p.edges :=
by induction p; simp [-quotient.eq, *]

@[simp]
lemma length_to_delete_edges {u v : V} {p : G.walk u v} (s : set (sym2 V))
  (hs : ∀ e, e ∈ p.edges → ¬ e ∈ s) :
  (p.to_delete_edges s hs).length = p.length :=
by induction p; simp [-quotient.eq, *]

lemma walk.is_trail.to_delete_edges {u v : V} {p : G.walk u v} (hp : p.is_trail) (s : set (sym2 V))
  (hs : ∀ e, e ∈ p.edges → ¬ e ∈ s) :
  (p.to_delete_edges s hs).is_trail :=
begin
  induction p,
  { simp, },
  { simp,
    simp at hp,
    split,
    apply p_ih,
    exact hp.1,
    exact hp.2, },
end

@[simp]
lemma edge_set_delete_edges (s : set (sym2 V)) : (G.delete_edges s).edge_set = G.edge_set \ s :=
begin
  ext e,
  refine sym2.ind (λ u v, _) e,
  simp,
end

@[simp]
lemma incidence_set_delete_edges (s : set (sym2 V)) (v : V) : (G.delete_edges s).incidence_set v = G.incidence_set v \ s :=
begin
  ext e,
  refine sym2.ind (λ u w, _) e,
  simp [mk_mem_incidence_set_iff],
  tauto,
end

@[simp]
lemma edge_finset_delete_edges [fintype V] [decidable_eq V] [decidable_rel G.adj] (s : finset (sym2 V))
  [decidable_rel (G.delete_edges s).adj] :
  (G.delete_edges s).edge_finset = G.edge_finset \ s :=
begin
  ext e,
  refine sym2.ind (λ u v, _) e,
  simp,
end

lemma mem_incidence_set_of_mem {v : V} {e : sym2 V} (hv : v ∈ e) (he : e ∈ G.edge_set) :
  e ∈ G.incidence_set v := ⟨he, hv⟩

@[simp]
lemma delete_edge_degree (v : V) (e : sym2 V)
  [fintype (G.neighbor_set v)] [fintype ((G.delete_edges {e}).neighbor_set v)]
  [decidable (v ∈ e)] (he : e ∈ G.edge_set) :
  (G.delete_edges {e}).degree v = if v ∈ e then G.degree v - 1 else G.degree v :=
begin
  classical,
  rw [← card_incidence_set_eq_degree],
  simp_rw [incidence_set_delete_edges],
  split_ifs with h,
  { simp,
    rw [finset.card_sdiff],
    simp,
    simp [h],
    exact mem_incidence_set_of_mem h he },
  { have : G.incidence_set v \ {e} = G.incidence_set v,
    { ext e',
      simp,
      rintro ⟨h1, h2⟩ heq,
      rw heq at h2,
      exact h h2, },
    simp_rw [this],
    simp, },
end

lemma finset.filter_sdiff {α : Type*} (s s' : finset α) (p : α → Prop) [decidable_pred p] [decidable_eq α] :
  (s \ s').filter p = s.filter (λ x, ¬ x ∈ s' ∧ p x) :=
begin
  ext x,
  simp [and_assoc],
end

section fintype
variables [fintype V] [decidable_eq V]
variables [decidable_rel G.adj]
variables (G)

/-- Gives all trails between two vertices.  (TODO: make more efficient) -/
def trail_of_len : Π (n : ℕ) (u v : V), finset (G.walk u v)
| 0 u v := if h : u = v
           then by { subst u, exact {walk.nil}, }
           else ∅
| (n+1) u v := finset.univ.bUnion (λ (w : V),
                 if h : G.adj u w
                 then (trail_of_len n w v).bUnion (λ p,
                   if ⟦(u, w)⟧ ∈ p.edges then ∅ else {walk.cons h p})
                 else ∅)

variables {G}

lemma trail_of_len_eq (n : ℕ) (u v : V) :
  ↑(G.trail_of_len n u v) = {p : G.walk u v | p.length = n ∧ p.is_trail} :=
begin
  dsimp only [walk.is_trail_def],
  induction n generalizing u v,
  { ext p,
    cases p,
    { simp! only [dite_eq_ite, set.mem_singleton, if_true, finset.coe_singleton, eq_self_iff_true,
      and_self, list.nodup_nil,
      set.mem_set_of_eq],
      simp, },
    simp! only [set.mem_set_of_eq, iff_false, finset.mem_coe, false_and],
    split_ifs,
    { subst u, simp, },
    { simp, }, },
  { ext p,
    cases p,
    { have : ∀ n, 0 = n + 1 ↔ false,
      { intro n,
        simp only [forall_const, (nat.succ_ne_zero n).symm], },
      simp! only [nat.succ_eq_add_one, this, set.mem_Union, nat.nat_zero_eq_zero, finset.coe_bUnion,
          finset.mem_univ, set.Union_true, list.nodup_nil, set.mem_set_of_eq, exists_imp_distrib,
          iff_false, finset.mem_coe, false_and],
      intro w, split_ifs,
      simp! only [and_imp, exists_prop, finset.mem_bUnion, forall_true_left, exists_imp_distrib],
      intro q, split_ifs, simp, simp, simp, },
    { simp! only [set.mem_Union, finset.coe_bUnion, finset.mem_univ, set.Union_true,
        list.nodup_cons, set.mem_set_of_eq, finset.mem_coe],
      simp only [walk.cons_is_trail_iff],
      split,
      { rintro ⟨w, hh⟩,
        split_ifs at hh,
        simp! only [exists_prop, finset.mem_bUnion] at hh,
        obtain ⟨q, hq, hh⟩ := hh,
        rw ←finset.mem_coe at hq,
        rw n_ih at hq,
        simp at hq,
        split_ifs at hh,
        exfalso, simpa using hh,
        simp at hh,
        obtain ⟨rfl, rfl⟩ := hh,
        simp [hq.1, hq.2, h_1],
        exfalso, simpa using hh, },
      { rintro ⟨rfl, h, hnd⟩,
        use p_v,
        simp [p_h],
        use p_p,
        rw ←finset.mem_coe,
        rw n_ih,
        simp [h, hnd], }, }, },
end

lemma eulerian_trails_eq (u v : V) :
  ↑(G.trail_of_len G.edge_finset.card u v) = {p : G.walk u v | p.is_eulerian} :=
begin
  rw trail_of_len_eq,
  ext p,
  simp [walk.is_eulerian_iff, and_comm],
end

/-
instance {u v : V} : decidable_pred (walk.is_eulerian : G.walk u v → Prop) :=
begin
  intro p,
  by_cases h : p ∈ G.trail_of_len G.edge_finset.card u v,
  { apply decidable.is_true,
    rw [←finset.mem_coe, eulerian_trails_eq] at h,
    exact h, },
  { apply decidable.is_false,
    rw [←finset.mem_coe, eulerian_trails_eq] at h,
    exact h, },
end-/

instance finset_nonempty_decidable {α : Type*} : Π (s : finset α), decidable (finset.nonempty s) :=
begin
  intro s,
  rw [←finset.card_pos],
  change decidable (0 < s.val.card),
  refine quotient.rec_on s.val (λ s', _) _,
  cases s',
  { apply decidable.is_false,
    simp, },
  { apply decidable.is_true,
    simp, },
  intros l₁ l₂ p,
  simp,
end

instance nonempty_trail_of_len_decidable :
  decidable_pred (λ (p : V × V), (G.trail_of_len G.edge_finset.card p.1 p.2).nonempty) :=
begin
  apply_instance,
end

instance exists_eulerian_decidable : decidable (∃ u v (p : G.walk u v), p.is_eulerian) :=
if h : ∃ (p : V × V), (G.trail_of_len G.edge_finset.card p.1 p.2).nonempty
then decidable.is_true begin
  obtain ⟨⟨u, v⟩, p, h⟩ := h,
  use [u, v, p],
  rw [←finset.mem_coe, eulerian_trails_eq] at h,
  exact h,
end else decidable.is_false begin
  contrapose! h,
  dsimp at ⊢ h,
  obtain ⟨u, v, p, h⟩ := h,
  use [u, v],
  rw ←finset.coe_nonempty,
  rw eulerian_trails_eq,
  use [p, h],
end

/-
namespace cycle3

abbreviation graph := complete_graph (fin 3)

theorem euler_cycle : ∃ u v (p : graph.walk u v), p.is_eulerian :=
begin
  dec_trivial,
end

end cycle3
-/


end fintype

end simple_graph
