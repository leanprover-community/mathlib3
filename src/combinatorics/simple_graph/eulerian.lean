/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
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

end walk

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

def adj (v w : verts) : bool := edges.mem (v, w) || edges.mem (w, v)

@[simps]
def graph : simple_graph verts :=
{ adj := λ v w, adj v w,
  sym := begin
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

instance : decidable (¬∃ (u v : verts) (p : graph.walk u v), p.is_eulerian) :=
infer_instance

--#eval graph.edge_finset.card
--#eval (graph.trail_of_len 10 V1 V1).card
-- 0

theorem no_euler_trail' : ¬(graph.trail_of_len graph.edge_finset.card V1 V1).nonempty :=
begin
  dec_trivial,
end

theorem no_euler_trail : ¬∃ (u v : verts) (p : graph.walk u v), p.is_eulerian :=
begin
  haveI : decidable (¬∃ (u v : verts) (p : graph.walk u v), p.is_eulerian), apply_instance,
  dec_trivial,
end

end konigsberg
-/
end fintype

end simple_graph
