/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.move_somewhere
/-!

# Graph connectivity

In a simple graph,

* A *walk* is a finite sequence of adjacent vertices, and can be
  thought of equally well as a sequence of edges.

* A *trail* is a walk whose edges each appear no more than once.

* A *path* is a trail whose vertices appear no more than once.

* A *cycle* is a nonempty trail whose first and last vertices are the
  same and whose vertices except for the first appear no more than once.

**Warning:** graph theorists mean something different by "path" than do
homotopy theorists.  A "walk" in graph theory is a "path" in homotopy
theory.

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `simple_graph.walk`

* `simple_graph.is_trail`, `simple_graph.is_path`, and `simple_graph.is_cycle`.

* `simple_graph.path`

* `simple_graph.reachable`, `simple_graph.connected`,
  and `simple_graph.connected_component`

* `simple_graph.is_acyclic` and `simple_graph.is_tree`

* `simple_graph.walk.is_eulerian` and `simple_graph.walk.is_hamiltonian`

* `simple_graph.edge_connected` for k-edge-connectivity of a graph

## Tags
walks

-/

universes u

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `simple_graph.walk.support`. -/
@[derive decidable_eq]
inductive walk : V → V → Type u
| nil {u : V} : walk u u
| cons {u v w: V} (h : G.adj u v) (p : walk v w) : walk u w

attribute [refl] walk.nil

instance walk.inhabited (v : V) : inhabited (G.walk v v) := ⟨by refl⟩

namespace walk
variables {G}

/-- The length of a walk is the number of edges along it. -/
def length : Π {u v : V}, G.walk u v → ℕ
| _ _ nil := 0
| _ _ (cons _ q) := q.length.succ

/-- The concatenation of two compatible walks. -/
@[trans]
def append : Π {u v w : V}, G.walk u v → G.walk v w → G.walk u w
| _ _ _ nil q := q
| _ _ _ (cons h p) q := cons h (p.append q)

/-- The concatenation of the reverse of the first walk with the second walk. -/
protected def reverse_aux : Π {u v w : V}, G.walk u v → G.walk u w → G.walk v w
| _ _ _ nil q := q
| _ _ _ (cons h p) q := reverse_aux p (cons (G.sym h) q)

/-- Reverse the orientation of a walk. -/
@[symm]
def reverse {u v : V} (w : G.walk u v) : G.walk v u := w.reverse_aux nil

/-- Get the `n`th vertex from a path, where `n` is generally expected to be
between `0` and `p.length`, inclusive.
If `n` is greater than the length of the path, the result is the path's endpoint. -/
def get_vert : Π {u v : V} (p : G.walk u v) (n : ℕ), V
| u v nil _ := u
| u v (cons _ _) 0 := u
| u v (cons _ q) (n+1) := q.get_vert n

@[simp] lemma cons_append {u v w x : V} (h : G.adj u v) (p : G.walk v w) (q : G.walk w x) :
  (cons h p).append q = cons h (p.append q) := rfl

@[simp] lemma cons_nil_append {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h nil).append p = cons h p := rfl

@[simp] lemma append_nil : Π {u v : V} (p : G.walk u v), p.append nil = p
| _ _ nil := rfl
| _ _ (cons h p) := by rw [cons_append, append_nil]

@[simp] lemma nil_append {u v : V} (p : G.walk u v) : nil.append p = p := rfl

lemma append_assoc : Π {u v w x : V} (p : G.walk u v) (q : G.walk v w) (r : G.walk w x),
  p.append (q.append r) = (p.append q).append r
| _ _ _ _ nil _ _ := rfl
| _ _ _ _ (cons h p') q r := by { dsimp only [append], rw append_assoc, }

@[simp] lemma nil_reverse {u : V} : (nil : G.walk u u).reverse = nil := rfl

lemma singleton_reverse {u v : V} (h : G.adj u v) :
  (cons h nil).reverse = cons (G.sym h) nil := rfl

@[simp]
protected lemma reverse_aux_eq_reverse_append {u v w : V} (p : G.walk u v) (q : G.walk u w) :
  p.reverse_aux q = p.reverse.append q :=
begin
  induction p generalizing q w,
  { refl },
  { dsimp [walk.reverse_aux, walk.reverse],
    rw [p_ih, p_ih, ←append_assoc],
    refl, }
end

@[simp] lemma append_reverse {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.append q).reverse = q.reverse.append p.reverse :=
begin
  induction p generalizing q w,
  { simp },
  { dsimp only [cons_append, reverse, walk.reverse_aux],
    simp only [p_ih, walk.reverse_aux_eq_reverse_append, append_nil],
    rw append_assoc, }
end

@[simp] lemma cons_reverse {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).reverse = p.reverse.append (cons (G.sym h) nil) :=
begin
  dsimp [reverse, walk.reverse_aux],
  simp only [walk.reverse_aux_eq_reverse_append, append_nil],
end

@[simp] lemma reverse_reverse : Π {u v : V} (p : G.walk u v), p.reverse.reverse = p
| _ _ nil := rfl
| _ _ (cons h p) := by simp [reverse_reverse]

@[simp] lemma nil_length {u : V} : (nil : G.walk u u).length = 0 := rfl

@[simp] lemma cons_length {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).length = p.length + 1 := rfl

@[simp] lemma append_length : Π {u v w : V} (p : G.walk u v) (q : G.walk v w),
  (p.append q).length = p.length + q.length
| _ _ _ nil _ := by simp
| _ _ _ (cons _ p') _ := by simp [append_length, add_left_comm, add_comm]

protected lemma reverse_aux_length {u v w : V} (p : G.walk u v) (q : G.walk u w) :
  (p.reverse_aux q).length = p.length + q.length :=
begin
  induction p,
  { simp [walk.reverse_aux], },
  { simp only [walk.reverse_aux, p_ih, cons_length],
    ring, },
end

@[simp] lemma reverse_length {u v : V} (p : G.walk u v) : p.reverse.length = p.length :=
by convert walk.reverse_aux_length p nil

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support : Π {u v : V}, G.walk u v → list V
| u v nil := [u]
| u v (cons h p) := u :: p.support

/-- The `edges` of a walk is the list of edges it visits in order. -/
def edges : Π {u v : V}, G.walk u v → list (sym2 V)
| u v nil := []
| u v (@cons _ _ _ x _ h p) := ⟦(u, x)⟧ :: p.edges

@[simp] lemma nil_support {u : V} : (nil : G.walk u u).support = [u] := rfl

@[simp] lemma cons_support {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).support = u :: p.support := rfl

lemma support_ne_nil {u v : V} (p : G.walk u v) : p.support ≠ [] :=
by cases p; simp

@[simp] lemma start_mem_support {u v : V} (p : G.walk u v) : u ∈ p.support :=
by cases p; simp

@[simp] lemma end_mem_support {u v : V} (p : G.walk u v) : v ∈ p.support :=
by induction p; simp *

lemma edges_mem_edge_set {u v : V} {p : G.walk u v} {e : sym2 V}
  (h : e ∈ p.edges) : e ∈ G.edge_set :=
begin
  induction p generalizing e,
  { exact false.elim h, },
  { rw [edges, list.mem_cons_iff] at h,
    rcases h with ⟨rfl, h⟩,
    { exact p_h },
    { exact p_ih h }, },
end

@[simp] lemma nil_edges {u : V} : (nil : G.walk u u).edges = [] := rfl

@[simp] lemma cons_edges {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).edges = ⟦(u, v)⟧ :: p.edges := rfl

@[simp] lemma support_length {u v : V} (p : G.walk u v) : p.support.length = p.length + 1 :=
by induction p; simp *

@[simp] lemma edges_length {u v : V} (p : G.walk u v) : p.edges.length = p.length :=
by induction p; simp *

lemma edge_vert_mem_support {t u v w : V} (p : G.walk v w)
  (he : ⟦(t, u)⟧ ∈ p.edges) :
  t ∈ p.support :=
begin
  induction p,
  { exact false.elim he, },
  { simp only [cons_support, list.mem_cons_iff],
    simp only [cons_edges, list.mem_cons_iff, quotient.eq] at he,
    cases he,
    { cases he,
      { exact or.inl rfl, },
      { cases p_p; simp, }, },
    { exact or.inr (p_ih he), } },
end

/-- A *trail* is a walk with no repeating edges. -/
def is_trail {u v : V} (p : G.walk u v) : Prop := p.edges.nodup

/-- A *path* is a trail with no repeating vertices. -/
structure is_path {u v : V} (p : G.walk u v) : Prop :=
(to_trail : is_trail p)
(support_nodup : p.support.nodup)

/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
structure is_circuit {u : V} (p : G.walk u u) : Prop :=
(to_trail : is_trail p)
(ne_nil : p ≠ nil)

/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure is_cycle [decidable_eq V] {u : V} (p : G.walk u u) extends to_circuit :
  is_circuit p : Prop :=
(support_nodup : p.support.tail.nodup)

/-- A walk `p` is *Eulerian* if it visits every edge exactly once.

Combine with `p.is_trail` to get an Eulerian trail (also known as an "Eulerian path"),
or combine with `p.is_circuit` to get an Eulerian circuit (also known as an "Eulerian cycle"). -/
def is_eulerian [decidable_eq V] {u v : V} (p : G.walk u v) : Prop :=
∀ e, e ∈ G.edge_set → p.edges.count e = 1

/-- A walk `p` is *Hamiltonian* if it visits every vertex exactly once.
Hamiltonian walks are automatically paths. (TODO: make the path version, too.) -/
def is_hamiltonian [decidable_eq V] {u v : V} (p : G.walk u v) : Prop :=
∀ v, p.support.count v = 1

lemma is_path_def {u v : V} (p : G.walk u v) :
  p.is_path ↔ is_trail p ∧ p.support.nodup :=
by split; { rintro ⟨h1, h2⟩, exact ⟨h1, h2⟩ }

lemma is_cycle_def [decidable_eq V] {u : V} (p : G.walk u u) :
  p.is_cycle ↔ is_trail p ∧ p ≠ nil ∧ p.support.tail.nodup :=
iff.intro (λ h, ⟨h.1.1, h.1.2, h.2⟩) (λ h, ⟨⟨h.1, h.2.1⟩, h.2.2⟩)

lemma trail_count_le_one [decidable_eq V] {u v : V}
  (p : G.walk u v) (h : p.is_trail) (e : sym2 V) : p.edges.count e ≤ 1 :=
list.nodup_iff_count_le_one.mp h e

lemma trail_count_eq_one [decidable_eq V] {u v : V}
  (p : G.walk u v) (h : p.is_trail) {e : sym2 V}
  (he : e ∈ p.edges) : p.edges.count e = 1 :=
list.count_eq_one_of_mem h he

@[simp] lemma nil_is_trail {u : V} : (nil : G.walk u u).is_trail :=
by simp [is_trail, edges]

@[simp] lemma nil_is_path {u : V} : (nil : G.walk u u).is_path :=
by { fsplit; simp }

lemma is_trail_of_cons_is_trail {u v w : V} {h : G.adj u v} {p : G.walk v w}
  (h : (cons h p).is_trail) : p.is_trail :=
by { rw [is_trail, edges, list.nodup_cons] at h, exact h.2, }

lemma is_path_of_cons_is_path {u v w : V} {h : G.adj u v} {p : G.walk v w}
  (h : (cons h p).is_path) : p.is_path :=
begin
  cases h with ht hd,
  split,
  { exact is_trail_of_cons_is_trail ht, },
  { rw [cons_support, list.nodup_cons] at hd,
    exact hd.2, },
end

@[simp] lemma cons_is_trail_iff {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).is_trail ↔ p.is_trail ∧ ⟦(u, v)⟧ ∉ p.edges :=
by simp [is_trail, and_comm]

@[simp] lemma cons_is_path_iff {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).is_path ↔ p.is_path ∧ u ∉ p.support :=
begin
  simp only [is_path_def, cons_is_trail_iff, cons_support, list.nodup_cons],
  split,
  { rintro ⟨⟨ht, hne⟩, hns, hsn⟩,
    exact ⟨⟨ht, hsn⟩, hns⟩, },
  { rintro ⟨⟨ht, hsn⟩, hns⟩,
    simp only [ht, hsn, hns, and_true, not_false_iff, true_and],
    intro he,
    exact hns (edge_vert_mem_support p he), },
end

end walk

/-- Two vertices are *reachable* if there is a walk between them.

This is equivalent to `relation.refl_trans_gen` of `G.adj`.
See `simple_graph.reachable_iff_refl_trans_gen`. -/
def reachable (u v : V) : Prop := nonempty (G.walk u v)

variables {G}

protected lemma reachable.elim {p : Prop} {u v : V}
  (h : G.reachable u v) (hp : G.walk u v → p) : p :=
nonempty.elim h hp

@[refl] lemma reachable.refl {u : V} : G.reachable u u := by { fsplit, refl }

@[symm] lemma reachable.symm {u v : V} (huv : G.reachable u v) : G.reachable v u :=
huv.elim (λ p, ⟨p.reverse⟩)

@[trans] lemma reachable.trans {u v w : V} (huv : G.reachable u v) (hvw : G.reachable v w) :
  G.reachable u w :=
huv.elim (λ puv, hvw.elim (λ pvw, ⟨puv.append pvw⟩))

lemma reachable_iff_refl_trans_gen (u v : V) :
  G.reachable u v ↔ relation.refl_trans_gen G.adj u v :=
begin
  split,
  { rintro ⟨h⟩,
    induction h,
    { refl, },
    { exact (relation.refl_trans_gen.single h_h).trans h_ih, }, },
  { intro h,
    induction h with _ _ _ ha hr,
    { refl, },
    { exact reachable.trans hr ⟨walk.cons ha walk.nil⟩, }, },
end

variables (G)

lemma reachable_is_equivalence : equivalence G.reachable :=
mk_equivalence _ (@reachable.refl _ G) (@reachable.symm _ G) (@reachable.trans _ G)

/-- The equivalence relation on vertices given by `simple_graph.reachable`. -/
def reachable_setoid : setoid V := setoid.mk _ G.reachable_is_equivalence

/-- The connected components of a graph are elements of the quotient of vertices by
the `simple_graph.reachable` relation. -/
def connected_component := quot G.reachable

/-- A graph is connected is every pair of vertices is reachable from one another. -/
def connected : Prop := ∀ (u v : V), G.reachable u v

/-- Gives the connected component containing a particular vertex. -/
def connected_component_of (v : V) : G.connected_component := quot.mk G.reachable v

instance connected_components.inhabited [inhabited V] : inhabited G.connected_component :=
⟨G.connected_component_of (default _)⟩

lemma connected_component.subsingleton_of_connected (h : G.connected) :
  subsingleton G.connected_component :=
⟨λ c d, quot.ind (λ v d, quot.ind (λ w, quot.sound (h v w)) d) c d⟩

/-- A subgraph is connected if it is connected as a simple graph. -/
abbreviation subgraph.connected {G : simple_graph V} (H : G.subgraph) : Prop := H.coe.connected

/-- A graph is *k-edge-connected* if it remains connected whenever
fewer than k edges are removed. -/
def edge_connected (k : ℕ) : Prop :=
∀ (s : finset (sym2 V)), ↑s ⊆ G.edge_set → s.card < k →
  ((⊤ : G.subgraph).delete_edges ↑s).spanning_coe.connected

section walk_to_path

/-- The type of paths between two vertices. -/
abbreviation path (u v : V) := {p : G.walk u v // p.is_path}

namespace walk
variables {G}

lemma append_support {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  (p.append p').support = p.support ++ p'.support.tail :=
begin
  cases p',
  { simp, },
  { induction p,
    { simp, },
    { simp [p_ih], },
  },
end

@[simp]
lemma mem_append_support_iff {t u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  t ∈ (p.append p').support ↔ t ∈ p.support ∨ t ∈ p'.support :=
begin
  rw [append_support, list.mem_append],
  split,
  { rintro (h|h),
    { exact or.inl h, },
    { cases p',
      { exact false.elim h, },
      { simp only [cons_support, list.tail_cons] at h,
        right,
        simp only [list.mem_cons_iff, cons_support],
        exact or.inr h, }, } },
  { rintro (h|h),
    { exact or.inl h },
    { cases p',
      { simp only [nil_support, list.mem_singleton] at h,
        subst t,
        simp, },
      { simp only [list.mem_cons_iff, cons_support] at h,
        rcases h with (rfl|h),
        { simp, },
        { simp [h], }, }, }, },
end

lemma append_support' [decidable_eq V] {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  ((p.append p').support : multiset V) = p.support + p'.support - {v} :=
begin
  rw append_support,
  cases p',
  { simp only [nil_support, list.tail_cons, list.append_nil],
    convert_to _ = (p.support + ([v] - {v}) : multiset V),
    { erw multiset.add_sub_cancel,
      simp, },
    { nth_rewrite 0 ←add_zero (p.support : multiset V),
      rw add_left_cancel_iff,
      simp, }, },
  { simp_rw [cons_support, list.tail_cons, ←multiset.cons_coe, ←multiset.singleton_add],
    rw [add_comm, add_assoc, add_comm],
    erw multiset.add_sub_cancel,
    rw [←multiset.coe_add, add_comm], },
end

lemma mem_append_support {u v w : V} (p : G.walk u v) (p' : G.walk v u) (h : w ∈ p.support) :
  w ∈ (p.append p').support :=
by simp [h]

@[simp]
lemma reverse_support {u v : V} (p : G.walk u v) : p.reverse.support = p.support.reverse :=
begin
  induction p,
  { trivial, },
  { simp only [list.reverse_cons, cons_reverse, cons_support, append_support, p_ih],
    refl, },
end

@[simp]
lemma append_edges {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  (p.append p').edges = p.edges ++ p'.edges :=
begin
  induction p,
  { simp, },
  { simp [p_ih], },
end

@[simp]
lemma reverse_edges {u v : V} (p : G.walk u v) : p.reverse.edges = p.edges.reverse :=
begin
  induction p,
  { trivial },
  { simp [p_ih, -quotient.eq, sym2.eq_swap], },
end

lemma reverse_trail {u v : V} (p : G.walk u v) (h : p.is_trail) : p.reverse.is_trail :=
by simpa [is_trail] using h

@[simp] lemma reverse_trail_iff {u v : V} (p : G.walk u v) : p.reverse.is_trail ↔ p.is_trail :=
by split; { intro h, convert reverse_trail _ h, try { rw reverse_reverse } }

lemma is_trail_of_append_left {u v w : V} (p : G.walk u v) (q : G.walk v w)
  (h : (p.append q).is_trail) : p.is_trail :=
begin
  rw [is_trail, append_edges, list.nodup_append] at h,
  exact h.1,
end

lemma is_trail_of_append_right {u v w : V} (p : G.walk u v) (q : G.walk v w)
  (h : (p.append q).is_trail) : q.is_trail :=
begin
  rw [is_trail, append_edges, list.nodup_append] at h,
  exact h.2.1,
end

lemma reverse_path {u v : V} (p : G.walk u v) (h : p.is_path) : p.reverse.is_path :=
by simpa [is_path_def] using h

@[simp] lemma reverse_path_iff {u v : V} (p : G.walk u v) : p.reverse.is_path ↔ p.is_path :=
by split; intro h; convert reverse_path _ h; simp

lemma is_path_of_append_left {u v w : V} (p : G.walk u v) (q : G.walk v w)
  (h : (p.append q).is_path) : p.is_path :=
begin
  fsplit,
  { apply is_trail_of_append_left _ _ h.to_trail, },
  { have h' := h.support_nodup,
    rw append_support at h',
    exact list.nodup_of_nodup_append_left h', },
end

lemma is_path_of_append_right {u v w : V} (p : G.walk u v) (q : G.walk v w)
  (h : (p.append q).is_path) : q.is_path :=
begin
  rw ←reverse_path_iff at h ⊢,
  rw append_reverse at h,
  exact is_path_of_append_left _ _ h,
end

variables [decidable_eq V]

/-- Given a vertex in the support of a path, give the path up until that vertex. -/
def split_at_vertex_fst : Π {v w : V} (p : G.walk v w) (u : V) (h : u ∈ p.support), G.walk v u
| v w nil u h := begin
  simp only [nil_support, list.mem_singleton] at h,
  subst h,
end
| v w (cons r p) u h :=
  if hx : v = u then
    by subst u
  else
  begin
    simp only [list.mem_cons_iff, cons_support] at h,
    have : u ∈ p.support := h.cases_on (λ h', (hx h'.symm).elim) id,
    exact cons r (split_at_vertex_fst p _ this),
  end

/-- Given a vertex in the support of a path, give the path from that vertex to the end. -/
def split_at_vertex_snd : Π {v w : V} (p : G.walk v w) (u : V) (h : u ∈ p.support), G.walk u w
| v w nil u h := begin
  simp only [nil_support, list.mem_singleton] at h,
  subst h,
end
| v w (cons r p) u h :=
  if hx : v = u then
    by { subst u, exact cons r p }
  else
  begin
    simp only [list.mem_cons_iff, cons_support] at h,
    have : u ∈ p.support := h.cases_on (λ h', (hx h'.symm).elim) id,
    exact split_at_vertex_snd p _ this,
  end

/-- This and `split_at_vertex_fst_support_count` give a specification for
the way these functions split a walk. -/
@[simp]
lemma split_at_vertex_spec {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.split_at_vertex_fst u h).append (p.split_at_vertex_snd u h) = p :=
begin
  induction p,
  { simp only [split_at_vertex_fst, split_at_vertex_snd],
    generalize_proofs,
    subst u,
    refl, },
  { simp at h,
    cases h,
    { subst u,
      simp [split_at_vertex_fst, split_at_vertex_snd], },
    { by_cases hvu : p_u = u,
      subst p_u,
      simp [split_at_vertex_fst, split_at_vertex_snd],
      simp [split_at_vertex_fst, split_at_vertex_snd, hvu, p_ih], }, },
end

@[simp]
lemma split_at_vertex_fst_support_count {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.split_at_vertex_fst u h).support.count u = 1 :=
begin
  induction p,
  { simp at h,
    subst u,
    simp [split_at_vertex_fst], },
  { simp [split_at_vertex_fst],
    split_ifs,
    { subst u,
      simp, },
    { simp at h,
      cases h,
      { exact (h_1 h_2.symm).elim, },
      { rw [cons_support, list.count_cons, p_ih h_2],
        simp,
        intro h,
        exact h_1 h.symm, }, }, },
end

lemma split_at_vertex_fst_support_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.split_at_vertex_fst u h).support ⊆ p.support :=
begin
  conv_rhs { rw [←split_at_vertex_spec p h] },
  intros x hx,
  rw mem_append_support_iff,
  exact or.inl hx,
end

lemma split_at_vertex_snd_support_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.split_at_vertex_snd u h).support ⊆ p.support :=
begin
  conv_rhs { rw [←split_at_vertex_spec p h] },
  intros x hx,
  rw mem_append_support_iff,
  exact or.inr hx,
end

lemma split_at_vertex_fst_edges_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.split_at_vertex_fst u h).edges ⊆ p.edges :=
begin
  conv_rhs { rw [←split_at_vertex_spec p h] },
  intros x hx,
  rw [append_edges, list.mem_append],
  exact or.inl hx,
end

lemma split_at_vertex_snd_edges_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.split_at_vertex_snd u h).edges ⊆ p.edges :=
begin
  conv_rhs { rw [←split_at_vertex_spec p h] },
  intros x hx,
  rw [append_edges, list.mem_append],
  exact or.inr hx,
end

lemma split_at_vertex_fst_is_trail {u v w : V} (p : G.walk v w)
  (hc : p.is_trail) (h : u ∈ p.support) : (p.split_at_vertex_fst u h).is_trail :=
begin
  rw ← split_at_vertex_spec _ h at hc,
  apply is_trail_of_append_left _ _ hc,
end

lemma split_at_vertex_snd_is_trail {u v w : V} (p : G.walk v w)
  (hc : p.is_trail) (h : u ∈ p.support) : (p.split_at_vertex_snd u h).is_trail :=
begin
  rw ← split_at_vertex_spec _ h at hc,
  apply is_trail_of_append_right _ _ hc,
end

lemma split_at_vertex_fst_is_path {u v w : V} (p : G.walk v w)
  (hc : p.is_path) (h : u ∈ p.support) : (p.split_at_vertex_fst u h).is_path :=
begin
  rw ← split_at_vertex_spec _ h at hc,
  apply is_path_of_append_left _ _ hc,
end

lemma split_at_vertex_snd_is_path {u v w : V} (p : G.walk v w)
  (hc : p.is_path) (h : u ∈ p.support) : (p.split_at_vertex_snd u h).is_path :=
begin
  rw ← split_at_vertex_spec _ h at hc,
  apply is_path_of_append_right _ _ hc,
end

/-- Rotate a loop walk such that it is centered at the given vertex. -/
def rotate {u v : V} (c : G.walk v v) (h : u ∈ c.support) : G.walk u u :=
(c.split_at_vertex_snd u h).append (c.split_at_vertex_fst u h)

/-
@[simp]
lemma rotate_support {u v : V} (c : G.walk v v) (h : u ∈ c.support) :
  (c.rotate h).support = c.support + {u} - {v} :=
begin
  simp only [rotate, multiset.singleton_eq_singleton, add_zero, multiset.sub_zero,
    append_support, multiset.sub_cons, multiset.add_cons],
  rw [add_comm, split_at_vertex_support, add_comm],
  refl,
end
-/

lemma rotate_edges {u v : V} (c : G.walk v v) (h : u ∈ c.support) :
  (c.rotate h).edges ~r c.edges :=
begin
  simp [rotate, append_edges],
  apply list.is_rotated.trans list.is_rotated_append,
  rw [←append_edges, split_at_vertex_spec],
end

lemma rotate_trail {u v : V} (c : G.walk v v) (hc : c.is_trail) (h : u ∈ c.support) :
  (c.rotate h).is_trail :=
begin
  rw [is_trail, (c.rotate_edges h).perm.nodup_iff],
  exact hc,
end

lemma rotate_circuit {u v : V} (c : G.walk v v) (hc : c.is_circuit) (h : u ∈ c.support) :
  (c.rotate h).is_circuit :=
begin
  fsplit,
  { exact rotate_trail _ hc.to_trail _, },
  { cases c,
    { exact (hc.ne_nil rfl).elim, },
    { intro hn,
      have hn' := congr_arg length hn,
      rw [rotate, append_length, add_comm, ←append_length, split_at_vertex_spec] at hn',
      simpa using hn', } },
end

lemma rotate_cycle {u v : V} (c : G.walk v v) (hc : c.is_cycle) (h : u ∈ c.support) :
  (c.rotate h).is_cycle :=
begin
  split,
  { exact rotate_circuit _ hc.to_circuit _, },
  { rw rotate,
    rw [append_support, list.append_tail (support_ne_nil _), list.nodup_append_comm],
    rw [←list.append_tail (support_ne_nil _), ←append_support, split_at_vertex_spec],
    exact hc.support_nodup, },
end

/-- Given a walk, produces a walk with the same endpoints and no repeated vertices or edges. -/
def to_path_aux : Π {u v : V}, G.walk u v → G.walk u v
| u v nil := nil
| u v (@cons _ _ _ x _ ha p) :=
  let p' := p.to_path_aux
  in if hs : u ∈ p'.support
     then p'.split_at_vertex_snd u hs
     else cons ha p'

lemma to_path_aux_is_path {u v : V} (p : G.walk u v) : p.to_path_aux.is_path :=
begin
  induction p,
  { simp [to_path_aux], },
  { simp [to_path_aux],
    split_ifs,
    { exact split_at_vertex_snd_is_path _ p_ih _, },
    { rw cons_is_path_iff,
      exact ⟨p_ih, h⟩, }, },
end

/-- Given a walk, produces a path with the same endpoints using `simple_graph.walk.to_path_aux`. -/
def to_path {u v : V} (p : G.walk u v) : G.path u v := ⟨p.to_path_aux, to_path_aux_is_path p⟩

lemma to_path_aux_support_subset {u v : V} (p : G.walk u v) : p.to_path_aux.support ⊆ p.support :=
begin
  induction p,
  { simp [to_path_aux], },
  { simp [to_path_aux],
    split_ifs,
    { apply list.subset.trans (split_at_vertex_snd_support_subset _ _),
      apply list.subset_cons_of_subset _ p_ih, },
    { rw cons_support,
      exact list.cons_subset_cons _ p_ih, }, },
end

lemma to_path_support_subset {u v : V} (p : G.walk u v) :
  walk.support (p.to_path : G.walk u v) ⊆ p.support :=
by simp [to_path, to_path_aux_support_subset]

lemma to_path_aux_edges_subset {u v : V} (p : G.walk u v) : p.to_path_aux.edges ⊆ p.edges :=
begin
  induction p,
  { simp [to_path_aux], },
  { simp [to_path_aux],
    split_ifs,
    { apply list.subset.trans (split_at_vertex_snd_edges_subset _ _),
      apply list.subset_cons_of_subset _ p_ih, },
    { rw cons_edges,
      exact list.cons_subset_cons _ p_ih, }, },
end

lemma to_path_edges_subset {u v : V} (p : G.walk u v) :
  walk.edges (p.to_path : G.walk u v) ⊆ p.edges :=
by simp [to_path, to_path_aux_edges_subset]

end walk

namespace walk
variables {G}

/-- Given a walk that avoids an edge, create a walk in the subgraph with that deleted. -/
def walk_of_avoiding_walk {v w : V} (e : sym2 V)
  (p : G.walk v w) (hp : e ∉ p.edges) :
  ((⊤ : G.subgraph).delete_edges {e}).spanning_coe.walk v w :=
begin
  induction p,
  { refl, },
  { simp only [edges, list.mem_cons_iff] at hp,
    push_neg at hp,
    apply walk.cons _ (p_ih _),
    use p_h,
    simp only [set.mem_singleton_iff, subtype.coe_mk],
    exact hp.1.symm,
    exact hp.2, },
end

/-- Helpful for replacing walks in an expression with paths. -/
lemma coe_path {u v : V} (p : G.walk u v) (h : p.is_path) : p = (⟨p, h⟩ : G.path u v) := rfl

end walk

namespace path
variables {G}

@[simp] lemma path_is_path {u v : V} (p : G.path u v) : walk.is_path (p : G.walk u v) := p.property

@[simp] lemma to_trail {u v : V} (p : G.path u v) : walk.is_trail (p : G.walk u v) :=
p.property.to_trail

/-- The empty path at a vertex. -/
@[refl] def nil {u : V} : G.path u u := ⟨walk.nil, by simp⟩

/-- The length-1 path given by a pair of adjacent vertices. -/
def singleton {u v : V} (h : G.adj u v) : G.path u v :=
⟨walk.cons h walk.nil, by simp [walk.is_path_def, walk.is_trail, walk.edges, G.ne_of_adj h]⟩

lemma singleton_edge_mem {u v : V} (h : G.adj u v) : ⟦(u, v)⟧ ∈ (singleton h : G.walk u v).edges :=
by simp [singleton]

/-- The reverse of a path is another path.  See `simple_graph.walk.reverse`. -/
@[symm] def reverse {u v : V} (p : G.path u v) : G.path v u :=
by { classical,
     exact ⟨walk.reverse p, walk.reverse_path p p.property⟩ }

lemma support_count_eq_one [decidable_eq V] {u v w : V} {p : G.path u v}
  (hw : w ∈ (p : G.walk u v).support) : (p : G.walk u v).support.count w = 1 :=
list.count_eq_one_of_mem p.property.support_nodup hw

lemma edges_count_eq_one [decidable_eq V] {u v : V} {p : G.path u v} (e : sym2 V)
  (hw : e ∈ (p : G.walk u v).edges) : (p : G.walk u v).edges.count e = 1 :=
list.count_eq_one_of_mem p.property.to_trail hw

end path

section map
variables {G} {V' : Type*} {G' : simple_graph V'}

/-- Given a graph homomorphism, map walks to walks. -/
def walk.map (f : G →g G') : Π {u v : V}, G.walk u v → G'.walk (f u) (f v)
| _ _ walk.nil := walk.nil
| _ _ (walk.cons h p) := walk.cons (f.map_adj h) (walk.map p)

lemma walk.map_append (f : G →g G') {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.append q).map f = (p.map f).append (q.map f) :=
begin
  induction p,
  { refl, },
  { simp [walk.map, p_ih], },
end

@[simp]
lemma walk.map_support_eq (f : G →g G') {u v : V} (p : G.walk u v) :
  (p.map f).support = p.support.map f :=
begin
  induction p,
  { refl, },
  { simp [walk.map, p_ih], },
end

/-- Note: this is using the underlying map for `simple_graph.map_edge_set`. -/
@[simp]
lemma walk.map_edges_eq (f : G →g G') {u v : V} (p : G.walk u v) :
  (p.map f).edges = p.edges.map (λ e, sym2.map f e) :=
begin
  induction p,
  { refl, },
  { simp only [walk.map, walk.edges, p_ih],
    refl, },
end

/-- Given an injective graph homomorphism, map paths to paths. -/
def path.map (f : G →g G') (hinj : function.injective f) {u v : V} (p : G.path u v) :
  G'.path (f u) (f v) :=
⟨walk.map f p, begin
  cases p with p hp,
  induction p,
  { simp [walk.map], },
  { rw walk.cons_is_path_iff at hp,
    specialize p_ih hp.1,
    rw subtype.coe_mk at p_ih,
    simp only [walk.map, walk.cons_is_path_iff, p_ih, not_exists, true_and,
      walk.map_support_eq, not_and, list.mem_map, subtype.coe_mk],
    intros x hx hf,
    have := hinj hf,
    subst x,
    exact hp.2 hx, },
end⟩

lemma connected_of_edge_connected {k : ℕ} (hk : 0 < k) (h : G.edge_connected k) :
  G.connected :=
begin
  intros v w,
  specialize h ∅ (by simp) (by simp [hk]) v w,
  simp only [finset.coe_empty, subgraph.delete_edges_of_empty] at h,
  cases h,
  exact ⟨h.map (subgraph.map_spanning_top _)⟩,
end

end map

end walk_to_path

namespace walk
variables {G}

/-- Whether or not the path `p` is a prefix of the path `q`. -/
def prefix_of [decidable_eq V] : Π {u v w : V} (p : G.walk u v) (q : G.walk u w), Prop
| u v w nil _ := true
| u v w (cons _ _) nil := false
| u v w (@cons _ _ _ x _ r p) (@cons _ _ _ y _ s q) :=
  if h : x = y
  then by { subst y, exact prefix_of p q }
  else false

end walk

section
variables [decidable_eq V]

/-- A graph is *acyclic* (or a *forest*) if it has no cycles.

A characterization: `simple_graph.is_acyclic_iff`.-/
def is_acyclic : Prop := ∀ (v : V) (c : G.walk v v), ¬c.is_cycle

/-- A *tree* is a connected acyclic graph. -/
def is_tree : Prop := G.connected ∧ G.is_acyclic

end

namespace subgraph
variables {G} (H : subgraph G)

/-- An edge of a subgraph is a bridge edge if, after removing it, its incident vertices
are no longer reachable.  The vertices are meant to be adjacent.

Implementation note: this uses `simple_graph.subgraph.spanning_coe` since adding
vertices to a subgraph does not change reachability, and it is simpler than
dealing with the dependent types from `simple_graph.subgraph.coe`. -/
def is_bridge (v w : V) : Prop :=
¬(H.delete_edges {⟦(v, w)⟧}).spanning_coe.reachable v w

end subgraph

/-- An edge of a graph is a bridge if, after removing it, its incident vertices
are no longer reachable.

Characterizations of bridges:
`simple_graph.is_bridge_iff_walks_contain`
`is_bridge_iff_no_cycle_contains` -/
def is_bridge (v w : V) : Prop := (⊤ : G.subgraph).is_bridge v w

lemma is_bridge_iff_walks_contain {v w : V} :
  G.is_bridge v w ↔ ∀ (p : G.walk v w), ⟦(v, w)⟧ ∈ p.edges :=
begin
  split,
  { intros hb p,
    by_contra he,
    apply hb,
    exact ⟨p.walk_of_avoiding_walk _ he⟩, },
  { intro hpe,
    rintro ⟨p'⟩,
    specialize hpe (p'.map (subgraph.map_spanning_top _)),
    simp only [set_coe.exists, walk.map_edges_eq, list.mem_map] at hpe,
    obtain ⟨z, he, hd⟩ := hpe,
    simp only [subgraph.map_spanning_top, hom.map_edge_set, rel_hom.coe_fn_mk,
      id.def, subtype.coe_mk, sym2.map_id] at hd,
    subst z,
    have := walk.edges_mem_edge_set he,
    simpa [subgraph.spanning_coe] using this, },
end

variables [decidable_eq V]

lemma is_bridge_iff_no_cycle_contains.aux1
  {u v w : V}
  (c : G.walk u u)
  (he : ⟦(v, w)⟧ ∈ c.edges)
  (hb : ∀ (p : G.walk v w), ⟦(v, w)⟧ ∈ p.edges)
  (hc : c.is_trail)
  (hv : v ∈ c.support)
  (hw : w ∈ (c.split_at_vertex_fst v hv).support) :
  false :=
begin
  let p1 := c.split_at_vertex_fst v hv,
  let p2 := c.split_at_vertex_snd v hv,
  let p11 := p1.split_at_vertex_fst w hw,
  let p12 := p1.split_at_vertex_snd w hw,
  have : (p11.append p12).append p2 = c := by simp,
  let q := p2.append p11,
  have hbq := hb (p2.append p11),
  have hpq' := hb p12.reverse,
  have this' : multiset.count ⟦(v, w)⟧ (p2.edges + p11.edges + p12.edges) = 1,
  { convert_to multiset.count ⟦(v, w)⟧ c.edges = _,
    congr,
    rw ←this,
    simp_rw [walk.append_edges, ←multiset.coe_add],
    rw [add_assoc ↑p11.edges, add_comm ↑p12.edges, ←add_assoc],
    congr' 1,
    rw add_comm,
    apply c.trail_count_eq_one hc he, },
  have this'' : multiset.count ⟦(v, w)⟧ (p2.append p11).edges
                  + multiset.count ⟦(v, w)⟧ p12.edges = 1,
  { convert this',
    rw walk.append_edges,
    symmetry,
    apply multiset.count_add, },
  have hA : multiset.count ⟦(v, w)⟧ (p2.append p11).edges = 1,
  { apply walk.trail_count_eq_one,
    have hr := c.rotate_trail hc hv,
    have : c.rotate hv = (p2.append p11).append p12,
    { simp [walk.rotate],
      rw ←walk.append_assoc,
      congr' 1,
      simp, },
    rw this at hr,
    apply walk.is_trail_of_append_left _ _ hr,
    assumption, },
  have hB : multiset.count ⟦(v, w)⟧ p12.edges = 1,
  { apply walk.trail_count_eq_one,
    apply walk.is_trail_of_append_right,
    apply walk.is_trail_of_append_left,
    rw this,
    exact hc,
    simpa using hpq', },
  rw [hA, hB] at this'',
  simpa using this'',
end

lemma is_bridge_iff_no_cycle_contains {v w : V} (h : G.adj v w) :
  G.is_bridge v w ↔ ∀ {u : V} (p : G.walk u u), p.is_cycle → ⟦(v, w)⟧ ∉ p.edges :=
begin
  split,
  { intros hb u c hc he,
    rw is_bridge_iff_walks_contain at hb,
    have hv : v ∈ c.support := walk.edge_vert_mem_support c he,
    have hwc : w ∈ c.support := walk.edge_vert_mem_support c
                                (by { rw sym2.eq_swap, exact he, }),
    let p1 := c.split_at_vertex_fst v hv,
    let p2 := c.split_at_vertex_snd v hv,
    by_cases hw : w ∈ p1.support,
    { exact is_bridge_iff_no_cycle_contains.aux1 G c he hb hc.to_trail hv hw, },
    { have hw' : w ∈ p2.support,
      { have : c = p1.append p2 := by simp,
        rw [this, walk.mem_append_support_iff] at hwc,
        cases hwc,
        { exact (hw hwc).elim },
        { exact hwc }, },
      apply is_bridge_iff_no_cycle_contains.aux1 G (p2.append p1)
        (by { rw [walk.append_edges, list.mem_append, or_comm,
                  ←list.mem_append, ←walk.append_edges, walk.split_at_vertex_spec,
                  sym2.eq_swap],
              exact he })
        _ (walk.rotate_trail _ hc.to_trail hv),
      swap,
      { apply walk.mem_append_support,
        exact hw', },
      { simp, },
      { intro p,
        specialize hb p.reverse,
        rw sym2.eq_swap,
        simpa using hb, }, }, },
  { intro hc,
    rw is_bridge_iff_walks_contain,
    intro p,
    by_contra hne,
    specialize hc (walk.cons (G.sym h) p.to_path) _,
    { simp [walk.is_cycle_def, walk.cons_is_trail_iff],
      split,
      { intro h,
        apply hne,
        rw sym2.eq_swap at h,
        exact walk.to_path_edges_subset _ h, },
      { exact p.to_path.property.2, }, },
    simp [-quotient.eq] at hc,
    push_neg at hc,
    apply hc.1,
    rw sym2.eq_swap, },
end

lemma is_acyclic_iff_all_bridges : G.is_acyclic ↔ ∀ {v w : V}, G.adj v w → G.is_bridge v w :=
begin
  split,
  { intros ha v w hvw,
    rw is_bridge_iff_no_cycle_contains _ hvw,
    intros u p hp,
    exact (ha _ p hp).elim, },
  { intros hb v p hp,
    cases p,
    { simpa [walk.is_cycle_def] using hp, },
    { specialize hb p_h,
      rw is_bridge_iff_no_cycle_contains _ p_h at hb,
      apply hb _ hp,
      rw [walk.cons_edges],
      apply list.mem_cons_self, }, },
end

lemma unique_path_if_is_acyclic (h : G.is_acyclic) {v w : V} (p q : G.path v w) : p = q :=
begin
  obtain ⟨p, hp⟩ := p,
  obtain ⟨q, hq⟩ := q,
  simp only,
  induction p generalizing q,
  { by_cases hnq : q = walk.nil,
    { subst q, },
    { exfalso,
      cases q,
      exact (hnq rfl).elim,
      simpa [walk.is_path_def] using hq, }, },
  { rw is_acyclic_iff_all_bridges at h,
    specialize h p_h,
    rw is_bridge_iff_walks_contain at h,
    specialize h (q.append p_p.reverse),
    simp at h,
    cases h,
    { cases q,
      { exfalso,
        simpa [walk.is_path_def] using hp, },
      { rw walk.cons_is_path_iff at hp hq,
        simp [walk.edges] at h,
        cases h,
        { cases h,
          { congr,
            exact p_ih hp.1 _ hq.1, },
          { exfalso,
            apply hq.2,
            simp, }, },
        { exfalso,
          apply hq.2 (walk.edge_vert_mem_support _ h), }, }, },
    { rw walk.cons_is_path_iff at hp,
      exact (hp.2 (walk.edge_vert_mem_support _ h)).elim, }, },
end

lemma is_acyclic_if_unique_path (h : ∀ (v w : V) (p q : G.path v w), p = q) : G.is_acyclic :=
begin
  intros v c hc,
  simp [walk.is_cycle_def] at hc,
  cases c,
  { exact (hc.2.1 rfl).elim },
  { simp [walk.cons_is_trail_iff] at hc,
    have hp : c_p.is_path,
    { cases_matching* [_ ∧ _],
      simp only [walk.is_path_def],
      split; assumption, },
    specialize h _ _ ⟨c_p, hp⟩ (path.singleton (G.sym c_h)),
    simp [path.singleton] at h,
    subst c_p,
    simpa [walk.edges, -quotient.eq, sym2.eq_swap] using hc, },
end

lemma is_acyclic_iff : G.is_acyclic ↔ ∀ (v w : V) (p q : G.path v w), p = q :=
begin
  split,
  { apply unique_path_if_is_acyclic, },
  { apply is_acyclic_if_unique_path, },
end

lemma is_tree_iff : G.is_tree ↔ ∀ (v w : V), ∃!(p : G.walk v w), p.is_path :=
begin
  simp only [is_tree, is_acyclic_iff],
  split,
  { rintro ⟨hc, hu⟩ v w,
    let q := (hc v w).some.to_path,
    use q,
    simp only [true_and, path.path_is_path],
    intros p hp,
    specialize hu v w ⟨p, hp⟩ q,
    rw ←hu,
    refl, },
  { intro h,
    split,
    { intros v w,
      obtain ⟨p, hp⟩ := h v w,
      use p, },
    { rintros v w ⟨p, hp⟩ ⟨q, hq⟩,
      simp only,
      exact unique_of_exists_unique (h v w) hp hq, }, },
end

/-- Get the unique path between two vertices in the tree. -/
noncomputable abbreviation tree_path (h : G.is_tree) (v w : V) : G.path v w :=
⟨((G.is_tree_iff.mp h) v w).some, ((G.is_tree_iff.mp h) v w).some_spec.1⟩

lemma tree_path_spec {h : G.is_tree} {v w : V} (p : G.path v w) : p = G.tree_path h v w :=
begin
  cases p,
  have := ((G.is_tree_iff.mp h) v w).some_spec,
  simp only [this.2 p_val p_property],
end

/-- The tree metric, which is the length of the path between any two vertices.

Fixing a vertex as the root, then `G.tree_dist h root` gives the depth of each node with
respect to the root. -/
noncomputable def tree_dist (h : G.is_tree) (v w : V) : ℕ :=
walk.length (G.tree_path h v w : G.walk v w)

variables {G}

/-- Given a tree and a choice of root, then we can tell whether a given ordered
pair of adjacent vertices `v` and `w` is *rootward* based on whether or not `w` lies
on the path from `v` to the root.

This gives paths a canonical orientation in a rooted tree. -/
def is_rootward (h : G.is_tree) (root : V) (v w : V) : Prop :=
G.adj v w ∧ ⟦(v, w)⟧ ∈ (G.tree_path h v root : G.walk v root).edges

lemma is_rootward_antisymm (h : G.is_tree) (root : V) : anti_symmetric (is_rootward h root) :=
begin
  rintros v w ⟨ha, hvw⟩ ⟨ha', hwv⟩,
  by_contra hne,
  rw sym2.eq_swap at hwv,
  have hv := walk.edge_vert_mem_support _ hwv,
  have h' := h.2,
  rw is_acyclic_iff at h',
  specialize h' _ _
    (G.tree_path h v root)
    ⟨walk.split_at_vertex_snd _ _ hv, walk.split_at_vertex_snd_is_path _ (path.path_is_path _) _⟩,
  have hs := congr_arg (λ p, multiset.count w ↑(walk.support p)) (walk.split_at_vertex_spec _ hv),
  dsimp only at hs,
  rw h' at hvw,
  have hw := walk.edge_vert_mem_support _ hwv,
  rw walk.append_support' at hs,
  have : multiset.count w {v} = 0,
  { simp only [multiset.singleton_eq_singleton, multiset.count_eq_zero, multiset.mem_singleton], 
    exact ne.symm hne, },
  rw [multiset.count_sub, this, sub_zero', multiset.count_add] at hs,
  simp_rw [multiset.coe_count] at hs,
  rw [path.support_count_eq_one] at hs,
  swap, { simp, },
  rw walk.coe_path (walk.split_at_vertex_fst _ _ _) at hs,
  swap, { apply walk.split_at_vertex_fst_is_path, apply path.path_is_path, },
  rw walk.coe_path (walk.split_at_vertex_snd _ _ _) at hs,
  swap, { apply walk.split_at_vertex_snd_is_path, apply path.path_is_path, },
  rw [path.support_count_eq_one, path.support_count_eq_one] at hs,
  simpa using hs,
  apply walk.edge_vert_mem_support _ (by { rw [sym2.eq_swap], exact hvw }),
  apply walk.start_mem_support,
end

lemma is_rootward_or_reverse (h : G.is_tree) (root : V) {v w : V} (hvw : G.adj v w) :
  is_rootward h root v w ∨ is_rootward h root w v :=
begin
  have h' := h.2,
  rw is_acyclic_iff at h',
  by_contra hr,
  simp only [is_rootward] at hr,
  push_neg at hr,
  rcases hr with ⟨hrv, hrw⟩,
  specialize hrv hvw,
  specialize hrw (G.sym hvw),
  let p := (G.tree_path h v root : G.walk v root).append
           (G.tree_path h w root : G.walk w root).reverse,
  specialize h' _ _ (path.singleton hvw) p.to_path,
  have hp := walk.to_path_edges_subset p,
  rw [←h', walk.append_edges, walk.reverse_edges] at hp,
  specialize hp (path.singleton_edge_mem hvw),
  rw [list.mem_append, list.mem_reverse] at hp,
  rw sym2.eq_swap at hrw,
  cases hp; simpa only [hrv, hrw] using hp,
end

end simple_graph
