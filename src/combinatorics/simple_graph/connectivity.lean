/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.subgraph
import data.list.cycle

/-!

# Graph connectivity

In a simple graph,

* A *walk* is a finite sequence of adjacent vertices, and can be
  thought of equally well as a sequence of directed edges.

* A *trail* is a walk whose edges each appear no more than once.

* A *path* is a trail whose vertices appear no more than once.

* A *cycle* is a nonempty trail whose first and last vertices are the
  same and whose vertices except for the first appear no more than once.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `simple_graph.walk`

* `simple_graph.is_trail`, `simple_graph.is_path`, and `simple_graph.is_cycle`.

* `simple_graph.path`

* `simple_graph.reachable`, `simple_graph.connected`,
  and `simple_graph.connected_component`

* `simple_graph.is_acyclic` and `simple_graph.is_tree`

* `simple_graph.edge_connected` for k-edge-connectivity of a graph

## Tags
walks, trails, paths, circuits, cycles

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

lemma exists_eq_cons_of_ne : Π {u v : V} (hne : u ≠ v) (p : G.walk u v),
  ∃ (w : V) (h : G.adj u w) (p' : G.walk w v), p = cons h p'
| _ _ hne nil := (hne rfl).elim
| _ _ _ (cons h p') := ⟨_, h, p', rfl⟩

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
| _ _ _ (cons h p) q := reverse_aux p (cons (G.symm h) q)

/-- The walk in reverse. -/
@[symm]
def reverse {u v : V} (w : G.walk u v) : G.walk v u := w.reverse_aux nil

/-- Get the `n`th vertex from a walk, where `n` is generally expected to be
between `0` and `p.length`, inclusive.
If `n` is greater than or equal to `p.length`, the result is the path's endpoint. -/
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
| _ _ _ _ (cons h p') q r := by { dunfold append, rw append_assoc, }

@[simp] lemma reverse_nil {u : V} : (nil : G.walk u u).reverse = nil := rfl

lemma reverse_singleton {u v : V} (h : G.adj u v) :
  (cons h nil).reverse = cons (G.symm h) nil := rfl

@[simp] lemma cons_reverse_aux {u v w x : V} (p : G.walk u v) (q : G.walk w x) (h : G.adj w u) :
  (cons h p).reverse_aux q = p.reverse_aux (cons (G.symm h) q) := rfl

@[simp] protected lemma append_reverse_aux : Π {u v w x : V}
  (p : G.walk u v) (q : G.walk v w) (r : G.walk u x),
  (p.append q).reverse_aux r = q.reverse_aux (p.reverse_aux r)
| _ _ _ _ nil _ _ := rfl
| _ _ _ _ (cons h p') q r := append_reverse_aux p' q (cons (G.symm h) r)

@[simp] protected lemma reverse_aux_append : Π {u v w x : V}
  (p : G.walk u v) (q : G.walk u w) (r : G.walk w x),
  (p.reverse_aux q).append r = p.reverse_aux (q.append r)
| _ _ _ _ nil _ _ := rfl
| _ _ _ _ (cons h p') q r := by simp [reverse_aux_append p' (cons (G.symm h) q) r]

protected lemma reverse_aux_eq_reverse_append {u v w : V} (p : G.walk u v) (q : G.walk u w) :
  p.reverse_aux q = p.reverse.append q :=
by simp [reverse]

@[simp] lemma reverse_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).reverse = p.reverse.append (cons (G.symm h) nil) :=
by simp [reverse]

@[simp] lemma reverse_append {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.append q).reverse = q.reverse.append p.reverse :=
by simp [reverse]

@[simp] lemma reverse_reverse : Π {u v : V} (p : G.walk u v), p.reverse.reverse = p
| _ _ nil := rfl
| _ _ (cons h p) := by simp [reverse_reverse]

@[simp] lemma length_nil {u : V} : (nil : G.walk u u).length = 0 := rfl

@[simp] lemma length_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).length = p.length + 1 := rfl

@[simp] lemma length_append : Π {u v w : V} (p : G.walk u v) (q : G.walk v w),
  (p.append q).length = p.length + q.length
| _ _ _ nil _ := by simp
| _ _ _ (cons _ _) _ := by simp [length_append, add_left_comm, add_comm]

@[simp] protected lemma length_reverse_aux : Π {u v w : V} (p : G.walk u v) (q : G.walk u w),
  (p.reverse_aux q).length = p.length + q.length
| _ _ _ nil _ := by simp!
| _ _ _ (cons _ _) _ := by simp [length_reverse_aux, nat.add_succ, nat.succ_add]

@[simp] lemma length_reverse {u v : V} (p : G.walk u v) : p.reverse.length = p.length :=
by simp [reverse]

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support : Π {u v : V}, G.walk u v → list V
| u v nil := [u]
| u v (cons h p) := u :: p.support

/-- The `edges` of a walk is the list of edges it visits in order. -/
def edges : Π {u v : V}, G.walk u v → list (sym2 V)
| u v nil := []
| u v (@cons _ _ _ x _ h p) := ⟦(u, x)⟧ :: p.edges

@[simp] lemma support_nil {u : V} : (nil : G.walk u u).support = [u] := rfl

@[simp] lemma support_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).support = u :: p.support := rfl

lemma support_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  (p.append p').support = p.support ++ p'.support.tail :=
by induction p; cases p'; simp [*]

@[simp]
lemma support_reverse {u v : V} (p : G.walk u v) : p.reverse.support = p.support.reverse :=
by induction p; simp [support_append, *]

lemma support_ne_nil {u v : V} (p : G.walk u v) : p.support ≠ [] :=
by cases p; simp

lemma tail_support_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  (p.append p').support.tail = p.support.tail ++ p'.support.tail :=
by rw [support_append, list.tail_append_of_ne_nil _ _ (support_ne_nil _)]

lemma support_eq_cons {u v : V} (p : G.walk u v) : p.support = u :: p.support.tail :=
by cases p; simp

@[simp] lemma start_mem_support {u v : V} (p : G.walk u v) : u ∈ p.support :=
by cases p; simp

@[simp] lemma end_mem_support {u v : V} (p : G.walk u v) : v ∈ p.support :=
by induction p; simp [*]

lemma mem_support_iff {u v w : V} (p : G.walk u v) :
  w ∈ p.support ↔ w = u ∨ w ∈ p.support.tail :=
by cases p; simp

@[simp]
lemma mem_tail_support_append_iff {t u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  t ∈ (p.append p').support.tail ↔ t ∈ p.support.tail ∨ t ∈ p'.support.tail :=
by rw [tail_support_append, list.mem_append]

@[simp] lemma end_mem_tail_support_of_ne {u v : V} (h : u ≠ v) (p : G.walk u v) :
  v ∈ p.support.tail :=
by { obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p, simp }

@[simp]
lemma mem_support_append_iff {t u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  t ∈ (p.append p').support ↔ t ∈ p.support ∨ t ∈ p'.support :=
begin
  simp only [mem_support_iff, mem_tail_support_append_iff],
  by_cases h : t = v; by_cases h' : t = u;
  subst_vars;
  try { have := ne.symm h' };
  simp [*],
end

lemma coe_support {u v : V} (p : G.walk u v) :
  (p.support : multiset V) = {u} + p.support.tail :=
by cases p; refl

lemma coe_support_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  ((p.append p').support : multiset V) = {u} + p.support.tail + p'.support.tail :=
by rw [support_append, ←multiset.coe_add, coe_support]

lemma coe_support_append' [decidable_eq V] {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  ((p.append p').support : multiset V) = p.support + p'.support - {v} :=
begin
  rw [support_append, ←multiset.coe_add],
  simp only [coe_support],
  rw add_comm {v},
  simp only [← add_assoc, add_tsub_cancel_right],
end

lemma chain_adj_support_aux : Π {u v w : V} (h : G.adj u v) (p : G.walk v w),
  list.chain G.adj u p.support
| _ _ _ h nil := list.chain.cons h list.chain.nil
| _ _ _ h (cons h' p) := list.chain.cons h (chain_adj_support_aux h' p)

lemma chain_adj_support : Π {u v : V} (p : G.walk u v), list.chain' G.adj p.support
| _ _ nil := list.chain.nil
| _ _ (cons h p) := chain_adj_support_aux h p

/-- Every edge in a walk's edge list is an edge of the graph.
It is written in this form to avoid unsightly coercions. -/
lemma edges_subset_edge_set : Π {u v : V} (p : G.walk u v) {e : sym2 V}
  (h : e ∈ p.edges), e ∈ G.edge_set
| _ _ (cons h' p') e h := by rcases h with ⟨rfl, h⟩; solve_by_elim

@[simp] lemma edges_nil {u : V} : (nil : G.walk u u).edges = [] := rfl

@[simp] lemma edges_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).edges = ⟦(u, v)⟧ :: p.edges := rfl

@[simp] lemma edges_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  (p.append p').edges = p.edges ++ p'.edges :=
by induction p; simp [*]

@[simp] lemma edges_reverse {u v : V} (p : G.walk u v) : p.reverse.edges = p.edges.reverse :=
by induction p; simp [*, sym2.eq_swap]

@[simp] lemma length_support {u v : V} (p : G.walk u v) : p.support.length = p.length + 1 :=
by induction p; simp *

@[simp] lemma length_edges {u v : V} (p : G.walk u v) : p.edges.length = p.length :=
by induction p; simp *

lemma mem_support_of_mem_edges : Π {t u v w : V} (p : G.walk v w) (he : ⟦(t, u)⟧ ∈ p.edges),
  t ∈ p.support
| t u v w (cons h p') he := begin
  simp only [support_cons, edges_cons, list.mem_cons_iff, quotient.eq] at he ⊢,
  rcases he with ((he|he)|he),
  { exact or.inl rfl },
  { exact or.inr (start_mem_support _) },
  { exact or.inr (mem_support_of_mem_edges _ he), }
end

lemma edges_nodup_of_support_nodup {u v : V} {p : G.walk u v} (h : p.support.nodup) :
  p.edges.nodup :=
begin
  induction p,
  { simp, },
  { simp only [edges_cons, support_cons, list.nodup_cons] at h ⊢,
    exact ⟨λ h', h.1 (mem_support_of_mem_edges p_p h'), p_ih h.2⟩, }
end

/-- A *trail* is a walk with no repeating edges. -/
structure is_trail {u v : V} (p : G.walk u v) : Prop :=
(edges_nodup : p.edges.nodup)

/-- A *path* is a walk with no repeating vertices.
Use `simple_graph.walk.is_path.mk'` for a simpler constructor. -/
structure is_path {u v : V} (p : G.walk u v) extends to_trail : is_trail p : Prop :=
(support_nodup : p.support.nodup)

/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
structure is_circuit {u : V} (p : G.walk u u) extends to_trail : is_trail p : Prop :=
(ne_nil : p ≠ nil)

/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure is_cycle [decidable_eq V] {u : V} (p : G.walk u u)
  extends to_circuit : is_circuit p : Prop :=
(support_nodup : p.support.tail.nodup)

lemma is_trail_def {u v : V} (p : G.walk u v) : p.is_trail ↔ p.edges.nodup :=
⟨is_trail.edges_nodup, λ h, ⟨h⟩⟩

lemma is_path.mk' {u v : V} {p : G.walk u v} (h : p.support.nodup) : is_path p :=
⟨⟨edges_nodup_of_support_nodup h⟩, h⟩

lemma is_path_def {u v : V} (p : G.walk u v) : p.is_path ↔ p.support.nodup :=
⟨is_path.support_nodup, is_path.mk'⟩

lemma is_cycle_def [decidable_eq V] {u : V} (p : G.walk u u) :
  p.is_cycle ↔ is_trail p ∧ p ≠ nil ∧ p.support.tail.nodup :=
iff.intro (λ h, ⟨h.1.1, h.1.2, h.2⟩) (λ h, ⟨⟨h.1, h.2.1⟩, h.2.2⟩)

@[simp] lemma is_trail.nil {u : V} : (nil : G.walk u u).is_trail :=
⟨by simp [edges]⟩

lemma is_trail.of_cons {u v w : V} {h : G.adj u v} {p : G.walk v w} :
  (cons h p).is_trail → p.is_trail :=
by simp [is_trail_def]

@[simp] lemma cons_is_trail_iff {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).is_trail ↔ p.is_trail ∧ ⟦(u, v)⟧ ∉ p.edges :=
by simp [is_trail_def, and_comm]

lemma is_trail.reverse {u v : V} (p : G.walk u v) (h : p.is_trail) : p.reverse.is_trail :=
by simpa [is_trail_def] using h

@[simp] lemma reverse_is_trail_iff {u v : V} (p : G.walk u v) : p.reverse.is_trail ↔ p.is_trail :=
by split; { intro h, convert h.reverse _, try { rw reverse_reverse } }

lemma is_trail.of_append_left {u v w : V} {p : G.walk u v} {q : G.walk v w}
  (h : (p.append q).is_trail) : p.is_trail :=
by { rw [is_trail_def, edges_append, list.nodup_append] at h, exact ⟨h.1⟩ }

lemma is_trail.of_append_right {u v w : V} {p : G.walk u v} {q : G.walk v w}
  (h : (p.append q).is_trail) : q.is_trail :=
by { rw [is_trail_def, edges_append, list.nodup_append] at h, exact ⟨h.2.1⟩ }

lemma is_trail.count_edges_le_one [decidable_eq V] {u v : V}
  {p : G.walk u v} (h : p.is_trail) (e : sym2 V) : p.edges.count e ≤ 1 :=
list.nodup_iff_count_le_one.mp h.edges_nodup e

lemma is_trail.count_edges_eq_one [decidable_eq V] {u v : V}
  {p : G.walk u v} (h : p.is_trail) {e : sym2 V} (he : e ∈ p.edges) :
  p.edges.count e = 1 :=
list.count_eq_one_of_mem h.edges_nodup he

@[simp] lemma is_path.nil {u : V} : (nil : G.walk u u).is_path :=
by { fsplit; simp }

lemma is_path.of_cons {u v w : V} {h : G.adj u v} {p : G.walk v w} :
  (cons h p).is_path → p.is_path :=
by simp [is_path_def]

@[simp] lemma cons_is_path_iff {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).is_path ↔ p.is_path ∧ u ∉ p.support :=
by split; simp [is_path_def] { contextual := tt }

lemma is_path.reverse {u v : V} {p : G.walk u v} (h : p.is_path) : p.reverse.is_path :=
by simpa [is_path_def] using h

@[simp] lemma is_path_reverse_iff {u v : V} (p : G.walk u v) : p.reverse.is_path ↔ p.is_path :=
by split; intro h; convert h.reverse; simp

lemma is_path.of_append_left {u v w : V} {p : G.walk u v} {q : G.walk v w} :
  (p.append q).is_path → p.is_path :=
by { simp only [is_path_def, support_append], exact list.nodup_of_nodup_append_left }

lemma is_path.of_append_right {u v w : V} {p : G.walk u v} {q : G.walk v w}
  (h : (p.append q).is_path) : q.is_path :=
begin
  rw ←is_path_reverse_iff at h ⊢,
  rw reverse_append at h,
  apply h.of_append_left,
end

end walk

-- ^^^ in mathlib ^^^

namespace walk
variables {G}

lemma mem_support_nil_iff {u v : V} : u ∈ (nil : G.walk v v).support ↔ u = v :=
by simp

end walk

-- ^^^ in a PR ^^^

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

/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def preconnected : Prop := ∀ (u v : V), G.reachable u v

/-- A graph is connected if it's preconnected and contains at least one vertex. -/
@[protect_proj]
structure connected : Prop :=
(preconnected : G.preconnected)
(nonempty : nonempty V)

/-- Gives the connected component containing a particular vertex. -/
def connected_component_of (v : V) : G.connected_component := quot.mk G.reachable v

instance connected_components.inhabited [inhabited V] : inhabited G.connected_component :=
⟨G.connected_component_of (default _)⟩

lemma connected_component.subsingleton_of_connected (h : G.preconnected) :
  subsingleton G.connected_component :=
⟨λ c d, quot.ind (λ v d, quot.ind (λ w, quot.sound (h v w)) d) c d⟩

/-- A subgraph is connected if it is connected as a simple graph. -/
abbreviation subgraph.connected {G : simple_graph V} (H : G.subgraph) : Prop := H.coe.connected

/-- A graph is *k-edge-connected* if it remains connected whenever
fewer than k edges are removed. -/
def edge_connected (k : ℕ) : Prop :=
∀ s : finset (sym2 V), ↑s ⊆ G.edge_set → s.card < k → ((⊤ : subgraph G).delete_edges ↑s).connected

section walk_to_path

/-- The type of paths between two vertices. -/
abbreviation path (u v : V) := {p : G.walk u v // p.is_path}

namespace walk
variables {G}

variables [decidable_eq V]

/-- Given a vertex in the support of a path, give the path up until that vertex. -/
def take_until : Π {v w : V} (p : G.walk v w) (u : V) (h : u ∈ p.support), G.walk v u
| v w nil u h := by rw mem_support_nil_iff.mp h
| v w (cons r p) u h :=
  if hx : v = u
  then by subst u
  else cons r (take_until p _ $ h.cases_on (λ h', (hx h'.symm).elim) id)

/-- Given a vertex in the support of a path, give the path from that vertex to the end. -/
def drop_until : Π {v w : V} (p : G.walk v w) (u : V) (h : u ∈ p.support), G.walk u w
| v w nil u h := by rw mem_support_nil_iff.mp h
| v w (cons r p) u h :=
  if hx : v = u
  then by { subst u, exact cons r p }
  else drop_until p _ $ h.cases_on (λ h', (hx h'.symm).elim) id

/-- The `take_until` and `drop_until` functions split a walk into two pieces.
The lemma `count_support_take_until_eq_one` specifies where this split occurs. -/
@[simp]
lemma take_spec {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.take_until u h).append (p.drop_until u h) = p :=
begin
  induction p,
  { rw mem_support_nil_iff at h,
    subst u,
    refl, },
  { obtain (rfl|h) := h,
    { simp! },
    { simp! only,
      split_ifs with h'; subst_vars; simp [*], } },
end

@[simp]
lemma count_support_take_until_eq_one {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.take_until u h).support.count u = 1 :=
begin
  induction p,
  { rw mem_support_nil_iff at h,
    subst u,
    simp!, },
  { obtain (rfl|h) := h,
    { simp! },
    { simp! only,
      split_ifs with h'; rw eq_comm at h'; subst_vars; simp! [*, list.count_cons], } },
end

lemma count_edges_take_until_le_one {u v w : V} (p : G.walk v w) (h : u ∈ p.support) (x : V) :
  (p.take_until u h).edges.count ⟦(u, x)⟧ ≤ 1 :=
begin
  induction p with u' u' v' w' ha p' ih,
  { rw mem_support_nil_iff at h,
    subst u,
    simp!, },
  { obtain (rfl|h) := h,
    { simp!, },
    { simp! only,
      split_ifs with h',
      { subst h',
        simp, },
      { rw [edges_cons, list.count_cons],
        split_ifs with h'',
        { rw sym2.eq_iff at h'',
          obtain (⟨rfl,rfl⟩|⟨rfl,rfl⟩) := h'',
          { exact (h' rfl).elim },
          { cases p'; simp! } },
        { apply ih, } } } },
end

lemma support_take_until_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.take_until u h).support ⊆ p.support :=
λ x hx, by { rw [← take_spec p h, mem_support_append_iff], exact or.inl hx }

lemma support_drop_until_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.drop_until u h).support ⊆ p.support :=
λ x hx, by { rw [← take_spec p h, mem_support_append_iff], exact or.inr hx }

lemma edges_take_until_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.take_until u h).edges ⊆ p.edges :=
λ x hx, by { rw [← take_spec p h, edges_append, list.mem_append], exact or.inl hx }

lemma edges_drop_until_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.drop_until u h).edges ⊆ p.edges :=
λ x hx, by { rw [← take_spec p h, edges_append, list.mem_append], exact or.inr hx }

lemma is_trail.take_until {u v w : V} {p : G.walk v w} (hc : p.is_trail) (h : u ∈ p.support) :
  (p.take_until u h).is_trail :=
is_trail.of_append_left (by rwa ← take_spec _ h at hc)

lemma is_trail.drop_until {u v w : V} {p : G.walk v w} (hc : p.is_trail) (h : u ∈ p.support) :
  (p.drop_until u h).is_trail :=
is_trail.of_append_right (by rwa ← take_spec _ h at hc)

lemma is_path.take_until {u v w : V} {p : G.walk v w} (hc : p.is_path) (h : u ∈ p.support) :
  (p.take_until u h).is_path :=
is_path.of_append_left (by rwa ← take_spec _ h at hc)

lemma is_path.drop_until {u v w : V} (p : G.walk v w) (hc : p.is_path) (h : u ∈ p.support) :
  (p.drop_until u h).is_path :=
is_path.of_append_right (by rwa ← take_spec _ h at hc)

/-- Given a vertex in the tail support of a path, give the path up until that vertex.
Useful for when `u` might equal `v`. -/
def take_until' : Π {v w : V} (p : G.walk v w) (u : V) (h : u ∈ p.support.tail), G.walk v u
| v w nil u h := by simpa using h
| v w (cons r p) u h := cons r (p.take_until u h)

/-- Given a vertex in the tail support of a path, give the path from that vertex to the end.
Useful for when `u` might equal `v`. -/
def drop_until' : Π {v w : V} (p : G.walk v w) (u : V) (h : u ∈ p.support.tail), G.walk u w
| v w nil u h := by simpa using h
| v w (cons r p) u h := p.drop_until u h

lemma take_spec' {u v w : V} (p : G.walk v w) (h : u ∈ p.support.tail) :
  (p.take_until' u h).append (p.drop_until' u h) = p :=
begin
  cases p,
  { simpa using h, },
  { simp!, },
end

/-- Rotate a loop walk such that it is centered at the given vertex. -/
def rotate {u v : V} (c : G.walk v v) (h : u ∈ c.support) : G.walk u u :=
(c.drop_until u h).append (c.take_until u h)

@[simp]
lemma rotate_support {u v : V} (c : G.walk v v) (h : u ∈ c.support) :
  (c.rotate h).support.tail ~r c.support.tail :=
begin
  simp only [rotate, tail_support_append],
  apply list.is_rotated.trans list.is_rotated_append,
  rw [←tail_support_append, take_spec],
end

lemma rotate_edges {u v : V} (c : G.walk v v) (h : u ∈ c.support) :
  (c.rotate h).edges ~r c.edges :=
begin
  simp only [rotate, edges_append],
  apply list.is_rotated.trans list.is_rotated_append,
  rw [←edges_append, take_spec],
end

lemma is_trail.rotate {u v : V} {c : G.walk v v} (hc : c.is_trail) (h : u ∈ c.support) :
  (c.rotate h).is_trail :=
begin
  rw [is_trail_def, (c.rotate_edges h).perm.nodup_iff],
  exact hc.edges_nodup,
end

lemma is_circuit.rotate {u v : V} {c : G.walk v v} (hc : c.is_circuit) (h : u ∈ c.support) :
  (c.rotate h).is_circuit :=
begin
  refine ⟨hc.to_trail.rotate _, _⟩,
  cases c,
  { exact (hc.ne_nil rfl).elim, },
  { intro hn,
    have hn' := congr_arg length hn,
    rw [rotate, length_append, add_comm, ← length_append, take_spec] at hn',
    simpa using hn', },
end

lemma is_cycle.rotate {u v : V} {c : G.walk v v} (hc : c.is_cycle) (h : u ∈ c.support) :
  (c.rotate h).is_cycle :=
begin
  refine ⟨hc.to_circuit.rotate _, _⟩,
  rw list.is_rotated.nodup_iff (rotate_support _ _),
  exact hc.support_nodup,
end

/-- Given a walk, produces a walk with the same endpoints and no repeated vertices. -/
def to_path_aux : Π {u v : V}, G.walk u v → G.walk u v
| u v nil := nil
| u v (cons ha p) :=
  let p' := p.to_path_aux
  in if hs : u ∈ p'.support
     then p'.drop_until u hs
     else cons ha p'

lemma to_path_aux_is_path {u v : V} (p : G.walk u v) : p.to_path_aux.is_path :=
begin
  induction p,
  { simp!, },
  { simp! only,
    split_ifs,
    { apply is_path.drop_until,
      assumption, },
    { simp [*, cons_is_path_iff], } },
end

/-- Given a walk, produces a path with the same endpoints using `simple_graph.walk.to_path_aux`. -/
def to_path {u v : V} (p : G.walk u v) : G.path u v := ⟨p.to_path_aux, p.to_path_aux_is_path⟩

lemma support_to_path_aux_subset {u v : V} (p : G.walk u v) : p.to_path_aux.support ⊆ p.support :=
begin
  induction p,
  { simp!, },
  { simp! only,
    split_ifs,
    { apply list.subset.trans (support_drop_until_subset _ _),
      apply list.subset_cons_of_subset,
      assumption, },
    { rw support_cons,
      apply list.cons_subset_cons,
      assumption, }, },
end

lemma support_to_path_subset {u v : V} (p : G.walk u v) :
  (p.to_path : G.walk u v).support ⊆ p.support :=
by simp [to_path, support_to_path_aux_subset]

lemma edges_to_path_aux_subset {u v : V} (p : G.walk u v) : p.to_path_aux.edges ⊆ p.edges :=
begin
  induction p,
  { simp [to_path_aux], },
  { simp [to_path_aux],
    split_ifs,
    { apply list.subset.trans (edges_drop_until_subset _ _),
      apply list.subset_cons_of_subset _ p_ih, },
    { rw edges_cons,
      exact list.cons_subset_cons _ p_ih, }, },
end

lemma edges_to_path_subset {u v : V} (p : G.walk u v) :
  (p.to_path : G.walk u v).edges ⊆ p.edges :=
by simp [to_path, edges_to_path_aux_subset]

end walk

namespace walk
variables {G}

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
⟨walk.cons h walk.nil, by simp [walk.is_path_def, walk.is_trail_def, walk.edges, G.ne_of_adj h]⟩

lemma singleton_edge_mem {u v : V} (h : G.adj u v) : ⟦(u, v)⟧ ∈ (singleton h : G.walk u v).edges :=
by simp [singleton]

/-- The reverse of a path is another path.  See `simple_graph.walk.reverse`. -/
@[symm] def reverse {u v : V} (p : G.path u v) : G.path v u :=
by { classical,
     exact ⟨walk.reverse p, p.property.reverse⟩ }

lemma support_count_eq_one [decidable_eq V] {u v w : V} {p : G.path u v}
  (hw : w ∈ (p : G.walk u v).support) : (p : G.walk u v).support.count w = 1 :=
list.count_eq_one_of_mem p.property.support_nodup hw

lemma edges_count_eq_one [decidable_eq V] {u v : V} {p : G.path u v} (e : sym2 V)
  (hw : e ∈ (p : G.walk u v).edges) : (p : G.walk u v).edges.count e = 1 :=
list.count_eq_one_of_mem p.property.to_trail.edges_nodup hw

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

-- lemma edge_connected.to_preconnected {k : ℕ} (h : G.edge_connected k) (hk : 0 < k) :
--   G.preconnected :=
-- begin
--   intros v w,
--   have h' := (h ∅ (by simp) (by simp [hk])).preconnected v w,
--   simp only [finset.coe_empty, delete_edges_empty_eq] at h',
--   exact h',
-- end

-- lemma edge_connected.to_connected {k : ℕ} (h : G.edge_connected k) (hk : 0 < k) : G.connected :=
-- let C' := h ∅ (by simp) (by simp [hk]) in
-- { preconnected := by simpa using C'.preconnected,
--   nonempty := C'.nonempty }

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

Since this is for simple graphs, we use the endpoints of the vertices as the edge itself.

Implementation note: this uses `simple_graph.subgraph.spanning_coe` since adding
vertices to a subgraph does not change reachability, and it is simpler than
dealing with the dependent types from `simple_graph.subgraph.coe`. -/
def is_bridge (v w : V) : Prop :=
¬(H.delete_edges {⟦(v, w)⟧}).spanning_coe.reachable v w

end subgraph

variables [decidable_eq V]

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
      assumption, },
    specialize h _ _ ⟨c_p, hp⟩ (path.singleton (G.symm c_h)),
    simp [path.singleton] at h,
    subst c_p,
    simpa [walk.edges, -quotient.eq, sym2.eq_swap] using hc, },
end

variables {G}

open fintype

/-- Get the next edge after vertext `v` on a path `p` from `v` to vertex `w`. -/
def next_edge (G : simple_graph V) : ∀ (v w : V) (h : v ≠ w) (p : G.walk v w), G.incidence_set v
| v w h walk.nil := (h rfl).elim
| v w h (@walk.cons _ _ _ u _ hvw _) := ⟨⟦(v, u)⟧, hvw, sym2.mem_mk_left _ _⟩

lemma nonempty_path_not_loop {v : V} {e : sym2 V} (p : G.path v v)
  (h : e ∈ walk.edges (p : G.walk v v)) : false :=
begin
  cases p with p hp,
  cases p,
  { exact h, },
  { cases hp,
    simpa using hp_support_nodup, },
end

lemma eq_next_edge_if_mem_path {u v w : V}
  (hne : u ≠ v) (hinc : ⟦(u, w)⟧ ∈ G.incidence_set u)
  (p : G.path u v) (h : ⟦(u, w)⟧ ∈ (p : G.walk u v).edges) :
  G.next_edge u v hne p = ⟨⟦(u, w)⟧, hinc⟩ :=
begin
  cases p with p hp,
  cases p,
  { exact (hne rfl).elim },
  { cases hp,
    simp at hp_support_nodup,
    simp only [next_edge, subtype.mk_eq_mk, subtype.coe_mk],
    congr,
    simp only [list.mem_cons_iff, subtype.coe_mk, simple_graph.walk.edges_cons, sym2.eq_iff] at h,
    cases h,
    { obtain (⟨_,rfl⟩|⟨rfl,rfl⟩) := h; refl, },
    { have h := walk.mem_support_of_mem_edges _ h,
      exact (hp_support_nodup.1 h).elim, }, },
end

lemma next_edge_mem_edges (G : simple_graph V) (v w : V) (h : v ≠ w) (p : G.walk v w) :
  (G.next_edge v w h p : sym2 V) ∈ p.edges :=
begin
  cases p with p hp,
  { exact (h rfl).elim },
  { simp only [next_edge, list.mem_cons_iff, walk.edges_cons, subtype.coe_mk],
    left,
    refl,},
end

end simple_graph
