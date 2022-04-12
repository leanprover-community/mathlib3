/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import data.list
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

* `simple_graph.walk` (with accompanying pattern definitions
  `simple_graph.walk.nil'` and `simple_graph.walk.cons'`)

* `simple_graph.walk.is_trail`, `simple_graph.walk.is_path`, and `simple_graph.walk.is_cycle`.

* `simple_graph.path`

* `simple_graph.reachable` for the relation of whether there exists
  a walk between a given pair of vertices

* `simple_graph.preconnected` and `simple_graph.connected` are predicates
  on simple graphs for whether every vertex can be reached from every other,
  and in the latter case, whether the vertex type is nonempty.

* `simple_graph.subgraph.connected` gives subgraphs the connectivity
  predicate via `simple_graph.subgraph.coe`.

* `simple_graph.connected_component`

* `simple_graph.is_acyclic` and `simple_graph.is_tree`

* `simple_graph.edge_connected` for k-edge-connectivity of a graph

## Tags
walks, trails, paths, circuits, cycles

-/

@[simp] lemma function.injective.mem_list_map_iff {α β : Type*} {f : α → β} {l : list α} {a : α}
  (hf : function.injective f) :
  f a ∈ l.map f ↔ a ∈ l :=
begin
  refine ⟨λ h, _, list.mem_map_of_mem f⟩,
  obtain ⟨y, hy, heq⟩ := list.mem_map.1 h,
  exact hf heq ▸ hy,
end

universes u

open function

namespace simple_graph
variables {V : Type u} {V' : Type*} (G : simple_graph V)

lemma dart.to_prod_injective {G : simple_graph V} : injective (dart.to_prod : G.dart → V × V) :=
λ d e h, by { cases d, cases e, congr' }

/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `simple_graph.walk.support`.

See `simple_graph.walk.nil'` and `simple_graph.walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
@[derive decidable_eq]
inductive walk : V → V → Type u
| nil {u : V} : walk u u
| cons {u v w: V} (h : G.adj u v) (p : walk v w) : walk u w

attribute [refl] walk.nil

instance walk.inhabited (v : V) : inhabited (G.walk v v) := ⟨by refl⟩

namespace walk
variables {G} {u v w : V} {p : G.walk u v} {d : G.dart}

/-- Pattern to get `walk.nil` with the vertex as an explicit argument. -/
@[pattern] abbreviation nil' (u : V) : G.walk u u := walk.nil

/-- Pattern to get `walk.cons` with the vertices as explicit arguments. -/
@[pattern] abbreviation cons' (u v w : V) (h : G.adj u v) (p : G.walk v w) : G.walk u w :=
walk.cons h p

lemma exists_eq_cons_of_ne : Π {u v : V} (hne : u ≠ v) (p : G.walk u v),
  ∃ (w : V) (h : G.adj u w) (p' : G.walk w v), p = cons h p'
| _ _ hne nil := (hne rfl).elim
| _ _ _ (cons h p') := ⟨_, h, p', rfl⟩

/-- The length of a walk is the number of edges/darts along it. -/
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

@[simp] lemma get_vert_zero {u v} (w : G.walk u v) : w.get_vert 0 = u :=
by { cases w; refl }

lemma get_vert_of_length_le {u v} (w : G.walk u v) {i : ℕ} (hi : w.length ≤ i) :
  w.get_vert i = v :=
begin
  induction w with _ x y z hxy wyz IH generalizing i,
  { refl },
  { cases i,
    { cases hi, },
    { exact IH (nat.succ_le_succ_iff.1 hi) } }
end

@[simp] lemma get_vert_length {u v} (w : G.walk u v) : w.get_vert w.length = v :=
w.get_vert_of_length_le rfl.le

lemma adj_get_vert_succ {u v} (w : G.walk u v) {i : ℕ} (hi : i < w.length) :
  G.adj (w.get_vert i) (w.get_vert (i+1)) :=
begin
  induction w with _ x y z hxy wyz IH generalizing i,
  { cases hi, },
  { cases i,
    { simp [get_vert, hxy] },
    { exact IH (nat.succ_lt_succ_iff.1 hi) } },
end

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

lemma eq_of_length_eq_zero : Π {u v : V} {p : G.walk u v}, p.length = 0 → u = v
| _ _ nil _ := rfl

@[simp] lemma exists_length_eq_zero_iff {u v : V} : (∃ (p : G.walk u v), p.length = 0) ↔ u = v :=
begin
  split,
  { rintro ⟨p, hp⟩,
    exact eq_of_length_eq_zero hp, },
  { rintro rfl,
    exact ⟨nil, rfl⟩, },
end

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support : Π {u v : V}, G.walk u v → list V
| u v nil := [u]
| u v (cons h p) := u :: p.support

/-- The `darts` of a walk is the list of darts it visits in order. -/
def darts : Π {u v : V}, G.walk u v → list G.dart
| u v nil := []
| u v (cons h p) := ⟨(u, _), h⟩ :: p.darts

/-- The `edges` of a walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `simple_graph.walk.darts`. -/
def edges {u v : V} (p : G.walk u v) : list (sym2 V) := p.darts.map dart.edge

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

lemma mem_support_nil_iff {u v : V} : u ∈ (nil : G.walk v v).support ↔ u = v := by simp

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

lemma chain_adj_support : Π {u v w : V} (h : G.adj u v) (p : G.walk v w),
  list.chain G.adj u p.support
| _ _ _ h nil := list.chain.cons h list.chain.nil
| _ _ _ h (cons h' p) := list.chain.cons h (chain_adj_support h' p)

lemma chain'_adj_support : Π {u v : V} (p : G.walk u v), list.chain' G.adj p.support
| _ _ nil := list.chain.nil
| _ _ (cons h p) := chain_adj_support h p

lemma chain_dart_adj_darts : Π {d : G.dart} {v w : V} (h : d.snd = v) (p : G.walk v w),
  list.chain G.dart_adj d p.darts
| _ _ _ h nil := list.chain.nil
| _ _ _ h (cons h' p) := list.chain.cons h (chain_dart_adj_darts (by exact rfl) p)

lemma chain'_dart_adj_darts : Π {u v : V} (p : G.walk u v), list.chain' G.dart_adj p.darts
| _ _ nil := trivial
| _ _ (cons h p) := chain_dart_adj_darts rfl p

/-- Every edge in a walk's edge list is an edge of the graph.
It is written in this form (rather than using `⊆`) to avoid unsightly coercions. -/
lemma edges_subset_edge_set : Π {u v : V} (p : G.walk u v) ⦃e : sym2 V⦄
  (h : e ∈ p.edges), e ∈ G.edge_set
| _ _ (cons h' p') e h := by rcases h with ⟨rfl, h⟩; solve_by_elim

@[simp] lemma darts_nil {u : V} : (nil : G.walk u u).darts = [] := rfl

@[simp] lemma darts_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).darts = ⟨(u, v), h⟩ :: p.darts := rfl

@[simp] lemma darts_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  (p.append p').darts = p.darts ++ p'.darts :=
by induction p; simp [*]

@[simp] lemma darts_reverse {u v : V} (p : G.walk u v) :
  p.reverse.darts = (p.darts.map dart.symm).reverse :=
by induction p; simp [*, sym2.eq_swap]

lemma cons_map_snd_darts {u v : V} (p : G.walk u v) :
  u :: p.darts.map dart.snd = p.support :=
by induction p; simp! [*]

lemma map_snd_darts {u v : V} (p : G.walk u v) :
  p.darts.map dart.snd = p.support.tail :=
by simpa using congr_arg list.tail (cons_map_snd_darts p)

lemma map_fst_darts_append {u v : V} (p : G.walk u v) :
  p.darts.map dart.fst ++ [v] = p.support :=
by induction p; simp! [*]

lemma map_fst_darts {u v : V} (p : G.walk u v) :
  p.darts.map dart.fst = p.support.init :=
by simpa! using congr_arg list.init (map_fst_darts_append p)

@[simp] lemma edges_nil {u : V} : (nil : G.walk u u).edges = [] := rfl

@[simp] lemma edges_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).edges = ⟦(u, v)⟧ :: p.edges := rfl

@[simp] lemma edges_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  (p.append p').edges = p.edges ++ p'.edges :=
by simp [edges]

@[simp] lemma edges_reverse {u v : V} (p : G.walk u v) : p.reverse.edges = p.edges.reverse :=
by simp [edges]

@[simp] lemma length_support {u v : V} (p : G.walk u v) : p.support.length = p.length + 1 :=
by induction p; simp *

@[simp] lemma length_darts {u v : V} (p : G.walk u v) : p.darts.length = p.length :=
by induction p; simp *

@[simp] lemma length_edges {u v : V} (p : G.walk u v) : p.edges.length = p.length :=
by simp [edges]

lemma dart_fst_mem_support_of_mem_darts :
  Π {u v : V} (p : G.walk u v) {d : G.dart}, d ∈ p.darts → d.fst ∈ p.support
| u v (cons h p') d hd := begin
  simp only [support_cons, darts_cons, list.mem_cons_iff] at hd ⊢,
  rcases hd with (rfl|hd),
  { exact or.inl rfl, },
  { exact or.inr (dart_fst_mem_support_of_mem_darts _ hd), },
end

lemma dart_snd_mem_support_of_mem_darts :
  Π {u v : V} (p : G.walk u v) {d : G.dart}, d ∈ p.darts → d.snd ∈ p.support
| u v (cons h p') d hd := begin
  simp only [support_cons, darts_cons, list.mem_cons_iff] at hd ⊢,
  rcases hd with (rfl|hd),
  { simp },
  { exact or.inr (dart_snd_mem_support_of_mem_darts _ hd), },
end

lemma mem_support_of_mem_edges {t u v w : V} (p : G.walk v w) (he : ⟦(t, u)⟧ ∈ p.edges) :
  t ∈ p.support :=
begin
  obtain ⟨d, hd, he⟩ := list.mem_map.mp he,
  rw dart_edge_eq_mk_iff' at he,
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
  { exact dart_fst_mem_support_of_mem_darts _ hd, },
  { exact dart_snd_mem_support_of_mem_darts _ hd, },
end

lemma darts_nodup_of_support_nodup {u v : V} {p : G.walk u v} (h : p.support.nodup) :
  p.darts.nodup :=
begin
  induction p,
  { simp, },
  { simp only [darts_cons, support_cons, list.nodup_cons] at h ⊢,
    refine ⟨λ h', h.1 (dart_fst_mem_support_of_mem_darts p_p h'), p_ih h.2⟩, }
end

lemma edges_nodup_of_support_nodup {u v : V} {p : G.walk u v} (h : p.support.nodup) :
  p.edges.nodup :=
begin
  induction p,
  { simp, },
  { simp only [edges_cons, support_cons, list.nodup_cons] at h ⊢,
    exact ⟨λ h', h.1 (mem_support_of_mem_edges p_p h'), p_ih h.2⟩, }
end

/-! ### Trails, paths, circuits, cycles -/

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
structure is_cycle {u : V} (p : G.walk u u)
  extends to_circuit : is_circuit p : Prop :=
(support_nodup : p.support.tail.nodup)

lemma is_trail_def {u v : V} (p : G.walk u v) : p.is_trail ↔ p.edges.nodup :=
⟨is_trail.edges_nodup, λ h, ⟨h⟩⟩

lemma is_path.mk' {u v : V} {p : G.walk u v} (h : p.support.nodup) : is_path p :=
⟨⟨edges_nodup_of_support_nodup h⟩, h⟩

lemma is_path_def {u v : V} (p : G.walk u v) : p.is_path ↔ p.support.nodup :=
⟨is_path.support_nodup, is_path.mk'⟩

lemma is_cycle_def {u : V} (p : G.walk u u) :
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
by { simp only [is_path_def, support_append], exact list.nodup.of_append_left }

lemma is_path.of_append_right {u v w : V} {p : G.walk u v} {q : G.walk v w}
  (h : (p.append q).is_path) : q.is_path :=
begin
  rw ←is_path_reverse_iff at h ⊢,
  rw reverse_append at h,
  apply h.of_append_left,
end

/-! ### Walk decompositions -/

section walk_decomp
variables [decidable_eq V]

/-- Given a vertex in the support of a path, give the path up until (and including) that vertex. -/
def take_until : Π {v w : V} (p : G.walk v w) (u : V) (h : u ∈ p.support), G.walk v u
| v w nil u h := by rw mem_support_nil_iff.mp h
| v w (cons r p) u h :=
  if hx : v = u
  then by subst u
  else cons r (take_until p _ $ h.cases_on (λ h', (hx h'.symm).elim) id)

/-- Given a vertex in the support of a path, give the path from (and including) that vertex to
the end. In other words, drop vertices from the front of a path until (and not including)
that vertex. -/
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

lemma darts_take_until_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.take_until u h).darts ⊆ p.darts :=
λ x hx, by { rw [← take_spec p h, darts_append, list.mem_append], exact or.inl hx }

lemma darts_drop_until_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.drop_until u h).darts ⊆ p.darts :=
λ x hx, by { rw [← take_spec p h, darts_append, list.mem_append], exact or.inr hx }

lemma edges_take_until_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.take_until u h).edges ⊆ p.edges :=
list.map_subset _ (p.darts_take_until_subset h)

lemma edges_drop_until_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.drop_until u h).edges ⊆ p.edges :=
list.map_subset _ (p.darts_drop_until_subset h)

lemma length_take_until_le {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.take_until u h).length ≤ p.length :=
begin
  have := congr_arg walk.length (p.take_spec h),
  rw [length_append] at this,
  exact nat.le.intro this,
end

lemma length_drop_until_le {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.drop_until u h).length ≤ p.length :=
begin
  have := congr_arg walk.length (p.take_spec h),
  rw [length_append, add_comm] at this,
  exact nat.le.intro this,
end

protected
lemma is_trail.take_until {u v w : V} {p : G.walk v w} (hc : p.is_trail) (h : u ∈ p.support) :
  (p.take_until u h).is_trail :=
is_trail.of_append_left (by rwa ← take_spec _ h at hc)

protected
lemma is_trail.drop_until {u v w : V} {p : G.walk v w} (hc : p.is_trail) (h : u ∈ p.support) :
  (p.drop_until u h).is_trail :=
is_trail.of_append_right (by rwa ← take_spec _ h at hc)

protected
lemma is_path.take_until {u v w : V} {p : G.walk v w} (hc : p.is_path) (h : u ∈ p.support) :
  (p.take_until u h).is_path :=
is_path.of_append_left (by rwa ← take_spec _ h at hc)

protected
lemma is_path.drop_until {u v w : V} (p : G.walk v w) (hc : p.is_path) (h : u ∈ p.support) :
  (p.drop_until u h).is_path :=
is_path.of_append_right (by rwa ← take_spec _ h at hc)

/-- Rotate a loop walk such that it is centered at the given vertex. -/
def rotate {u v : V} (c : G.walk v v) (h : u ∈ c.support) : G.walk u u :=
(c.drop_until u h).append (c.take_until u h)

@[simp]
lemma support_rotate {u v : V} (c : G.walk v v) (h : u ∈ c.support) :
  (c.rotate h).support.tail ~r c.support.tail :=
begin
  simp only [rotate, tail_support_append],
  apply list.is_rotated.trans list.is_rotated_append,
  rw [←tail_support_append, take_spec],
end

lemma rotate_darts {u v : V} (c : G.walk v v) (h : u ∈ c.support) :
  (c.rotate h).darts ~r c.darts :=
begin
  simp only [rotate, darts_append],
  apply list.is_rotated.trans list.is_rotated_append,
  rw [←darts_append, take_spec],
end

lemma rotate_edges {u v : V} (c : G.walk v v) (h : u ∈ c.support) :
  (c.rotate h).edges ~r c.edges :=
(rotate_darts c h).map _

protected
lemma is_trail.rotate {u v : V} {c : G.walk v v} (hc : c.is_trail) (h : u ∈ c.support) :
  (c.rotate h).is_trail :=
begin
  rw [is_trail_def, (c.rotate_edges h).perm.nodup_iff],
  exact hc.edges_nodup,
end

protected
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

protected
lemma is_cycle.rotate {u v : V} {c : G.walk v v} (hc : c.is_cycle) (h : u ∈ c.support) :
  (c.rotate h).is_cycle :=
begin
  refine ⟨hc.to_circuit.rotate _, _⟩,
  rw list.is_rotated.nodup_iff (support_rotate _ _),
  exact hc.support_nodup,
end

end walk_decomp

end walk

/-! ### Walks to paths -/

/-- The type for paths between two vertices. -/
abbreviation path (u v : V) := {p : G.walk u v // p.is_path}

namespace walk
variables {G} [decidable_eq V]

/-- Given a walk, produces a walk from it by bypassing subwalks between repeated vertices.
The result is a path, as shown in `simple_graph.walk.bypass_is_path`.
This is packaged up in `simple_graph.walk.to_path`. -/
def bypass : Π {u v : V}, G.walk u v → G.walk u v
| u v nil := nil
| u v (cons ha p) :=
  let p' := p.bypass
  in if hs : u ∈ p'.support
     then p'.drop_until u hs
     else cons ha p'

lemma bypass_is_path {u v : V} (p : G.walk u v) : p.bypass.is_path :=
begin
  induction p,
  { simp!, },
  { simp only [bypass],
    split_ifs,
    { apply is_path.drop_until,
      assumption, },
    { simp [*, cons_is_path_iff], } },
end

lemma length_bypass_le {u v : V} (p : G.walk u v) : p.bypass.length ≤ p.length :=
begin
  induction p,
  { refl },
  { simp only [bypass],
    split_ifs,
    { transitivity,
      apply length_drop_until_le,
      rw [length_cons],
      exact le_add_right p_ih, },
    { rw [length_cons, length_cons],
      exact add_le_add_right p_ih 1, } },
end

/-- Given a walk, produces a path with the same endpoints using `simple_graph.walk.bypass`. -/
def to_path {u v : V} (p : G.walk u v) : G.path u v := ⟨p.bypass, p.bypass_is_path⟩

lemma support_bypass_subset {u v : V} (p : G.walk u v) : p.bypass.support ⊆ p.support :=
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
support_bypass_subset _

lemma darts_bypass_subset {u v : V} (p : G.walk u v) : p.bypass.darts ⊆ p.darts :=
begin
  induction p,
  { simp!, },
  { simp! only,
    split_ifs,
    { apply list.subset.trans (darts_drop_until_subset _ _),
      apply list.subset_cons_of_subset _ p_ih, },
    { rw darts_cons,
      exact list.cons_subset_cons _ p_ih, }, },
end

lemma edges_bypass_subset {u v : V} (p : G.walk u v) : p.bypass.edges ⊆ p.edges :=
list.map_subset _ p.darts_bypass_subset

lemma darts_to_path_subset {u v : V} (p : G.walk u v) :
  (p.to_path : G.walk u v).darts ⊆ p.darts :=
darts_bypass_subset _

lemma edges_to_path_subset {u v : V} (p : G.walk u v) :
  (p.to_path : G.walk u v).edges ⊆ p.edges :=
edges_bypass_subset _

variables {G}

/-- Whether or not the path `p` is a prefix of the path `q`. -/
def prefix_of : Π {u v w : V} (p : G.walk u v) (q : G.walk u w), Prop
| u v w nil _ := true
| u v w (cons _ _) nil := false
| u v w (@cons _ _ _ x _ r p) (@cons _ _ _ y _ s q) :=
  if h : x = y
  then by { subst y, exact prefix_of p q }
  else false

end walk

namespace walk

/-- Given a walk that avoids an edge, create a walk in the subgraph with that edge deleted. -/
def walk_of_avoiding_walk {v w : V} (e : sym2 V) (p : G.walk v w) (hp : e ∉ p.edges) :
  (G.delete_edges {e}).walk v w :=
begin
  induction p,
  { refl },
  { simp only [walk.edges, list.mem_cons_iff, list.mem_map] at hp,
    push_neg at hp,
    sorry;
    apply walk.cons _ (p_ih hp.2);
    simp [*, hp.1.symm] }
end

section map
variables {G} {G' : simple_graph V'}

/-- Given a graph homomorphism, map walks to walks. -/
def map (f : G →g G') : Π {u v : V}, G.walk u v → G'.walk (f u) (f v)
| _ _ nil := nil
| _ _ (cons h p) := cons (f.map_adj h) (map p)

lemma map_append (f : G →g G') {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.append q).map f = (p.map f).append (q.map f) :=
begin
  induction p,
  { refl, },
  { simp [map, p_ih], },
end

@[simp]
lemma map_support_eq (f : G →g G') {u v : V} (p : G.walk u v) :
  (p.map f).support = p.support.map f :=
begin
  induction p,
  { refl, },
  { simp [map, p_ih], },
end

/-- Note: this is using the underlying map for `simple_graph.map_edge_set`. -/
@[simp]
lemma map_edges_eq (f : G →g G') {u v : V} (p : G.walk u v) :
  (p.map f).edges = p.edges.map (λ e, sym2.map f e) :=
begin
  induction p,
  { refl },
  { simp only [map, edges, p_ih],
    sorry }
end

end map

end walk

namespace path
variables {G} {G' : simple_graph V'}

@[simp] lemma coe_mk {u v : V} (p : G.walk u v) (h : p.is_path) : ↑(⟨p, h⟩ : G.path u v) = p := rfl

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

/-- Given an injective graph homomorphism, map paths to paths. -/
def map (f : G →g G') (hinj : function.injective f) {u v : V} (p : G.path u v) :
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

end path

/-! ## `reachable` and `connected` -/

/-- Two vertices are *reachable* if there is a walk between them.
This is equivalent to `relation.refl_trans_gen` of `G.adj`.
See `simple_graph.reachable_iff_refl_trans_gen`. -/
def reachable (u v : V) : Prop := nonempty (G.walk u v)

variables {G}

lemma reachable_iff_nonempty_univ {u v : V} :
  G.reachable u v ↔ (set.univ : set (G.walk u v)).nonempty :=
set.nonempty_iff_univ_nonempty

protected lemma reachable.elim {p : Prop} {u v : V}
  (h : G.reachable u v) (hp : G.walk u v → p) : p :=
nonempty.elim h hp

protected lemma reachable.elim_path {p : Prop} {u v : V}
  (h : G.reachable u v) (hp : G.path u v → p) : p :=
begin
  classical,
  exact h.elim (λ q, hp q.to_path),
end

@[refl] protected lemma reachable.refl {u : V} : G.reachable u u := by { fsplit, refl }

@[symm] protected lemma reachable.symm {u v : V} (huv : G.reachable u v) : G.reachable v u :=
huv.elim (λ p, ⟨p.reverse⟩)

@[trans] protected lemma reachable.trans {u v w : V}
  (huv : G.reachable u v) (hvw : G.reachable v w) :
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

/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `has_coe_to_fun` instance so that `h u v` can be used instead
of `h.preconnected u v`. -/
@[protect_proj]
structure connected : Prop :=
(preconnected : G.preconnected)
(nonempty : nonempty V)

/-- Gives the connected component containing a particular vertex. -/
def connected_component_of (v : V) : G.connected_component := quot.mk G.reachable v

instance connected_components.inhabited [inhabited V] : inhabited G.connected_component :=
⟨G.connected_component_of default⟩

lemma connected_component.subsingleton_of_connected (h : G.preconnected) :
  subsingleton G.connected_component :=
⟨λ c d, quot.ind (λ v d, quot.ind (λ w, quot.sound (h v w)) d) c d⟩

instance : has_coe_to_fun G.connected (λ _, Π (u v : V), G.reachable u v) :=
⟨λ h, h.preconnected⟩

/-- A subgraph is connected if it is connected as a simple graph. -/
abbreviation subgraph.connected {G : simple_graph V} (H : G.subgraph) : Prop := H.coe.connected

variables {G}

lemma preconnected.set_univ_walk_nonempty (hconn : G.preconnected) (u v : V) :
  (set.univ : set (G.walk u v)).nonempty :=
by { rw ← set.nonempty_iff_univ_nonempty, exact hconn u v }

lemma connected.set_univ_walk_nonempty (hconn : G.connected) (u v : V) :
  (set.univ : set (G.walk u v)).nonempty := hconn.preconnected.set_univ_walk_nonempty u v

variables (G)

/-- A graph is *k-edge-connected* if it remains connected whenever
fewer than k edges are removed. -/
def edge_connected (k : ℕ) : Prop :=
∀ (s : finset (sym2 V)), ↑s ⊆ G.edge_set → s.card < k → (G.delete_edges ↑s).connected

variables {G}

lemma edge_connected.to_preconnected {k : ℕ} (h : G.edge_connected k) (hk : 0 < k) :
  G.preconnected :=
begin
  intros v w,
  have h' := (h ∅ (by simp) (by simp [hk])).preconnected v w,
  simp only [finset.coe_empty, delete_edges_empty_eq] at h',
  exact h',
end

lemma edge_connected.to_connected {k : ℕ} (h : G.edge_connected k) (hk : 0 < k) : G.connected :=
let C' := h ∅ (by simp) (by simp [hk]) in
{ preconnected := by simpa using C'.preconnected,
  nonempty := C'.nonempty }

variables (G)

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

/-- An edge of a graph is a bridge if, after removing it, its incident vertices
are no longer reachable.

Characterizations of bridges:
`simple_graph.is_bridge_iff_walks_contain`
`is_bridge_iff_no_cycle_contains` -/
def is_bridge (v w : V) : Prop := ¬ (G.delete_edges {⟦(v, w)⟧}).reachable v w

lemma is_bridge_iff_walks_contain {v w : V} :
  G.is_bridge v w ↔ ∀ (p : G.walk v w), ⟦(v, w)⟧ ∈ p.edges :=
begin
  refine ⟨λ  hb p, _, _⟩,
  { by_contra he,
    exact hb ⟨p.walk_of_avoiding_walk _ _ he⟩ },
  { rintro hpe ⟨p'⟩,
    specialize hpe (p'.map (hom.map_spanning_subgraphs (G.delete_edges_le _))),
    simp only [set_coe.exists, walk.map_edges_eq, list.mem_map] at hpe,
    obtain ⟨z, he, hd⟩ := hpe,
    simp only [hom.map_spanning_subgraphs, rel_hom.coe_fn_mk] at hd,
    change sym2.map id z = _ at hd,
    simp only [id.def, sym2.map_id] at hd,
    subst z,
    have := p'.edges_subset_edge_set he,
    simpa using this }
end

variables [decidable_eq V]

lemma is_bridge_iff_no_cycle_contains.aux1
  {u v w : V}
  (c : G.walk u u)
  (he : ⟦(v, w)⟧ ∈ c.edges)
  (hb : ∀ (p : G.walk v w), ⟦(v, w)⟧ ∈ p.edges)
  (hc : c.is_trail)
  (hv : v ∈ c.support)
  (hw : w ∈ (c.take_until v hv).support) :
  false :=
begin
  let p1 := c.take_until v hv,
  let p2 := c.drop_until v hv,
  let p11 := p1.take_until w hw,
  let p12 := p1.drop_until w hw,
  have : (p11.append p12).append p2 = c := by simp,
  let q := p2.append p11,
  have hbq := hb (p2.append p11),
  have hpq' := hb p12.reverse,
  have this' : multiset.count ⟦(v, w)⟧ (p2.edges + p11.edges + p12.edges) = 1,
  { convert_to multiset.count ⟦(v, w)⟧ c.edges = _,
    congr,
    rw ←this,
    simp_rw [walk.edges_append, ←multiset.coe_add],
    rw [add_assoc ↑p11.edges, add_comm ↑p12.edges, ←add_assoc],
    congr' 1,
    rw add_comm,
    exact hc.count_edges_eq_one he },
  have this'' : multiset.count ⟦(v, w)⟧ (p2.append p11).edges
                  + multiset.count ⟦(v, w)⟧ p12.edges = 1,
  { convert this',
    rw walk.edges_append,
    symmetry,
    apply multiset.count_add },
  have hA : multiset.count ⟦(v, w)⟧ (p2.append p11).edges = 1,
  { apply walk.is_trail.count_edges_eq_one,
    have hr := hc.rotate hv,
    have : c.rotate hv = (p2.append p11).append p12,
    { simp [walk.rotate],
      rw ←walk.append_assoc,
      congr' 1,
      simp },
    rw this at hr,
    apply walk.is_trail.of_append_left hr,
    assumption },
  have hB : multiset.count ⟦(v, w)⟧ p12.edges = 1,
  { apply walk.is_trail.count_edges_eq_one,
    apply walk.is_trail.of_append_right,
    apply walk.is_trail.of_append_left,
    rw this,
    exact hc,
    simpa using hpq' },
  rw [hA, hB] at this'',
  simpa using this'',
end

lemma is_bridge_iff_no_cycle_contains {v w : V} (h : G.adj v w) :
  G.is_bridge v w ↔ ∀ {u : V} (p : G.walk u u), p.is_cycle → ⟦(v, w)⟧ ∉ p.edges :=
begin
  split,
  { intros hb u c hc he,
    rw is_bridge_iff_walks_contain at hb,
    have hv : v ∈ c.support := walk.mem_support_of_mem_edges c he,
    have hwc : w ∈ c.support := walk.mem_support_of_mem_edges c
                                (by { rw sym2.eq_swap, exact he }),
    let p1 := c.take_until v hv,
    let p2 := c.drop_until v hv,
    by_cases hw : w ∈ p1.support,
    { exact is_bridge_iff_no_cycle_contains.aux1 G c he hb hc.to_trail hv hw },
    { have hw' : w ∈ p2.support,
      { have : c = p1.append p2 := by simp,
        rw [this, walk.mem_support_append_iff] at hwc,
        cases hwc,
        { exact (hw hwc).elim },
        { exact hwc } },
      apply is_bridge_iff_no_cycle_contains.aux1 G (p2.append p1)
        (by { rw [walk.edges_append, list.mem_append, or_comm,
                  ←list.mem_append, ←walk.edges_append, walk.take_spec,
                  sym2.eq_swap],
              exact he })
        _ (hc.to_trail.rotate hv),
      swap,
      { rw walk.mem_support_append_iff,
        exact or.inl hw' },
      { simp },
      { intro p,
        specialize hb p.reverse,
        rw sym2.eq_swap,
        simpa using hb } } },
  { intro hc,
    rw is_bridge_iff_walks_contain,
    intro p,
    by_contra hne,
    specialize hc (walk.cons (G.symm h) p.to_path) _,
    { simp [walk.is_cycle_def, walk.cons_is_trail_iff],
      split,
      { intro h,
        apply hne,
        rw sym2.eq_swap at h,
        exact walk.edges_to_path_subset _ h },
      { exact p.to_path.property.2 } },
    simp [-quotient.eq] at hc,
    push_neg at hc,
    apply hc.1,
    rw sym2.eq_swap },
end

lemma is_acyclic_iff_all_bridges : G.is_acyclic ↔ ∀ {v w : V}, G.adj v w → G.is_bridge v w :=
begin
  split,
  { intros ha v w hvw,
    rw is_bridge_iff_no_cycle_contains _ hvw,
    intros u p hp,
    exact (ha _ p hp).elim },
  { intros hb v p hp,
    cases p,
    { simpa [walk.is_cycle_def] using hp },
    { specialize hb p_h,
      rw is_bridge_iff_no_cycle_contains _ p_h at hb,
      apply hb _ hp,
      rw [walk.edges_cons],
      apply list.mem_cons_self } },
end

lemma unique_path_if_is_acyclic (h : G.is_acyclic) {v w : V} (p q : G.path v w) : p = q :=
begin
  obtain ⟨p, hp⟩ := p,
  obtain ⟨q, hq⟩ := q,
  simp only,
  induction p generalizing q,
  { by_cases hnq : q = walk.nil,
    { subst q },
    { exfalso,
      cases q,
      exact (hnq rfl).elim,
      simpa [walk.is_path_def] using hq } },
  { rw is_acyclic_iff_all_bridges at h,
    specialize h p_h,
    rw is_bridge_iff_walks_contain at h,
    specialize h (q.append p_p.reverse),
    simp at h,
    cases h,
    { cases q,
      { exfalso,
        simpa [walk.is_path_def] using hp },
      { rw walk.cons_is_path_iff at hp hq,
        simp [walk.edges] at h,
        cases h,
        { cases h,
          { congr,
            exact p_ih hp.1 _ hq.1 },
          { exfalso,
            apply hq.2,
            simp } },
        { obtain ⟨a, ha, h⟩ := h,
          sorry -- some glue missing again?
          -- refine (hq.2 $ walk.mem_support_of_mem_edges _ _).elim,
           } } },
    { rw walk.cons_is_path_iff at hp,
      exact (hp.2 (walk.mem_support_of_mem_edges _ h)).elim } }
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
      assumption },
    specialize h _ _ ⟨c_p, hp⟩ (path.singleton (G.symm c_h)),
    simp [path.singleton] at h,
    subst c_p,
    simpa [walk.edges, -quotient.eq, sym2.eq_swap] using hc },
end

lemma is_acyclic_iff : G.is_acyclic ↔ ∀ (v w : V) (p q : G.path v w), p = q :=
begin
  split,
  { apply unique_path_if_is_acyclic },
  { apply is_acyclic_if_unique_path }
end

lemma is_tree_iff : G.is_tree ↔ nonempty V ∧ ∀ (v w : V), ∃!(p : G.walk v w), p.is_path :=
begin
  simp only [is_tree, is_acyclic_iff],
  split,
  { intro h,
    split,
    { cases h with h hne,
      simp [h.2] },
    intros v w,
    cases h with hc hu,
    let q := (hc.1 v w).some.to_path,
    use q,
    simp only [true_and, path.path_is_path],
    intros p hp,
    specialize hu v w ⟨p, hp⟩ q,
    rw ←hu,
    refl },
  { intro h,
    split,
    { split,
      intros v w,
      obtain ⟨p, hp⟩ := h.2 v w,
      use p,
      simp [h]},
    { rintros v w ⟨p, hp⟩ ⟨q, hq⟩,
      simp only,
      exact unique_of_exists_unique (h.2 v w) hp hq } },
end

/-- Get the unique path between two vertices in the tree. -/
noncomputable abbreviation tree_path (h : G.is_tree) (v w : V) : G.path v w :=
⟨((G.is_tree_iff.mp h).2 v w).some, ((G.is_tree_iff.mp h).2 v w).some_spec.1⟩

lemma tree_path_spec {h : G.is_tree} {v w : V} (p : G.path v w) : p = G.tree_path h v w :=
begin
  cases p,
  have := ((G.is_tree_iff.mp h).2 v w).some_spec,
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
  have hv := walk.mem_support_of_mem_edges _ hwv,
  have h' := h.2,
  rw is_acyclic_iff at h',
  specialize h' _ _
    (G.tree_path h v root)
    ⟨walk.drop_until _ _ hv, walk.is_path.drop_until _ (path.path_is_path _) _⟩,
  have hs := congr_arg (λ p, multiset.count w ↑(walk.support p)) (walk.take_spec _ hv),
  dsimp only at hs,
  rw h' at hvw,
  have hw := walk.mem_support_of_mem_edges _ hwv,
  rw walk.coe_support_append' at hs,
  have : multiset.count w {v} = 0,
  { simp only [multiset.singleton_eq_cons, multiset.count_eq_zero, multiset.mem_singleton],
    simpa using ne.symm hne },
  rw [multiset.count_sub, this, tsub_zero, multiset.count_add] at hs,
  simp_rw [multiset.coe_count] at hs,
  rw [path.support_count_eq_one] at hs,
  swap, { simp },
  rw ←path.coe_mk (walk.take_until _ _ _) at hs,
  swap, { apply walk.is_path.take_until, apply path.path_is_path },
  rw ←path.coe_mk (walk.drop_until _ _ _) at hs,
  swap, { apply walk.is_path.drop_until, apply path.path_is_path },
  rw [path.support_count_eq_one, path.support_count_eq_one] at hs,
  simpa using hs,
  apply walk.mem_support_of_mem_edges _ (by { rw [sym2.eq_swap], exact hvw }),
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
  specialize hrw (G.symm hvw),
  let p := (G.tree_path h v root : G.walk v root).append
           (G.tree_path h w root : G.walk w root).reverse,
  specialize h' _ _ (path.singleton hvw) p.to_path,
  have hp := walk.edges_to_path_subset p,
  rw [←h', walk.edges_append, walk.edges_reverse] at hp,
  specialize hp (path.singleton_edge_mem hvw),
  rw [list.mem_append, list.mem_reverse] at hp,
  rw sym2.eq_swap at hrw,
  cases hp; simpa only [hrv, hrw] using hp,
end

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
  { exact h },
  { cases hp,
    simpa using hp_support_nodup },
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
    { obtain (⟨_,rfl⟩|⟨rfl,rfl⟩) := h; refl },
    { have h := walk.mem_support_of_mem_edges _ h,
      exact (hp_support_nodup.1 h).elim } },
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

lemma is_tree.card_edges_eq_card_vertices_sub_one
  [fintype G.edge_set] [fintype V] [nonempty V] (h : G.is_tree) :
  card G.edge_set = card V - 1 :=
begin
  have root := classical.arbitrary V,
  rw ←set.card_ne_eq root,
  let f : {v | v ≠ root} → G.edge_set := λ v,
    ⟨G.next_edge v root v.property (G.tree_path h v root),
     G.incidence_set_subset _ (subtype.mem _)⟩,
  have finj : function.injective f,
  { rintros ⟨u₁, h₁⟩ ⟨u₂, h₂⟩,
    by_cases hne : u₁ = u₂,
    { subst u₂,
      simp },
    simp only [subtype.mk_eq_mk, subtype.coe_mk],
    generalize he₁ : G.next_edge _ _ _ _ = e₁,
    generalize he₂ : G.next_edge _ _ _ _ = e₂,
    cases e₁ with e₁ heu₁,
    cases e₂ with e₂ heu₂,
    simp only [subtype.coe_mk],
    rintro rfl,
    cases heu₁ with heu₁_edge heu₁_adj,
    cases heu₂ with heu₂_edge heu₂_adj,
    simp only [subtype.coe_mk] at heu₁_adj heu₂_adj,
    have e_is : e₁ = ⟦(u₁, u₂)⟧,
    { induction e₁ using quotient.ind,
      cases e₁ with v₁ w₁,
      simp only [sym2.mem_iff] at heu₁_adj heu₂_adj,
      obtain (rfl|rfl) := heu₁_adj;
      obtain (rfl|rfl) := heu₂_adj;
      try { exact (hne rfl).elim };
      simp [sym2.eq_swap] },
    subst e₁,
    apply is_rootward_antisymm h root,
    { split,
      exact heu₂_edge,
      convert G.next_edge_mem_edges _ _ h₁ _,
      erw he₁, refl },
    { split,
      exact G.symm heu₂_edge,
      convert G.next_edge_mem_edges _ _ h₂ _,
      erw he₂, simp [sym2.eq_swap] } },
  have fsurj : function.surjective f,
  { intro e,
    cases e with e he,
    induction e using quotient.ind,
    cases e with u₁ u₂,
    cases is_rootward_or_reverse h root he with hr hr,
    { use u₁,
      rintro rfl,
      dsimp only [is_rootward] at hr,
      exact nonempty_path_not_loop _ hr.2,
      cases hr,
      simp only [f],
      erw eq_next_edge_if_mem_path _ ⟨he, _⟩ _ hr_right; simp [he]},
    { use u₂,
      rintro rfl,
      dsimp only [is_rootward] at hr,
      exact nonempty_path_not_loop _ hr.2,
      cases hr,
      simp only [f],
      erw eq_next_edge_if_mem_path _ ⟨_ , _⟩ _ hr_right; simp [he, sym2.eq_swap] } },
  exact (card_of_bijective ⟨finj, fsurj⟩).symm,
end

end simple_graph
