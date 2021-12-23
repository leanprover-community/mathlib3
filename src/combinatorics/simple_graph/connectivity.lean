/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.basic
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

lemma support_ne_nil {u v : V} (p : G.walk u v) : p.support ≠ [] :=
by cases p; simp

lemma support_eq {u v : V} (p : G.walk u v) : p.support = u :: p.support.tail :=
by cases p; simp

@[simp] lemma start_mem_support {u v : V} (p : G.walk u v) : u ∈ p.support :=
by cases p; simp

@[simp] lemma end_mem_support {u v : V} (p : G.walk u v) : v ∈ p.support :=
by induction p; simp [*]

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

@[simp] lemma length_support {u v : V} (p : G.walk u v) : p.support.length = p.length + 1 :=
by induction p; simp *

@[simp] lemma length_edges {u v : V} (p : G.walk u v) : p.edges.length = p.length :=
by induction p; simp *

lemma mem_support_of_mem_edges : Π {t u v w : V} (p : G.walk v w)
  (he : ⟦(t, u)⟧ ∈ p.edges),
  t ∈ p.support
| t u v w (cons h p') he := begin
  simp only [support_cons, edges_cons, list.mem_cons_iff, quotient.eq] at he ⊢,
  rcases he with ((he|he)|he),
  { exact or.inl rfl },
  { exact or.inr (start_mem_support _) },
  { exact or.inr (mem_support_of_mem_edges _ he), }
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

lemma is_path_def {u v : V} (p : G.walk u v) :
  p.is_path ↔ is_trail p ∧ p.support.nodup :=
by split; { rintro ⟨h1, h2⟩, exact ⟨h1, h2⟩ }

lemma is_cycle_def [decidable_eq V] {u : V} (p : G.walk u u) :
  p.is_cycle ↔ is_trail p ∧ p ≠ nil ∧ p.support.tail.nodup :=
iff.intro (λ h, ⟨h.1.1, h.1.2, h.2⟩) (λ h, ⟨⟨h.1, h.2.1⟩, h.2.2⟩)

lemma count_edges_le_one_of_trail [decidable_eq V] {u v : V}
  (p : G.walk u v) (h : p.is_trail) (e : sym2 V) : p.edges.count e ≤ 1 :=
list.nodup_iff_count_le_one.mp h e

lemma count_edges_eq_one_of_trail [decidable_eq V] {u v : V}
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
  { rw [support_cons, list.nodup_cons] at hd,
    exact hd.2, },
end

@[simp] lemma cons_is_trail_iff {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).is_trail ↔ p.is_trail ∧ ⟦(u, v)⟧ ∉ p.edges :=
by simp [is_trail, and_comm]

@[simp] lemma cons_is_path_iff {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).is_path ↔ p.is_path ∧ u ∉ p.support :=
begin
  simp only [is_path_def, cons_is_trail_iff, support_cons, list.nodup_cons],
  split,
  { rintro ⟨⟨ht, hne⟩, hns, hsn⟩,
    exact ⟨⟨ht, hsn⟩, hns⟩, },
  { rintro ⟨⟨ht, hsn⟩, hns⟩,
    simp only [ht, hsn, hns, and_true, not_false_iff, true_and],
    intro he,
    exact hns (mem_support_of_mem_edges p he), },
end

end walk

end simple_graph
