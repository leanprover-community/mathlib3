/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import data.list.rotate
/-!

# Graph connectivity

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

* `simple_graph.walk.map` and `simple_graph.path.map` for the induced map on walks,
  given an (injective) graph homomorphism.

* `simple_graph.reachable` for the relation of whether there exists
  a walk between a given pair of vertices

* `simple_graph.preconnected` and `simple_graph.connected` are predicates
  on simple graphs for whether every vertex can be reached from every other,
  and in the latter case, whether the vertex type is nonempty.

* `simple_graph.subgraph.connected` gives subgraphs the connectivity
  predicate via `simple_graph.subgraph.coe`.

* `simple_graph.connected_component` is the type of connected components of
  a given graph.

* `simple_graph.is_bridge` for whether an edge is a bridge edge

## Main statements

* `simple_graph.is_bridge_iff_mem_and_forall_cycle_not_mem` characterizes bridge edges in terms of
  there being no cycle containing them.

## Tags
walks, trails, paths, circuits, cycles, bridge edges

-/

open function

universes u v w

namespace simple_graph
variables {V : Type u} {V' : Type v} {V'' : Type w}
variables (G : simple_graph V) (G' : simple_graph V') (G'' : simple_graph V'')

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

@[simps] instance walk.inhabited (v : V) : inhabited (G.walk v v) := ⟨walk.nil⟩

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[pattern, reducible] def adj.to_walk {G : simple_graph V} {u v : V} (h : G.adj u v) :
  G.walk u v := walk.cons h walk.nil

namespace walk
variables {G}

/-- Pattern to get `walk.nil` with the vertex as an explicit argument. -/
@[pattern] abbreviation nil' (u : V) : G.walk u u := walk.nil

/-- Pattern to get `walk.cons` with the vertices as explicit arguments. -/
@[pattern] abbreviation cons' (u v w : V) (h : G.adj u v) (p : G.walk v w) : G.walk u w :=
walk.cons h p

/-- Change the endpoints of a walk using equalities. This is helpful for relaxing
definitional equality constraints and to be able to state otherwise difficult-to-state
lemmas. While this is a simple wrapper around `eq.rec`, it gives a canonical way to write it.

The simp-normal form is for the `copy` to be pushed outward. That way calculations can
occur within the "copy context." -/
protected def copy {u v u' v'} (p : G.walk u v) (hu : u = u') (hv : v = v') : G.walk u' v' :=
eq.rec (eq.rec p hv) hu

@[simp] lemma copy_rfl_rfl {u v} (p : G.walk u v) :
  p.copy rfl rfl = p := rfl

@[simp] lemma copy_copy {u v u' v' u'' v''} (p : G.walk u v)
  (hu : u = u') (hv : v = v') (hu' : u' = u'') (hv' : v' = v'') :
  (p.copy hu hv).copy hu' hv' = p.copy (hu.trans hu') (hv.trans hv') :=
by { subst_vars, refl }

@[simp] lemma copy_nil {u u'} (hu : u = u') : (walk.nil : G.walk u u).copy hu hu = walk.nil :=
by { subst_vars, refl }

lemma copy_cons {u v w u' w'} (h : G.adj u v) (p : G.walk v w) (hu : u = u') (hw : w = w') :
  (walk.cons h p).copy hu hw = walk.cons (by rwa ← hu) (p.copy rfl hw) :=
by { subst_vars, refl }

@[simp]
lemma cons_copy {u v w v' w'} (h : G.adj u v) (p : G.walk v' w') (hv : v' = v) (hw : w' = w) :
  walk.cons h (p.copy hv hw) = (walk.cons (by rwa hv) p).copy rfl hw :=
by { subst_vars, refl }

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

/-- The reversed version of `simple_graph.walk.cons`, concatenating an edge to
the end of a walk. -/
def concat {u v w : V} (p : G.walk u v) (h : G.adj v w) : G.walk u w := p.append (cons h nil)

lemma concat_eq_append {u v w : V} (p : G.walk u v) (h : G.adj v w) :
  p.concat h = p.append (cons h nil) := rfl

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

@[simp] lemma append_copy_copy {u v w u' v' w'} (p : G.walk u v) (q : G.walk v w)
  (hu : u = u') (hv : v = v') (hw : w = w') :
  (p.copy hu hv).append (q.copy hv hw) = (p.append q).copy hu hw := by { subst_vars, refl }

lemma concat_nil {u v : V} (h : G.adj u v) : nil.concat h = cons h nil := rfl

@[simp] lemma concat_cons {u v w x : V} (h : G.adj u v) (p : G.walk v w) (h' : G.adj w x) :
  (cons h p).concat h' = cons h (p.concat h') := rfl

lemma append_concat {u v w x : V} (p : G.walk u v) (q : G.walk v w) (h : G.adj w x) :
  p.append (q.concat h) = (p.append q).concat h := append_assoc _ _ _

lemma concat_append {u v w x : V} (p : G.walk u v) (h : G.adj v w) (q : G.walk w x) :
  (p.concat h).append q = p.append (cons h q) :=
by rw [concat_eq_append, ← append_assoc, cons_nil_append]

/-- A non-trivial `cons` walk is representable as a `concat` walk. -/
lemma exists_cons_eq_concat : Π {u v w : V} (h : G.adj u v) (p : G.walk v w),
  ∃ (x : V) (q : G.walk u x) (h' : G.adj x w), cons h p = q.concat h'
| _ _ _ h nil := ⟨_, nil, h, rfl⟩
| _ _ _ h (cons h' p) :=
  begin
    obtain ⟨y, q, h'', hc⟩ := exists_cons_eq_concat h' p,
    refine ⟨y, cons h q, h'', _⟩,
    rw [concat_cons, hc],
  end

/-- A non-trivial `concat` walk is representable as a `cons` walk. -/
lemma exists_concat_eq_cons : Π {u v w : V} (p : G.walk u v) (h : G.adj v w),
  ∃ (x : V) (h' : G.adj u x) (q : G.walk x w), p.concat h = cons h' q
| _ _ _ nil h := ⟨_, h, nil, rfl⟩
| _ _ _ (cons h' p) h := ⟨_, h', walk.concat p h, concat_cons _ _ _⟩

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

@[simp] lemma reverse_copy {u v u' v'} (p : G.walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).reverse = p.reverse.copy hv hu := by { subst_vars, refl }

@[simp] lemma reverse_append {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.append q).reverse = q.reverse.append p.reverse :=
by simp [reverse]

@[simp] lemma reverse_concat {u v w : V} (p : G.walk u v) (h : G.adj v w) :
  (p.concat h).reverse = cons (G.symm h) p.reverse :=
by simp [concat_eq_append]

@[simp] lemma reverse_reverse : Π {u v : V} (p : G.walk u v), p.reverse.reverse = p
| _ _ nil := rfl
| _ _ (cons h p) := by simp [reverse_reverse]

@[simp] lemma length_nil {u : V} : (nil : G.walk u u).length = 0 := rfl

@[simp] lemma length_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).length = p.length + 1 := rfl

@[simp] lemma length_copy {u v u' v'} (p : G.walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).length = p.length :=
by { subst_vars, refl }

@[simp] lemma length_append : Π {u v w : V} (p : G.walk u v) (q : G.walk v w),
  (p.append q).length = p.length + q.length
| _ _ _ nil _ := by simp
| _ _ _ (cons _ _) _ := by simp [length_append, add_left_comm, add_comm]

@[simp] lemma length_concat {u v w : V} (p : G.walk u v) (h : G.adj v w) :
  (p.concat h).length = p.length + 1 := length_append _ _

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

@[simp] lemma length_eq_zero_iff {u : V} {p : G.walk u u} : p.length = 0 ↔ p = nil :=
by cases p; simp

section concat_rec

variables
  {motive : Π (u v : V), G.walk u v → Sort*}
  (Hnil : Π {u : V}, motive u u nil)
  (Hconcat : Π {u v w : V} (p : G.walk u v) (h : G.adj v w), motive u v p → motive u w (p.concat h))

/-- Auxiliary definition for `simple_graph.walk.concat_rec` -/
def concat_rec_aux : Π {u v : V} (p : G.walk u v), motive v u p.reverse
| _ _ nil := Hnil
| _ _ (cons h p) := eq.rec (Hconcat p.reverse (G.symm h) (concat_rec_aux p)) (reverse_cons h p).symm

/-- Recursor on walks by inducting on `simple_graph.walk.concat`.

This is inducting from the opposite end of the walk compared
to `simple_graph.walk.rec`, which inducts on `simple_graph.walk.cons`. -/
@[elab_as_eliminator]
def concat_rec {u v : V} (p : G.walk u v) : motive u v p :=
eq.rec (concat_rec_aux @Hnil @Hconcat p.reverse) (reverse_reverse p)

@[simp] lemma concat_rec_nil (u : V) :
  @concat_rec _ _ motive @Hnil @Hconcat _ _ (nil : G.walk u u) = Hnil := rfl

@[simp] lemma concat_rec_concat {u v w : V} (p : G.walk u v) (h : G.adj v w) :
  @concat_rec _ _ motive @Hnil @Hconcat _ _ (p.concat h)
  = Hconcat p h (concat_rec @Hnil @Hconcat p) :=
begin
  simp only [concat_rec],
  apply eq_of_heq,
  apply rec_heq_of_heq,
  transitivity concat_rec_aux @Hnil @Hconcat (cons h.symm p.reverse),
  { congr, simp },
  { rw [concat_rec_aux, rec_heq_iff_heq],
    congr; simp [heq_rec_iff_heq], }
end

end concat_rec

lemma concat_ne_nil {u v : V} (p : G.walk u v) (h : G.adj v u) :
  p.concat h ≠ nil :=
by cases p; simp [concat]

lemma concat_inj {u v v' w : V}
  {p : G.walk u v} {h : G.adj v w} {p' : G.walk u v'} {h' : G.adj v' w}
  (he : p.concat h = p'.concat h') :
  ∃ (hv : v = v'), p.copy rfl hv = p' :=
begin
  induction p,
  { cases p',
    { exact ⟨rfl, rfl⟩ },
    { exfalso,
      simp only [concat_nil, concat_cons] at he,
      obtain ⟨rfl, he⟩ := he,
      simp only [heq_iff_eq] at he,
      exact concat_ne_nil _ _ he.symm, } },
  { rw concat_cons at he,
    cases p',
    { exfalso,
      simp only [concat_nil] at he,
      obtain ⟨rfl, he⟩ := he,
      rw [heq_iff_eq] at he,
      exact concat_ne_nil _ _ he, },
    { rw concat_cons at he,
      simp only at he,
      obtain ⟨rfl, he⟩ := he,
      rw [heq_iff_eq] at he,
      obtain ⟨rfl, rfl⟩ := p_ih he,
      exact ⟨rfl, rfl⟩, } }
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

@[simp] lemma support_concat {u v w : V} (p : G.walk u v) (h : G.adj v w) :
  (p.concat h).support = p.support.concat w := by induction p; simp [*, concat_nil]

@[simp] lemma support_copy {u v u' v'} (p : G.walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).support = p.support := by { subst_vars, refl }

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

@[simp] lemma support_nonempty {u v : V} (p : G.walk u v) : {w | w ∈ p.support}.nonempty :=
⟨u, by simp⟩

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

@[simp]
lemma subset_support_append_left {V : Type u} {G : simple_graph V} {u v w : V}
  (p : G.walk u v) (q : G.walk v w) :
  p.support ⊆ (p.append q).support :=
by simp only [walk.support_append, list.subset_append_left]

@[simp]
lemma subset_support_append_right {V : Type u} {G : simple_graph V} {u v w : V}
  (p : G.walk u v) (q : G.walk v w) :
  q.support ⊆ (p.append q).support :=
by { intro h, simp only [mem_support_append_iff, or_true, implies_true_iff] { contextual := tt }}

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

lemma adj_of_mem_edges {u v x y : V} (p : G.walk u v) (h : ⟦(x, y)⟧ ∈ p.edges) : G.adj x y :=
edges_subset_edge_set p h

@[simp] lemma darts_nil {u : V} : (nil : G.walk u u).darts = [] := rfl

@[simp] lemma darts_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).darts = ⟨(u, v), h⟩ :: p.darts := rfl

@[simp] lemma darts_concat {u v w : V} (p : G.walk u v) (h : G.adj v w) :
  (p.concat h).darts = p.darts.concat ⟨(v, w), h⟩ := by induction p; simp [*, concat_nil]

@[simp] lemma darts_copy {u v u' v'} (p : G.walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).darts = p.darts := by { subst_vars, refl }

@[simp] lemma darts_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  (p.append p').darts = p.darts ++ p'.darts :=
by induction p; simp [*]

@[simp] lemma darts_reverse {u v : V} (p : G.walk u v) :
  p.reverse.darts = (p.darts.map dart.symm).reverse :=
by induction p; simp [*, sym2.eq_swap]

lemma mem_darts_reverse {u v : V} {d : G.dart} {p : G.walk u v} :
  d ∈ p.reverse.darts ↔ d.symm ∈ p.darts :=
by simp

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

@[simp] lemma edges_concat {u v w : V} (p : G.walk u v) (h : G.adj v w) :
  (p.concat h).edges = p.edges.concat ⟦(v, w)⟧ := by simp [edges]

@[simp] lemma edges_copy {u v u' v'} (p : G.walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).edges = p.edges := by { subst_vars, refl }

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

lemma dart_snd_mem_support_of_mem_darts {u v : V} (p : G.walk u v) {d : G.dart} (h : d ∈ p.darts) :
  d.snd ∈ p.support :=
by simpa using p.reverse.dart_fst_mem_support_of_mem_darts (by simp [h] : d.symm ∈ p.reverse.darts)

lemma fst_mem_support_of_mem_edges {t u v w : V} (p : G.walk v w) (he : ⟦(t, u)⟧ ∈ p.edges) :
  t ∈ p.support :=
begin
  obtain ⟨d, hd, he⟩ := list.mem_map.mp he,
  rw dart_edge_eq_mk_iff' at he,
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
  { exact dart_fst_mem_support_of_mem_darts _ hd, },
  { exact dart_snd_mem_support_of_mem_darts _ hd, },
end

lemma snd_mem_support_of_mem_edges {t u v w : V} (p : G.walk v w) (he : ⟦(t, u)⟧ ∈ p.edges) :
  u ∈ p.support :=
by { rw sym2.eq_swap at he, exact p.fst_mem_support_of_mem_edges he }

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
    exact ⟨λ h', h.1 (fst_mem_support_of_mem_edges p_p h'), p_ih h.2⟩, }
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

@[simp] lemma is_trail_copy {u v u' v'} (p : G.walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).is_trail ↔ p.is_trail := by { subst_vars, refl }

lemma is_path.mk' {u v : V} {p : G.walk u v} (h : p.support.nodup) : is_path p :=
⟨⟨edges_nodup_of_support_nodup h⟩, h⟩

lemma is_path_def {u v : V} (p : G.walk u v) : p.is_path ↔ p.support.nodup :=
⟨is_path.support_nodup, is_path.mk'⟩

@[simp] lemma is_path_copy {u v u' v'} (p : G.walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).is_path ↔ p.is_path := by { subst_vars, refl }

lemma is_circuit_def {u : V} (p : G.walk u u) :
  p.is_circuit ↔ is_trail p ∧ p ≠ nil :=
iff.intro (λ h, ⟨h.1, h.2⟩) (λ h, ⟨h.1, h.2⟩)

@[simp] lemma is_circuit_copy {u u'} (p : G.walk u u) (hu : u = u') :
  (p.copy hu hu).is_circuit ↔ p.is_circuit := by { subst_vars, refl }

lemma is_cycle_def {u : V} (p : G.walk u u) :
  p.is_cycle ↔ is_trail p ∧ p ≠ nil ∧ p.support.tail.nodup :=
iff.intro (λ h, ⟨h.1.1, h.1.2, h.2⟩) (λ h, ⟨⟨h.1, h.2.1⟩, h.2.2⟩)

@[simp] lemma is_cycle_copy {u u'} (p : G.walk u u) (hu : u = u') :
  (p.copy hu hu).is_cycle ↔ p.is_cycle := by { subst_vars, refl }

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

lemma is_path.nil {u : V} : (nil : G.walk u u).is_path :=
by { fsplit; simp }

lemma is_path.of_cons {u v w : V} {h : G.adj u v} {p : G.walk v w} :
  (cons h p).is_path → p.is_path :=
by simp [is_path_def]

@[simp] lemma cons_is_path_iff {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).is_path ↔ p.is_path ∧ u ∉ p.support :=
by split; simp [is_path_def] { contextual := tt }

@[simp] lemma is_path_iff_eq_nil {u : V} (p : G.walk u u) : p.is_path ↔ p = nil :=
by { cases p; simp [is_path.nil] }

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

@[simp] lemma is_cycle.not_of_nil {u : V} : ¬ (nil : G.walk u u).is_cycle :=
λ h, h.ne_nil rfl

lemma cons_is_cycle_iff {u v : V} (p : G.walk v u) (h : G.adj u v) :
  (walk.cons h p).is_cycle ↔ p.is_path ∧ ¬ ⟦(u, v)⟧ ∈ p.edges :=
begin
  simp only [walk.is_cycle_def, walk.is_path_def, walk.is_trail_def, edges_cons, list.nodup_cons,
             support_cons, list.tail_cons],
  have : p.support.nodup → p.edges.nodup := edges_nodup_of_support_nodup,
  tauto,
end

/-! ### About paths -/

instance [decidable_eq V] {u v : V} (p : G.walk u v) : decidable p.is_path :=
by { rw is_path_def, apply_instance }

lemma is_path.length_lt [fintype V] {u v : V} {p : G.walk u v} (hp : p.is_path) :
  p.length < fintype.card V :=
by { rw [nat.lt_iff_add_one_le, ← length_support], exact hp.support_nodup.length_le_card }

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

lemma mem_support_iff_exists_append {V : Type u} {G : simple_graph V} {u v w : V}
  {p : G.walk u v} :
  w ∈ p.support ↔ ∃ (q : G.walk u w) (r : G.walk w v), p = q.append r :=
begin
  classical,
  split,
  { exact λ h, ⟨_, _, (p.take_spec h).symm⟩ },
  { rintro ⟨q, r, rfl⟩,
    simp only [mem_support_append_iff, end_mem_support, start_mem_support, or_self], },
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

@[simp] lemma take_until_copy {u v w v' w'} (p : G.walk v w)
  (hv : v = v') (hw : w = w') (h : u ∈ (p.copy hv hw).support) :
  (p.copy hv hw).take_until u h = (p.take_until u (by { subst_vars, exact h })).copy hv rfl :=
by { subst_vars, refl }

@[simp] lemma drop_until_copy {u v w v' w'} (p : G.walk v w)
  (hv : v = v') (hw : w = w') (h : u ∈ (p.copy hv hw).support) :
  (p.copy hv hw).drop_until u h = (p.drop_until u (by { subst_vars, exact h })).copy rfl hw :=
by { subst_vars, refl }

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

/--
Given a set `S` and a walk `w` from `u` to `v` such that `u ∈ S` but `v ∉ S`,
there exists a dart in the walk whose start is in `S` but whose end is not.
-/
lemma exists_boundary_dart
  {u v : V} (p : G.walk u v) (S : set V) (uS : u ∈ S) (vS : v ∉ S) :
  ∃ (d : G.dart), d ∈ p.darts ∧ d.fst ∈ S ∧ d.snd ∉ S :=
begin
  induction p with _ x y w a p' ih,
  { exact absurd uS vS },
  { by_cases h : y ∈ S,
    { obtain ⟨d, hd, hcd⟩ := ih h vS,
      exact ⟨d, or.inr hd, hcd⟩ },
    { exact ⟨⟨(x, y), a⟩, or.inl rfl, uS, h⟩ } }
end


end walk

/-! ### Type of paths -/

/-- The type for paths between two vertices. -/
abbreviation path (u v : V) := {p : G.walk u v // p.is_path}

namespace path
variables {G G'}

@[simp] protected lemma is_path {u v : V} (p : G.path u v) : (p : G.walk u v).is_path :=
p.property

@[simp] protected lemma is_trail {u v : V} (p : G.path u v) : (p : G.walk u v).is_trail :=
p.property.to_trail

/-- The length-0 path at a vertex. -/
@[refl, simps] protected def nil {u : V} : G.path u u := ⟨walk.nil, walk.is_path.nil⟩

/-- The length-1 path between a pair of adjacent vertices. -/
@[simps] def singleton {u v : V} (h : G.adj u v) : G.path u v :=
⟨walk.cons h walk.nil, by simp [h.ne]⟩

lemma mk_mem_edges_singleton {u v : V} (h : G.adj u v) :
  ⟦(u, v)⟧ ∈ (singleton h : G.walk u v).edges := by simp [singleton]

/-- The reverse of a path is another path.  See also `simple_graph.walk.reverse`. -/
@[symm, simps] def reverse {u v : V} (p : G.path u v) : G.path v u :=
⟨walk.reverse p, p.property.reverse⟩

lemma count_support_eq_one [decidable_eq V] {u v w : V} {p : G.path u v}
  (hw : w ∈ (p : G.walk u v).support) : (p : G.walk u v).support.count w = 1 :=
list.count_eq_one_of_mem p.property.support_nodup hw

lemma count_edges_eq_one [decidable_eq V] {u v : V} {p : G.path u v} (e : sym2 V)
  (hw : e ∈ (p : G.walk u v).edges) : (p : G.walk u v).edges.count e = 1 :=
list.count_eq_one_of_mem p.property.to_trail.edges_nodup hw

@[simp] lemma nodup_support {u v : V} (p : G.path u v) : (p : G.walk u v).support.nodup :=
(walk.is_path_def _).mp p.property

lemma loop_eq {v : V} (p : G.path v v) : p = path.nil :=
begin
  obtain ⟨_|_, this⟩ := p,
  { refl },
  { simpa },
end

lemma not_mem_edges_of_loop {v : V} {e : sym2 V} {p : G.path v v} :
  ¬ e ∈ (p : G.walk v v).edges :=
by simp [p.loop_eq]

lemma cons_is_cycle {u v : V} (p : G.path v u) (h : G.adj u v)
  (he : ¬ ⟦(u, v)⟧ ∈ (p : G.walk v u).edges) : (walk.cons h ↑p).is_cycle :=
by simp [walk.is_cycle_def, walk.cons_is_trail_iff, he]

end path

/-! ### Walks to paths -/

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

@[simp] lemma bypass_copy {u v u' v'} (p : G.walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).bypass = p.bypass.copy hu hv := by { subst_vars, refl }

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

end walk

/-! ### Mapping paths -/

namespace walk
variables {G G' G''}

/-- Given a graph homomorphism, map walks to walks. -/
protected def map (f : G →g G') : Π {u v : V}, G.walk u v → G'.walk (f u) (f v)
| _ _ nil := nil
| _ _ (cons h p) := cons (f.map_adj h) (map p)

variables (f : G →g G') (f' : G' →g G'') {u v u' v' : V} (p : G.walk u v)

@[simp] lemma map_nil : (nil : G.walk u u).map f = nil := rfl

@[simp] lemma map_cons {w : V} (h : G.adj w u) :
  (cons h p).map f = cons (f.map_adj h) (p.map f) := rfl

@[simp] lemma map_copy (hu : u = u') (hv : v = v') :
  (p.copy hu hv).map f = (p.map f).copy (by rw hu) (by rw hv) := by { subst_vars, refl }

@[simp] lemma map_id (p : G.walk u v) : p.map hom.id = p := by { induction p; simp [*] }

@[simp] lemma map_map : (p.map f).map f' = p.map (f'.comp f) := by { induction p; simp [*] }

/-- Unlike categories, for graphs vertex equality is an important notion, so needing to be able to
to work with equality of graph homomorphisms is a necessary evil. -/
lemma map_eq_of_eq {f : G →g G'} (f' : G →g G') (h : f = f') :
  p.map f = (p.map f').copy (by rw h) (by rw h) := by { subst_vars, refl }

@[simp] lemma map_eq_nil_iff {p : G.walk u u} : p.map f = nil ↔ p = nil :=
by cases p; simp

@[simp] lemma length_map : (p.map f).length = p.length :=
by induction p; simp [*]

lemma map_append {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.append q).map f = (p.map f).append (q.map f) :=
by induction p; simp [*]

@[simp] lemma reverse_map : (p.map f).reverse = p.reverse.map f :=
by induction p; simp [map_append, *]

@[simp] lemma support_map : (p.map f).support = p.support.map f :=
by induction p; simp [*]

@[simp] lemma darts_map : (p.map f).darts = p.darts.map f.map_dart :=
by induction p; simp [*]

@[simp] lemma edges_map : (p.map f).edges = p.edges.map (sym2.map f) :=
by induction p; simp [*]

variables {p f}

lemma map_is_path_of_injective (hinj : function.injective f) (hp : p.is_path) :
  (p.map f).is_path :=
begin
  induction p with w u v w huv hvw ih,
  { simp, },
  { rw walk.cons_is_path_iff at hp,
    simp [ih hp.1],
    intros x hx hf,
    cases hinj hf,
    exact hp.2 hx, },
end

protected lemma is_path.of_map {f : G →g G'} (hp : (p.map f).is_path) : p.is_path :=
begin
  induction p with w u v w huv hvw ih,
  { simp },
  { rw [map_cons, walk.cons_is_path_iff, support_map] at hp,
    rw walk.cons_is_path_iff,
    cases hp with hp1 hp2,
    refine ⟨ih hp1, _⟩,
    contrapose! hp2,
    exact list.mem_map_of_mem f hp2, }
end

lemma map_is_path_iff_of_injective (hinj : function.injective f) :
  (p.map f).is_path ↔ p.is_path :=
⟨is_path.of_map, map_is_path_of_injective hinj⟩

lemma map_is_trail_iff_of_injective (hinj : function.injective f) :
  (p.map f).is_trail ↔ p.is_trail :=
begin
  induction p with w u v w huv hvw ih,
  { simp },
  { rw [map_cons, cons_is_trail_iff, cons_is_trail_iff, edges_map],
    change _ ∧ sym2.map f ⟦(u, v)⟧ ∉ _ ↔ _,
    rw list.mem_map_of_injective (sym2.map.injective hinj),
    exact and_congr_left' ih, },
end

alias map_is_trail_iff_of_injective ↔ _ map_is_trail_of_injective

lemma map_is_cycle_iff_of_injective {p : G.walk u u} (hinj : function.injective f) :
  (p.map f).is_cycle ↔ p.is_cycle :=
by rw [is_cycle_def, is_cycle_def, map_is_trail_iff_of_injective hinj, ne.def, map_eq_nil_iff,
       support_map, ← list.map_tail, list.nodup_map_iff hinj]

alias map_is_cycle_iff_of_injective ↔ _ map_is_cycle_of_injective

variables (p f)

lemma map_injective_of_injective {f : G →g G'} (hinj : function.injective f) (u v : V) :
  function.injective (walk.map f : G.walk u v → G'.walk (f u) (f v)) :=
begin
  intros p p' h,
  induction p with _ _ _ _ _ _ ih generalizing p',
  { cases p',
    { refl },
    simpa using h, },
  { induction p',
    { simpa using h, },
    { simp only [map_cons] at h,
      cases hinj h.1,
      simp only [eq_self_iff_true, heq_iff_eq, true_and],
      apply ih,
      simpa using h.2, } },
end

/-- The specialization of `simple_graph.walk.map` for mapping walks to supergraphs. -/
@[reducible] def map_le {G G' : simple_graph V} (h : G ≤ G') {u v : V} (p : G.walk u v) :
  G'.walk u v := p.map (hom.map_spanning_subgraphs h)

@[simp] lemma map_le_is_trail {G G' : simple_graph V} (h : G ≤ G') {u v : V} {p : G.walk u v} :
  (p.map_le h).is_trail ↔ p.is_trail := map_is_trail_iff_of_injective (function.injective_id)

alias map_le_is_trail ↔ is_trail.of_map_le is_trail.map_le

@[simp] lemma map_le_is_path {G G' : simple_graph V} (h : G ≤ G') {u v : V} {p : G.walk u v} :
  (p.map_le h).is_path ↔ p.is_path := map_is_path_iff_of_injective (function.injective_id)

alias map_le_is_path ↔ is_path.of_map_le is_path.map_le

@[simp] lemma map_le_is_cycle {G G' : simple_graph V} (h : G ≤ G') {u : V} {p : G.walk u u} :
  (p.map_le h).is_cycle ↔ p.is_cycle := map_is_cycle_iff_of_injective (function.injective_id)

alias map_le_is_cycle ↔ is_cycle.of_map_le is_cycle.map_le

end walk

namespace path
variables {G G'}

/-- Given an injective graph homomorphism, map paths to paths. -/
@[simps] protected def map (f : G →g G') (hinj : function.injective f) {u v : V} (p : G.path u v) :
  G'.path (f u) (f v) :=
⟨walk.map f p, walk.map_is_path_of_injective hinj p.2⟩

lemma map_injective {f : G →g G'} (hinj : function.injective f) (u v : V) :
  function.injective (path.map f hinj : G.path u v → G'.path (f u) (f v)) :=
begin
  rintros ⟨p, hp⟩ ⟨p', hp'⟩ h,
  simp only [path.map, subtype.coe_mk] at h,
  simp [walk.map_injective_of_injective hinj u v h],
end

/-- Given a graph embedding, map paths to paths. -/
@[simps] protected def map_embedding (f : G ↪g G') {u v : V} (p : G.path u v) :
  G'.path (f u) (f v) :=
path.map f.to_hom f.injective p

lemma map_embedding_injective (f : G ↪g G') (u v : V) :
  function.injective (path.map_embedding f : G.path u v → G'.path (f u) (f v)) :=
map_injective f.injective u v

end path

/-! ### Transferring between graphs -/

namespace walk

variables {G}

/-- The walk `p` transferred to lie in `H`, given that `H` contains its edges. -/
@[protected, simp] def transfer : Π {u v : V} (p : G.walk u v) (H : simple_graph V)
  (h : ∀ e, e ∈ p.edges → e ∈ H.edge_set), H.walk u v
| _ _ (walk.nil) H h := walk.nil
| _ _ (walk.cons' u v w a p) H h :=
  walk.cons (h (⟦(u, v)⟧ : sym2 V) (by simp)) (p.transfer H (λ e he, h e (by simp [he])))

variables {u v w : V} (p : G.walk u v) (q : G.walk v w)
  {H : simple_graph V}
  (hp : ∀ e, e ∈ p.edges → e ∈ H.edge_set)
  (hq : ∀ e, e ∈ q.edges → e ∈ H.edge_set)

lemma transfer_self : p.transfer G p.edges_subset_edge_set = p :=
by { induction p; simp only [*, transfer, eq_self_iff_true, heq_iff_eq, and_self], }

lemma transfer_eq_map_of_le (GH : G ≤ H) :
  p.transfer H hp = p.map (simple_graph.hom.map_spanning_subgraphs GH) :=
by { induction p; simp only [*, transfer, map_cons, hom.map_spanning_subgraphs_apply,
                             eq_self_iff_true, heq_iff_eq, and_self, map_nil], }

@[simp] lemma edges_transfer : (p.transfer H hp).edges = p.edges :=
by { induction p; simp only [*, transfer, edges_nil, edges_cons, eq_self_iff_true, and_self], }

@[simp] lemma support_transfer : (p.transfer H hp).support = p.support :=
by { induction p; simp only [*, transfer, eq_self_iff_true, and_self, support_nil, support_cons], }

@[simp] lemma length_transfer : (p.transfer H hp).length = p.length :=
by induction p; simp [*]

variables {p}

protected lemma is_path.transfer (pp : p.is_path) : (p.transfer H hp).is_path :=
begin
  induction p;
  simp only [transfer, is_path.nil, cons_is_path_iff, support_transfer] at pp ⊢,
  { tauto, },
end

protected lemma is_cycle.transfer {p : G.walk u u} (pc : p.is_cycle) (hp) :
  (p.transfer H hp).is_cycle :=
begin
  cases p;
  simp only [transfer, is_cycle.not_of_nil, cons_is_cycle_iff, transfer, edges_transfer] at pc ⊢,
  { exact pc, },
  { exact ⟨pc.left.transfer _, pc.right⟩, },
end

variables (p)

@[simp] lemma transfer_transfer {K : simple_graph V} (hp' : ∀ e, e ∈ p.edges → e ∈ K.edge_set) :
  (p.transfer H hp).transfer K (by { rw p.edges_transfer hp, exact hp', }) = p.transfer K hp' :=
by { induction p; simp only [transfer, eq_self_iff_true, heq_iff_eq, true_and], apply p_ih, }

@[simp] lemma transfer_append (hpq) :
  (p.append q).transfer H hpq =
  (p.transfer H (λ e he, by { apply hpq, simp [he] })).append
    (q.transfer H (λ e he, by { apply hpq, simp [he] })) :=
begin
  induction p;
  simp only [transfer, nil_append, cons_append, eq_self_iff_true, heq_iff_eq, true_and],
  apply p_ih,
end

@[simp] lemma reverse_transfer :
  (p.transfer H hp).reverse =
  p.reverse.transfer H (by { simp only [edges_reverse, list.mem_reverse], exact hp, }) :=
begin
  induction p;
  simp only [*, transfer_append, transfer, reverse_nil, reverse_cons],
  refl,
end

end walk

/-! ## Deleting edges -/

namespace walk
variables {G}

/-- Given a walk that avoids a set of edges, produce a walk in the graph
with those edges deleted. -/
@[reducible]
def to_delete_edges (s : set (sym2 V))
  {v w : V} (p : G.walk v w) (hp : ∀ e, e ∈ p.edges → ¬ e ∈ s) : (G.delete_edges s).walk v w :=
p.transfer _ (by
  { simp only [edge_set_delete_edges, set.mem_diff],
    exact λ e ep, ⟨edges_subset_edge_set p ep, hp e ep⟩, })

@[simp] lemma to_delete_edges_nil (s : set (sym2 V)) {v : V} (hp) :
  (walk.nil : G.walk v v).to_delete_edges s hp = walk.nil := rfl

@[simp] lemma to_delete_edges_cons (s : set (sym2 V))
  {u v w : V} (h : G.adj u v) (p : G.walk v w) (hp) :
  (walk.cons h p).to_delete_edges s hp =
    walk.cons ⟨h, hp _ (or.inl rfl)⟩ (p.to_delete_edges s $ λ _ he, hp _ $ or.inr he) := rfl

/-- Given a walk that avoids an edge, create a walk in the subgraph with that edge deleted.
This is an abbreviation for `simple_graph.walk.to_delete_edges`. -/
abbreviation to_delete_edge {v w : V} (e : sym2 V) (p : G.walk v w) (hp : e ∉ p.edges) :
  (G.delete_edges {e}).walk v w :=
p.to_delete_edges {e} (λ e', by { contrapose!, simp [hp] { contextual := tt } })

@[simp]
lemma map_to_delete_edges_eq (s : set (sym2 V)) {v w : V} {p : G.walk v w} (hp) :
  walk.map (hom.map_spanning_subgraphs (G.delete_edges_le s)) (p.to_delete_edges s hp) = p :=
by rw [←transfer_eq_map_of_le, transfer_transfer, transfer_self]

protected lemma is_path.to_delete_edges (s : set (sym2 V))
  {v w : V} {p : G.walk v w} (h : p.is_path) (hp) :
  (p.to_delete_edges s hp).is_path := h.transfer _

protected lemma is_cycle.to_delete_edges (s : set (sym2 V))
  {v : V} {p : G.walk v v} (h : p.is_cycle) (hp) :
  (p.to_delete_edges s hp).is_cycle := h.transfer _

@[simp] lemma to_delete_edges_copy (s : set (sym2 V))
  {u v u' v'} (p : G.walk u v) (hu : u = u') (hv : v = v') (h) :
  (p.copy hu hv).to_delete_edges s h
    = (p.to_delete_edges s (by { subst_vars, exact h })).copy hu hv :=
by { subst_vars, refl }

end walk

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

protected lemma walk.reachable {G : simple_graph V} {u v : V} (p : G.walk u v) :
  G.reachable u v := ⟨p⟩

protected lemma adj.reachable {u v : V} (h : G.adj u v) :
  G.reachable u v := h.to_walk.reachable

@[refl] protected lemma reachable.refl (u : V) : G.reachable u u := by { fsplit, refl }
protected lemma reachable.rfl {u : V} : G.reachable u u := reachable.refl _

@[symm] protected lemma reachable.symm {u v : V} (huv : G.reachable u v) : G.reachable v u :=
huv.elim (λ p, ⟨p.reverse⟩)

lemma reachable_comm {u v : V} : G.reachable u v ↔ G.reachable v u :=
⟨reachable.symm, reachable.symm⟩

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

protected lemma reachable.map {G : simple_graph V} {G' : simple_graph V'}
  (f : G →g G') {u v : V} (h : G.reachable u v) : G'.reachable (f u) (f v) :=
h.elim (λ p, ⟨p.map f⟩)

variables (G)

lemma reachable_is_equivalence : equivalence G.reachable :=
mk_equivalence _ (@reachable.refl _ G) (@reachable.symm _ G) (@reachable.trans _ G)

/-- The equivalence relation on vertices given by `simple_graph.reachable`. -/
def reachable_setoid : setoid V := setoid.mk _ G.reachable_is_equivalence

/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def preconnected : Prop := ∀ (u v : V), G.reachable u v

lemma preconnected.map {G : simple_graph V} {H : simple_graph V'} (f : G →g H) (hf : surjective f)
  (hG : G.preconnected) : H.preconnected :=
hf.forall₂.2 $ λ a b, nonempty.map (walk.map _) $ hG _ _

lemma iso.preconnected_iff {G : simple_graph V} {H : simple_graph V'} (e : G ≃g H) :
  G.preconnected ↔ H.preconnected :=
⟨preconnected.map e.to_hom e.to_equiv.surjective,
  preconnected.map e.symm.to_hom e.symm.to_equiv.surjective⟩

/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `has_coe_to_fun` instance so that `h u v` can be used instead
of `h.preconnected u v`. -/
@[protect_proj, mk_iff]
structure connected : Prop :=
(preconnected : G.preconnected)
[nonempty : nonempty V]

instance : has_coe_to_fun G.connected (λ _, Π (u v : V), G.reachable u v) :=
⟨λ h, h.preconnected⟩

lemma connected.map {G : simple_graph V} {H : simple_graph V'} (f : G →g H) (hf : surjective f)
  (hG : G.connected) : H.connected :=
by { haveI := hG.nonempty.map f, exact ⟨hG.preconnected.map f hf⟩ }

lemma iso.connected_iff {G : simple_graph V} {H : simple_graph V'} (e : G ≃g H) :
  G.connected ↔ H.connected :=
⟨connected.map e.to_hom e.to_equiv.surjective,
  connected.map e.symm.to_hom e.symm.to_equiv.surjective⟩

/-- The quotient of `V` by the `simple_graph.reachable` relation gives the connected
components of a graph. -/
def connected_component := quot G.reachable

/-- Gives the connected component containing a particular vertex. -/
def connected_component_mk (v : V) : G.connected_component := quot.mk G.reachable v

variables {V' G G' G''}

namespace connected_component

@[simps] instance inhabited [inhabited V] : inhabited G.connected_component :=
⟨G.connected_component_mk default⟩

@[elab_as_eliminator]
protected lemma ind {β : G.connected_component → Prop}
  (h : ∀ (v : V), β (G.connected_component_mk v)) (c : G.connected_component) : β c :=
quot.ind h c

@[elab_as_eliminator]
protected lemma ind₂ {β : G.connected_component → G.connected_component → Prop}
  (h : ∀ (v w : V), β (G.connected_component_mk v) (G.connected_component_mk w))
  (c d : G.connected_component) : β c d :=
quot.induction_on₂ c d h

protected lemma sound {v w : V} :
  G.reachable v w → G.connected_component_mk v = G.connected_component_mk w := quot.sound

protected lemma exact {v w : V} :
  G.connected_component_mk v = G.connected_component_mk w → G.reachable v w :=
@quotient.exact _ G.reachable_setoid _ _

@[simp] protected lemma eq {v w : V} :
  G.connected_component_mk v = G.connected_component_mk w ↔ G.reachable v w :=
@quotient.eq _ G.reachable_setoid _ _

/-- The `connected_component` specialization of `quot.lift`. Provides the stronger
assumption that the vertices are connected by a path. -/
protected def lift {β : Sort*} (f : V → β)
  (h : ∀ (v w : V) (p : G.walk v w), p.is_path → f v = f w) : G.connected_component → β :=
quot.lift f (λ v w (h' : G.reachable v w), h'.elim_path (λ hp, h v w hp hp.2))

@[simp] protected lemma lift_mk {β : Sort*} {f : V → β}
  {h : ∀ (v w : V) (p : G.walk v w), p.is_path → f v = f w} {v : V} :
  connected_component.lift f h (G.connected_component_mk v) = f v := rfl

protected lemma «exists» {p : G.connected_component → Prop} :
  (∃ (c : G.connected_component), p c) ↔ ∃ v, p (G.connected_component_mk v) :=
(surjective_quot_mk G.reachable).exists

protected lemma «forall» {p : G.connected_component → Prop} :
  (∀ (c : G.connected_component), p c) ↔ ∀ v, p (G.connected_component_mk v) :=
(surjective_quot_mk G.reachable).forall

lemma _root_.simple_graph.preconnected.subsingleton_connected_component (h : G.preconnected) :
  subsingleton G.connected_component :=
⟨connected_component.ind₂ (λ v w, connected_component.sound (h v w))⟩

/-- The map on connected components induced by a graph homomorphism. -/
def map (φ : G →g G') (C : G.connected_component) : G'.connected_component :=
C.lift (λ v, G'.connected_component_mk (φ v)) $ λ v w p _,
  connected_component.eq.mpr (p.map φ).reachable

@[simp] lemma map_mk (φ : G →g G') (v : V) :
  (G.connected_component_mk v).map φ = G'.connected_component_mk (φ v) := rfl

@[simp] lemma map_id (C : connected_component G) : C.map hom.id = C :=
by { refine C.ind _, exact (λ _, rfl) }

@[simp] lemma map_comp (C : G.connected_component)
  (φ : G →g G') (ψ : G' →g G'') : (C.map φ).map ψ = C.map (ψ.comp φ) :=
by { refine C.ind _, exact (λ _, rfl), }

end connected_component

/-- A subgraph is connected if it is connected as a simple graph. -/
abbreviation subgraph.connected (H : G.subgraph) : Prop := H.coe.connected

lemma singleton_subgraph_connected {v : V} : (G.singleton_subgraph v).connected :=
begin
  split,
  rintros ⟨a, ha⟩ ⟨b, hb⟩,
  simp only [singleton_subgraph_verts, set.mem_singleton_iff] at ha hb,
  subst_vars
end

@[simp] lemma subgraph_of_adj_connected {v w : V} (hvw : G.adj v w) :
  (G.subgraph_of_adj hvw).connected :=
begin
  split,
  rintro ⟨a, ha⟩ ⟨b, hb⟩,
  simp only [subgraph_of_adj_verts, set.mem_insert_iff, set.mem_singleton_iff] at ha hb,
  obtain (rfl|rfl) := ha; obtain (rfl|rfl) := hb;
    refl <|> { apply adj.reachable, simp },
end

lemma preconnected.set_univ_walk_nonempty (hconn : G.preconnected) (u v : V) :
  (set.univ : set (G.walk u v)).nonempty :=
by { rw ← set.nonempty_iff_univ_nonempty, exact hconn u v }

lemma connected.set_univ_walk_nonempty (hconn : G.connected) (u v : V) :
  (set.univ : set (G.walk u v)).nonempty := hconn.preconnected.set_univ_walk_nonempty u v

/-! ### Walks as subgraphs -/

namespace walk
variables {G G'} {u v w : V}

/-- The subgraph consisting of the vertices and edges of the walk. -/
@[simp] protected def to_subgraph : Π {u v : V}, G.walk u v → G.subgraph
| u _ nil := G.singleton_subgraph u
| _ _ (cons h p) := G.subgraph_of_adj h ⊔ p.to_subgraph

lemma to_subgraph_cons_nil_eq_subgraph_of_adj (h : G.adj u v) :
  (cons h nil).to_subgraph = G.subgraph_of_adj h :=
by simp

lemma mem_verts_to_subgraph (p : G.walk u v) :
  w ∈ p.to_subgraph.verts ↔ w ∈ p.support :=
begin
  induction p with _ x y z h p' ih,
  { simp },
  { have : w = y ∨ w ∈ p'.support ↔ w ∈ p'.support :=
      ⟨by rintro (rfl | h); simp [*], by simp { contextual := tt}⟩,
    simp [ih, or_assoc, this] }
end

@[simp] lemma verts_to_subgraph (p : G.walk u v) : p.to_subgraph.verts = {w | w ∈ p.support} :=
set.ext (λ _, p.mem_verts_to_subgraph)

lemma mem_edges_to_subgraph (p : G.walk u v) {e : sym2 V} :
  e ∈ p.to_subgraph.edge_set ↔ e ∈ p.edges :=
by induction p; simp [*]

@[simp] lemma edge_set_to_subgraph (p : G.walk u v) : p.to_subgraph.edge_set = {e | e ∈ p.edges} :=
set.ext (λ _, p.mem_edges_to_subgraph)

@[simp] lemma to_subgraph_append (p : G.walk u v) (q : G.walk v w) :
  (p.append q).to_subgraph = p.to_subgraph ⊔ q.to_subgraph :=
by induction p; simp [*, sup_assoc]

@[simp] lemma to_subgraph_reverse (p : G.walk u v) :
  p.reverse.to_subgraph = p.to_subgraph :=
begin
  induction p,
  { simp },
  { simp only [*, walk.to_subgraph, reverse_cons, to_subgraph_append, subgraph_of_adj_symm],
    rw [sup_comm],
    congr,
    ext; simp [-set.bot_eq_empty], }
end

@[simp] lemma to_subgraph_rotate [decidable_eq V] (c : G.walk v v) (h : u ∈ c.support) :
  (c.rotate h).to_subgraph = c.to_subgraph :=
by rw [rotate, to_subgraph_append, sup_comm, ← to_subgraph_append, take_spec]

@[simp] lemma to_subgraph_map (f : G →g G') (p : G.walk u v) :
  (p.map f).to_subgraph = p.to_subgraph.map f :=
by induction p; simp [*, subgraph.map_sup]

@[simp] lemma finite_neighbor_set_to_subgraph (p : G.walk u v) :
  (p.to_subgraph.neighbor_set w).finite :=
begin
  induction p,
  { rw [walk.to_subgraph, neighbor_set_singleton_subgraph],
    apply set.to_finite, },
  { rw [walk.to_subgraph, subgraph.neighbor_set_sup],
    refine set.finite.union _ p_ih,
    refine set.finite.subset _ (neighbor_set_subgraph_of_adj_subset p_h),
    apply set.to_finite, },
end

end walk

/-! ### Walks of a given length -/

section walk_counting

lemma set_walk_self_length_zero_eq (u : V) :
  {p : G.walk u u | p.length = 0} = {walk.nil} :=
by { ext p, simp }

lemma set_walk_length_zero_eq_of_ne {u v : V} (h : u ≠ v) :
  {p : G.walk u v | p.length = 0} = ∅ :=
begin
  ext p,
  simp only [set.mem_set_of_eq, set.mem_empty_iff_false, iff_false],
  exact λ h', absurd (walk.eq_of_length_eq_zero h') h,
end

lemma set_walk_length_succ_eq (u v : V) (n : ℕ) :
  {p : G.walk u v | p.length = n.succ} =
    ⋃ (w : V) (h : G.adj u w), walk.cons h '' {p' : G.walk w v | p'.length = n} :=
begin
  ext p,
  cases p with _ _ w _ huw pwv,
  { simp [eq_comm], },
  { simp only [nat.succ_eq_add_one, set.mem_set_of_eq, walk.length_cons, add_left_inj,
      set.mem_Union, set.mem_image, exists_prop],
    split,
    { rintro rfl,
      exact ⟨w, huw, pwv, rfl, rfl, heq.rfl⟩, },
    { rintro ⟨w, huw, pwv, rfl, rfl, rfl⟩,
      refl, } },
end

variables (G) [decidable_eq V]

section locally_finite
variables [locally_finite G]

/-- The `finset` of length-`n` walks from `u` to `v`.
This is used to give `{p : G.walk u v | p.length = n}` a `fintype` instance, and it
can also be useful as a recursive description of this set when `V` is finite.

See `simple_graph.coe_finset_walk_length_eq` for the relationship between this `finset` and
the set of length-`n` walks. -/
def finset_walk_length : Π (n : ℕ) (u v : V), finset (G.walk u v)
| 0 u v := if h : u = v
           then by { subst u, exact {walk.nil} }
           else ∅
| (n+1) u v := finset.univ.bUnion (λ (w : G.neighbor_set u),
                 (finset_walk_length n w v).map ⟨λ p, walk.cons w.property p, λ p q, by simp⟩)

lemma coe_finset_walk_length_eq (n : ℕ) (u v : V) :
  (G.finset_walk_length n u v : set (G.walk u v)) = {p : G.walk u v | p.length = n} :=
begin
  induction n with n ih generalizing u v,
  { obtain rfl | huv := eq_or_ne u v;
    simp [finset_walk_length, set_walk_length_zero_eq_of_ne, *], },
  { simp only [finset_walk_length, set_walk_length_succ_eq,
      finset.coe_bUnion, finset.mem_coe, finset.mem_univ, set.Union_true],
    ext p,
    simp only [mem_neighbor_set, finset.coe_map, embedding.coe_fn_mk, set.Union_coe_set,
      set.mem_Union, set.mem_image, finset.mem_coe, set.mem_set_of_eq],
    congr' with w,
    congr' with h,
    congr' with q,
    have := set.ext_iff.mp (ih w v) q,
    simp only [finset.mem_coe, set.mem_set_of_eq] at this,
    rw ← this,
    refl, },
end

variables {G}

lemma walk.mem_finset_walk_length_iff_length_eq {n : ℕ} {u v : V} (p : G.walk u v) :
  p ∈ G.finset_walk_length n u v ↔ p.length = n :=
set.ext_iff.mp (G.coe_finset_walk_length_eq n u v) p

variables (G)

instance fintype_set_walk_length (u v : V) (n : ℕ) : fintype {p : G.walk u v | p.length = n} :=
fintype.of_finset (G.finset_walk_length n u v) $ λ p,
by rw [←finset.mem_coe, coe_finset_walk_length_eq]

lemma set_walk_length_to_finset_eq (n : ℕ) (u v : V) :
  {p : G.walk u v | p.length = n}.to_finset = G.finset_walk_length n u v :=
by { ext p, simp [←coe_finset_walk_length_eq] }

/- See `simple_graph.adj_matrix_pow_apply_eq_card_walk` for the cardinality in terms of the `n`th
power of the adjacency matrix. -/
lemma card_set_walk_length_eq (u v : V) (n : ℕ) :
  fintype.card {p : G.walk u v | p.length = n} = (G.finset_walk_length n u v).card :=
fintype.card_of_finset (G.finset_walk_length n u v) $ λ p,
  by rw [←finset.mem_coe, coe_finset_walk_length_eq]

instance fintype_set_path_length (u v : V) (n : ℕ) :
  fintype {p : G.walk u v | p.is_path ∧ p.length = n} :=
fintype.of_finset ((G.finset_walk_length n u v).filter walk.is_path) $
  by simp [walk.mem_finset_walk_length_iff_length_eq, and_comm]

end locally_finite

section finite
variables [fintype V] [decidable_rel G.adj]

lemma reachable_iff_exists_finset_walk_length_nonempty (u v : V) :
  G.reachable u v ↔ ∃ (n : fin (fintype.card V)), (G.finset_walk_length n u v).nonempty :=
begin
  split,
  { intro r,
    refine r.elim_path (λ p, _),
    refine ⟨⟨_, p.is_path.length_lt⟩, p, _⟩,
    simp [walk.mem_finset_walk_length_iff_length_eq], },
  { rintro ⟨_, p, _⟩, use p },
end

instance : decidable_rel G.reachable :=
λ u v, decidable_of_iff' _ (reachable_iff_exists_finset_walk_length_nonempty G u v)

instance : fintype G.connected_component :=
@quotient.fintype _ _ G.reachable_setoid (infer_instance : decidable_rel G.reachable)

instance : decidable G.preconnected :=
by { unfold preconnected, apply_instance }

instance : decidable G.connected :=
by { rw [connected_iff, ← finset.univ_nonempty_iff], exact and.decidable }

end finite

end walk_counting

section bridge_edges

/-! ### Bridge edges -/

/-- An edge of a graph is a *bridge* if, after removing it, its incident vertices
are no longer reachable from one another. -/
def is_bridge (G : simple_graph V) (e : sym2 V) : Prop :=
e ∈ G.edge_set ∧
sym2.lift ⟨λ v w, ¬ (G \ from_edge_set {e}).reachable v w, by simp [reachable_comm]⟩ e

lemma is_bridge_iff {u v : V} :
  G.is_bridge ⟦(u, v)⟧ ↔ G.adj u v ∧ ¬ (G \ from_edge_set {⟦(u, v)⟧}).reachable u v := iff.rfl

lemma reachable_delete_edges_iff_exists_walk {v w : V} :
  (G \ from_edge_set {⟦(v, w)⟧}).reachable v w ↔ ∃ (p : G.walk v w), ¬ ⟦(v, w)⟧ ∈ p.edges :=
begin
  split,
  { rintro ⟨p⟩,
    use p.map (hom.map_spanning_subgraphs (by simp)),
    simp_rw [walk.edges_map, list.mem_map, hom.map_spanning_subgraphs_apply, sym2.map_id', id.def],
    rintro ⟨e, h, rfl⟩,
    simpa using p.edges_subset_edge_set h, },
  { rintro ⟨p, h⟩,
    refine ⟨p.transfer _ (λ e ep, _)⟩,
    simp only [edge_set_sdiff, edge_set_from_edge_set, edge_set_sdiff_sdiff_is_diag,
               set.mem_diff, set.mem_singleton_iff],
    exact ⟨p.edges_subset_edge_set ep, λ h', h (h' ▸ ep)⟩,  },
end

lemma is_bridge_iff_adj_and_forall_walk_mem_edges {v w : V} :
  G.is_bridge ⟦(v, w)⟧ ↔ G.adj v w ∧ ∀ (p : G.walk v w), ⟦(v, w)⟧ ∈ p.edges :=
begin
  rw [is_bridge_iff, and_congr_right'],
  rw [reachable_delete_edges_iff_exists_walk, not_exists_not],
end

lemma reachable_delete_edges_iff_exists_cycle.aux [decidable_eq V]
  {u v w : V}
  (hb : ∀ (p : G.walk v w), ⟦(v, w)⟧ ∈ p.edges)
  (c : G.walk u u)
  (hc : c.is_trail)
  (he : ⟦(v, w)⟧ ∈ c.edges)
  (hw : w ∈ (c.take_until v (c.fst_mem_support_of_mem_edges he)).support) :
  false :=
begin
  have hv := c.fst_mem_support_of_mem_edges he,
  -- decompose c into
  --      puw     pwv     pvu
  --   u ----> w ----> v ----> u
  let puw := (c.take_until v hv).take_until w hw,
  let pwv := (c.take_until v hv).drop_until w hw,
  let pvu := c.drop_until v hv,
  have : c = (puw.append pwv).append pvu := by simp,
  -- We have two walks from v to w
  --      pvu     puw
  --   v ----> u ----> w
  --   |               ^
  --    `-------------'
  --      pwv.reverse
  -- so they both contain the edge ⟦(v, w)⟧, but that's a contradiction since c is a trail.
  have hbq := hb (pvu.append puw),
  have hpq' := hb pwv.reverse,
  rw [walk.edges_reverse, list.mem_reverse] at hpq',
  rw [walk.is_trail_def, this, walk.edges_append, walk.edges_append,
      list.nodup_append_comm, ← list.append_assoc, ← walk.edges_append] at hc,
  exact list.disjoint_of_nodup_append hc hbq hpq',
end

lemma adj_and_reachable_delete_edges_iff_exists_cycle {v w : V} :
  G.adj v w ∧ (G \ from_edge_set {⟦(v, w)⟧}).reachable v w ↔
  ∃ (u : V) (p : G.walk u u), p.is_cycle ∧ ⟦(v, w)⟧ ∈ p.edges :=
begin
  classical,
  rw reachable_delete_edges_iff_exists_walk,
  split,
  { rintro ⟨h, p, hp⟩,
    refine ⟨w, walk.cons h.symm p.to_path, _, _⟩,
    { apply path.cons_is_cycle,
      rw [sym2.eq_swap],
      intro h,
      exact absurd (walk.edges_to_path_subset p h) hp, },
    simp only [sym2.eq_swap, walk.edges_cons, list.mem_cons_iff, eq_self_iff_true, true_or], },
  { rintro ⟨u, c, hc, he⟩,
    have hvc : v ∈ c.support := walk.fst_mem_support_of_mem_edges c he,
    have hwc : w ∈ c.support := walk.snd_mem_support_of_mem_edges c he,
    let puv := c.take_until v hvc,
    let pvu := c.drop_until v hvc,
    obtain (hw | hw') : w ∈ puv.support ∨ w ∈ pvu.support,
    { rwa [← walk.mem_support_append_iff, walk.take_spec] },
    { by_contra' h,
      specialize h (c.adj_of_mem_edges he),
      exact reachable_delete_edges_iff_exists_cycle.aux h c hc.to_trail he hw, },
    { by_contra' hb,
      specialize hb (c.adj_of_mem_edges he),
      have hb' : ∀ (p : G.walk w v), ⟦(w, v)⟧ ∈ p.edges,
      { intro p,
        simpa [sym2.eq_swap] using hb p.reverse, },
      apply reachable_delete_edges_iff_exists_cycle.aux hb' (pvu.append puv)
        (hc.to_trail.rotate hvc) _ (walk.start_mem_support _),
      rwa [walk.edges_append, list.mem_append, or_comm, ← list.mem_append,
           ← walk.edges_append, walk.take_spec, sym2.eq_swap], } },
end

lemma is_bridge_iff_adj_and_forall_cycle_not_mem {v w : V} :
  G.is_bridge ⟦(v, w)⟧ ↔ G.adj v w ∧ ∀ ⦃u : V⦄ (p : G.walk u u), p.is_cycle → ⟦(v, w)⟧ ∉ p.edges :=
begin
  rw [is_bridge_iff, and.congr_right_iff],
  intro h,
  rw ← not_iff_not,
  push_neg,
  rw ← adj_and_reachable_delete_edges_iff_exists_cycle,
  simp only [h, true_and],
end

lemma is_bridge_iff_mem_and_forall_cycle_not_mem {e : sym2 V} :
  G.is_bridge e ↔ e ∈ G.edge_set ∧ ∀ ⦃u : V⦄ (p : G.walk u u), p.is_cycle → e ∉ p.edges :=
sym2.ind (λ v w, is_bridge_iff_adj_and_forall_cycle_not_mem) e

end bridge_edges

end simple_graph
