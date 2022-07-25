import data.rel
import data.set.finite
import data.sym.sym2
import set_theory.cardinal.finite
import algebra.big_operators.finprod

open_locale classical big_operators

noncomputable theory

open finset
universes u v w

variables {V : Type u} {E : Type v}

structure graph (V : Type u) (E : Type v) :=
(ends : E → sym2 V)
-- i believe that multigraph should not be something that relies on
-- digraph definitions to function, but rather that it should stand as its
-- own object

-- i also think using sym2 V will make it easier to generalize to
-- hypergraphs with sym n

namespace graph

section basic

variables {G : graph V E} {u v : V} {e f : E}

def adj (G : graph V E) : V → V → Prop :=
  λ v w, ∃ (e : E), G.ends e = ⟦(v, w)⟧

def inc (G : graph V E) : V → E → Prop :=
  λ v e, v ∈ G.ends e

/-- Set of edges incident to a given vertex, aka incidence set. -/
def incidence_set (G : graph V E) (v : V) : set E := {e : E | v ∈ G.ends e}

/-- Make a graph from the digraph -/
def graph.mk {V : Type u} {E : Type v} (ends : E → sym2 V) : graph V E := { ends := ends }

@[symm] lemma adj_symm (h : G.adj u v) : G.adj v u :=
begin
  cases h with e he,
  use e,
  rw sym2.eq_swap,
  exact he,
end

structure dart (G : graph V E) : Type (max u v) :=
(head : V)
(tail : V)
(e : E)
(h : G.ends e = ⟦(head, tail)⟧)

def reverse_dart (G : graph V E) (d : G.dart) : G.dart :=
{ head := d.tail,
  tail := d.head,
  e := d.e,
  h := by { rw d.h, rw sym2.eq_swap} }

@[simp]
lemma reverse_head_tail (G : graph V E) (d : G.dart) : (G.reverse_dart d).tail = d.head :=
  by refl

@[simp]
lemma reverse_tail_head (G : graph V E) (d : G.dart) : (G.reverse_dart d).head = d.tail :=
  by refl
end basic

section walks

variables (G : graph V E)

structure walk (G : graph V E) : Type (max u v) :=
(head : V)
(tail : V)
(darts : list G.dart)
(is_walk :
  [head] ++ (list.map dart.tail darts)
  = (list.map dart.head darts) ++ [tail])

lemma walk_rev_head (p : walk G) :
  list.map dart.head (list.map G.reverse_dart p.darts) =
    (list.map dart.tail p.darts) :=
begin
  simp,
  refl,
end

lemma walk_rev_tail (p : walk G) :
  list.map dart.tail (list.map G.reverse_dart p.darts) =
    (list.map dart.head p.darts) :=
begin
  simp,
  refl,
end

def empty_walk (v : V) : walk G :=
{ head := v,
  tail := v,
  darts := [],
  is_walk := by simp }

def reverse (p : walk G) : walk G :=
{ head := p.tail,
  tail := p.head,
  darts := (list.map G.reverse_dart p.darts.reverse),
  is_walk :=
    begin
      rw list.map_reverse,
      rw list.map_reverse,
      rw list.map_reverse,
      rw ← list.reverse_singleton,
      rw ← list.reverse_append,
      rw ← list.reverse_singleton p.head,
      rw ← list.reverse_append,
      rw list.reverse_inj,
      rw [walk_rev_head, walk_rev_tail, p.is_walk],
    end }

def append (p q : walk G) (h : p.tail = q.head) : walk G :=
{ head := p.head,
  tail := q.tail,
  darts := p.darts ++ q.darts,
  is_walk :=
    begin
      rw list.map_append,
      rw list.map_append,
      rw list.append_assoc,
      rw ← q.is_walk,
      rw ← list.append_assoc,
      rw p.is_walk,
      rw h,
      simp,
    end }

def reachable (u v : V) : Prop := ∃ (p : G.walk), p.head = u ∧ p.tail = v

namespace walk

@[refl] protected lemma reachable.refl (u : V) : G.reachable u u :=
begin
  use G.empty_walk u,
  split,
  rw empty_walk,
  rw empty_walk,
end
protected lemma reachable.rfl {u : V} : G.reachable u u := reachable.refl _ _

@[symm] protected lemma reachable.symm {u v : V} (huv : G.reachable u v) : G.reachable v u :=
begin
  cases huv with p hp,
  use G.reverse p,
  split,
  rw ← hp.2,
  refl,
  rw ← hp.1,
  refl,
end

@[trans] protected lemma reachable.trans {u v w : V} (huv : G.reachable u v) (hvw : G.reachable v w)
  : G.reachable u w :=
begin
  cases huv with p hp,
  cases hvw with q hq,
  have h : p.tail = q.head,
  rw [hp.2, hq.1],
  use G.append p q h,
  split,
  rw ← hp.1,
  refl,
  rw ← hq.2,
  refl,
end

def edges {G : graph V E} (p : G.walk) : list E := list.map dart.e p.darts

def support {G : graph V E} (p : G.walk) : list V := [p.head] ++ list.map dart.head p.darts

/-! ### Trails, paths, circuits, cycles -/

/-- A *trail* is a walk with no repeating edges. -/
structure is_trail {G : graph V E} (p : G.walk) : Prop :=
(edges_nodup : p.edges.nodup)

/-- A *path* is a walk with no repeating vertices. -/
structure is_path {G : graph V E} (p : G.walk) : Prop :=
(support_nodup : p.support.nodup)

/-- A *circuit* is a nonempty trail beginning and ending at the same vertex. -/
-- extends path & need to get rid of loops
structure is_circuit {G : graph V E} (p : G.walk) : Prop :=
(start_end : p.head = p.tail)
(ne_nil : p.darts ≠ [])

/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure is_cycle {G : graph V E} (p : G.walk) : Prop :=
(support_nodup : p.support.tail.nodup)

-- swap cycle and circuit definitions
-- show that circuit is edge set of 2-regular connected subgraph

end walk

end walks

section conn

def connected (G : graph V E) : Prop := ∀ u v : V, G.reachable u v

def is_loop_edge_of (G : graph V E) (v : V) (e : E) : Prop := G.ends e = sym2.diag v

def is_loop_edge (G : graph V E) (e : E) : Prop := sym2.is_diag (G.ends e)

def degree (G : graph V E) (v : V) : ℕ := nat.card (G.incidence_set v)
  + nat.card {e | G.is_loop_edge_of v e}
-- double count loop edges

theorem handshake (G : graph V E) [fintype V] [fintype E] :
  ∑ᶠ (x : V), G.degree x = 2 * (fintype.card E) :=
begin
  unfold degree,

  sorry,
end

def regular (G : graph V E) (k : ℕ) : Prop := ∀ (v : V), G.degree v = k

lemma is_trail_def {G : graph V E} (p : G.walk) : p.is_trail ↔ p.edges.nodup :=
⟨walk.is_trail.edges_nodup, λ h, ⟨h⟩⟩


structure subgraph (G : graph V E) :=
(verts : set V)
(edges : set E)
(edge_sub : ∀ (e : edges), (G.ends e).to_set ⊆ verts)

end conn

namespace subgraph

variables (G : graph V E)

/-- Give a vertex as an element of the subgraph's vertex type. -/
@[reducible]
def vert (G' : subgraph G) (v : V) (h : v ∈ G'.verts) : G'.verts := ⟨v, h⟩

def ends (G' : subgraph G) (e : E) (h : e ∈ G'.edges) : sym2 (G'.verts) :=
begin
  refine ⟦(G'.vert _ (quotient.out (G.ends e)).1 _, G'.vert _ (quotient.out (G.ends e)).2 _)⟧,
  exact set.mem_of_subset_of_mem (G'.edge_sub ⟨e, h⟩) (sym2.to_set_mem1 (G.ends e)),
  exact set.mem_of_subset_of_mem (G'.edge_sub ⟨e, h⟩) (sym2.to_set_mem2 (G.ends e)),
end
-- coercion between "ends" in subgraph to graph?
-- probably easier to do with "e.other" but whatever

def adj (G' : subgraph G) : G'.verts → G'.verts → Prop :=
  λ v w, ∃ (e ∈ G'.edges), G'.ends G e H = ⟦(v, w)⟧

protected def coe {G : graph V E} (G' : subgraph G) : graph G'.verts G'.edges :=
{ ends := λ e, G'.ends G e e.2 }





end subgraph
end graph
