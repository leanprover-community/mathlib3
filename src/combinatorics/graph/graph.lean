import .digraph

open_locale classical big_operators

noncomputable theory

universes u v w

variables {V : Type u} {E : Type v}

instance graph.setoid (V : Type u) (E : Type v) : setoid (digraph V E) :=
  setoid.mk _ (digraph.is_equivalence V E)

def graph (V : Type u) (E : Type v) :=
  quotient (graph.setoid V E)

namespace graph

section basic

variables {G : graph V E} {x y z : V} {e f : E}

def adj (G : graph V E) : V → V → Prop :=
  quot.lift_on G _ (@digraph.adj_respects _ _)

def inc (G : graph V E) : V → E → Prop :=
  quot.lift_on G _ (@digraph.inc_respects _ _)

def other_end (G : graph V E) : V → E → V :=
  quot.lift_on G _ (@digraph.other_end_respects _ _)

def is_loop (G : graph V E) : E → Prop :=
  quot.lift_on G _ (@digraph.is_loop_respects _ _)

def edge_nhd (G : graph V E) : V → set E :=
  quot.lift_on G _ (@digraph.edge_nhd_respects _ _)

def loops_at (G : graph V E) : V → set E :=
  quot.lift_on G _ (@digraph.loops_at_respects _ _)

def deg (G : graph V E) : V → ℕ :=
  quot.lift_on G _ (@digraph.deg_respects _ _)

def ends_set (G : graph V E) : E → set V :=
  quot.lift_on G _ (@digraph.ends_set_respects _ _)

class finite_at (G : graph V E) (x : V) :=
  (fin : fintype (G.edge_nhd x))

def ends_are (G : graph V E) (e : E) (x y : V) : Prop :=
  G.ends_set e = {x,y}

lemma adj_symm (G : graph V E) (x y : V):
  G.adj x y → G.adj y x :=
by {induction G, exact digraph.adj_symm _ _, exact λ h, rfl}


lemma ends_are_symm (G : graph V E) (h : G.ends_are e x y):
   G.ends_are e y x :=
by {unfold ends_are at h ⊢, rw [h, set.pair_comm]}


lemma other_end_idem {G : graph V E} (x : V) (e : E):
  G.other_end (G.other_end x e) e = x :=
by {induction G, exact digraph.other_end_idem x e, refl}

lemma other_end_adj {G : digraph V E}{u : V}{e : E}(hve : G.inc x e):
  G.adj x (G.other_end x e) :=
by {induction G, exact digraph.other_end_adj hve}

theorem handshake [fintype V] [fintype E]:
  ∑ᶠ (x : V), G.deg x = 2 * (fintype.card E) :=
by {induction G, exact digraph.handshake G, refl}

-- try setting up mapping to fin 2
-- how do you choose an orientation?

lemma edges_card (G : graph V E) :
  ∀ (e : E), nat.card (G.ends_set e) = 1 ∨ nat.card (G.ends_set e) = 2 :=
begin
-- having two different definitions for the ends sets is not great
-- not easy to move between ends_set and ends_finset
  intros e,
  induction G,
  have h2 := G.card_ends_finset_le_two e,
  have h3 := G.card_ends_finset_pos e,
  rw le_iff_eq_or_lt at h2,
  cases h2 with h2 h1,
  right,
  rw G.ends_set_eq_ends_finset at h2,
-- this induction thing makes it hard to move between digraphs and graphs
-- when i do induction G it replaces it with graph (quot.mk setoid.r G), not a digraph
-- so i can't use digraph lemmas here
  rw ← h2,
  simp,
  rw ends_set,
  simp only [nat.card_eq_fintype_card, fintype.card_of_finset],

  left,
  have h4 : (G.ends_finset e).card = 1,
  omega,
  rw ends_set,
  rw ← h4,
  simp,
end

lemma inc_card (G : graph V E) :
  ∀ (x : E), nat.card {x_1 // G.inc x_1 x} = 1 ∨ nat.card {x_1 // G.inc x_1 x} = 2 :=
begin
  intros e,
  have h2 := G.edges_card e,
  induction G,
  cases h2 with h1 h2,
  left,
  rw ← h1,
  sorry,
  sorry,
  refl,
end

/-- Noncomputably gives a bijection between `α` and `fin n`, where `nat.card α = n ≠ 0`. This is
only a very slight variation on `nat.equiv_fin_of_card_pos` but might be useful to PR -/
noncomputable def nat.equiv_fin_of_card_eq_pos {α : Type u} {n : ℕ} (hn : n ≠ 0)
  (h : nat.card α = n) : α ≃ fin n :=
(nat.equiv_fin_of_card_pos (h.substr hn)).trans (fin.cast h)

/-- Given a set s known to have size 1 or 2, choose a pair (a,b) with {a,b} = s -/
noncomputable def choose_ordering {s :  set V} (hs : nat.card s = 1 ∨ nat.card s = 2) :
  fin 2 → s :=
if h : (nat.card s = 1)
  then (λ i, (nat.card_eq_one_iff_unique.mp h).2.some)
  else (nat.equiv_fin_of_card_eq_pos two_ne_zero ((or_iff_right h).mp hs)).inv_fun

/-- `choose_ordering` does what was just claimed -/
lemma choose_ordering_works {s : set V} {x : V} (hs : nat.card s = 1 ∨ nat.card s = 2) :
  x ∈ s ↔ ∃ (i : fin 2), (choose_ordering hs i : V) = x :=
begin
  refine ⟨λ h, _, by {rintros ⟨i,rfl⟩, simp}⟩,
  suffices h₀ : ∃ i, choose_ordering hs i = ⟨x,h⟩, from h₀.imp (λ i hi, subtype.coe_inj.mpr hi),
  unfold choose_ordering, split_ifs with h',
    exact ⟨0, @subsingleton.elim s (nat.card_eq_one_iff_unique.mp h').1 _ ⟨x,h⟩⟩,
  rw equiv.inv_fun_as_coe,
  exact equiv.surjective _ _,
end

-- Probably need to clean up some namespace stuff here ; we don't want graph.digraph.mk
-- Maybe even move these next two declarations to the digraph file.

/-- noncomputably make a digraph from undirected incidence information -/
def digraph.of_undir {V : Type u} {E : Type v} (u_inc : V → E → Prop)
  (h : ∀ e, nat.card {x | u_inc x e} = 1 ∨ nat.card {x | u_inc x e} = 2) : digraph V E :=
{ ends := λ i e, (choose_ordering (h e) i)}

/-- The digraph being built is actually the right thing -/
@[simp] lemma digraph.of_undir_inc_iff {V : Type u} {E : Type v} (u_inc : V → E → Prop)
  (h : ∀ e, nat.card {x | u_inc x e} = 1 ∨ nat.card {x | u_inc x e} = 2) {v : V} {e : E}:
(digraph.of_undir u_inc h).inc v e ↔ u_inc v e :=
by {show (∃ (i : fin 2), ↑(choose_ordering _ i) = v) ↔ u_inc v e, rw ←choose_ordering_works, refl}

/-- Make a graph from the digraph -/
def graph.mk {V : Type u} {E : Type v} (inc : V → E → Prop)
  (h : ∀ e, nat.card {x | inc x e} = 1 ∨ nat.card {x | inc x e} = 2) : graph V E :=
⟦digraph.of_undir inc h⟧

/-- The graph is the right thing  -/
@[simp] lemma graph.mk_inc_iff {V : Type u} {E : Type v} (u_inc : V → E → Prop)
  (h : ∀ e, nat.card {x | u_inc x e} = 1 ∨ nat.card {x | u_inc x e} = 2) {v : V} {e : E} :
  (graph.mk u_inc h).inc v e ↔ u_inc v e :=
digraph.of_undir_inc_iff u_inc h


--@[simp] lemma digraph

  -- (h : ∀ e, nat.card ({x | inc x e}) ∈ ({1,2} : set nat)) : graph V E :=
  -- by {
  --   classical,
  --   have D : digraph V E,
  --   have h2 : ∀ e, fintype {x | inc x e},
  --   intros e,
  --   specialize h e,
  --   simp at h,

  --   --cases h,
  --   -- ran into weird error with case split, going to sleep now

  --   -- the error is because you were trying to use tactics to produce a term that is not in Prop


  --   sorry,
  --   sorry,
  --   -- maybe have some arbitrary ordering on the vertices to start?
  --   -- then we get a natural ordering of vertex pairs
  --   -- in list.lean we have a noncomputable ordering on fintype
  --   -- need to show fin 2 is fintype (easy)
  --   -- then use `_root_.fintype.to_encodable`?
  --   -- is this the ordering that i want?

  --   exact ⟦D⟧,
  -- }

/-- structure dart (G : graph V E) extends V × V :=
(is_adj : G.adj fst snd)-/

structure dart (G : graph V E) : Type (max u v) :=
(head : V)
(tail : V)
(e : E)
(h : G.ends_are e head tail)
-- lemma saying that dart is same if parts of them are equal etc

-- make G implicit so it's d.reverse or whatever
def reverse_dart (G : graph V E) (d : G.dart) : G.dart :=
{ head := d.tail,
  tail := d.head,
  e := d.e,
  h := by exact G.ends_are_symm d.h }

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

-- lemma edges_nodup_of_support_nodup {G : graph V E} {p : G.walk} (h : p.support.nodup) :
--   p.edges.nodup :=
-- begin


--   sorry,
-- end

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

def regular (G : graph V E) (k : ℕ) : Prop := ∀ (v : V), G.deg v = k

lemma is_trail_def {G : graph V E} (p : G.walk) : p.is_trail ↔ p.edges.nodup :=
⟨walk.is_trail.edges_nodup, λ h, ⟨h⟩⟩

-- lemma is_path.mk' {u v : V} {p : G.walk} (h : p.support.nodup) : p.is_path :=
-- ⟨walk.edges_nodup_of_support_nodup h, h⟩


structure subgraph (G : graph V E) :=
(verts : set V)
(edges : set E)
(edge_sub : ∀ {e ∈ edges}, G.ends_set e ⊆ verts)

end conn

namespace subgraph


protected def coe {G : graph V E} (G' : subgraph G) : graph G'.verts G'.edges :=
begin
  apply graph.mk (λ v : G'.verts, λ e : G'.edges, G.inc v e),
  simp only [set.coe_set_of, set_coe.forall, subtype.coe_mk],
  intros x h,
  have h2 := G.edges_card,
  specialize h2 x,
  rw ends_set at h2,
  simp at h2,
  sorry,
--   unfold graph,
--   unfold graph at G,
--   have h := G'.edge_sub,
--   have h2 := digraph.is_equivalence G'.verts G'.edges,
--   have h3 := setoid.mk _ h2,


--   -- need to show edge orientation doesn't matter

--   sorry,
end

-- def connected (G' : subgraph G) : Prop := G'.coe.connected

end subgraph




-- end graph



-- inductive walk (G : graph V E) : V → V → Type (max u v)
-- | nil {x : V} : walk x x
-- | cons (a : V) {x y : V} (e : E) (h : G.ends_are e a x) (p : walk x y) : walk a y

-- namespace walk

-- variables {G : graph V E}{a b x y z : V} {e f g : E}

-- attribute [refl] walk.nil

-- def append : Π {x y z : V}, (G.walk x y) → (G.walk y z) → G.walk x z
-- | _ _ _ nil W := W
-- | _ _ _ (cons a e he W0) W := cons a e he (W0.append W)

-- def length : Π {x y : V}, (G.walk x y) → ℕ
-- | _ _ nil := 0
-- | _ _ (cons a e he W) := W.length.succ

-- protected def reverse_aux : Π {x y z : V}, G.walk x y → G.walk x z → G.walk y z
-- | _ _ _ nil W := W
-- | _ _ _ (cons a e he W0) W := reverse_aux W0 (cons _ _ (G.ends_are_symm he) W)

-- def reverse {x y : V} (W : G.walk x y) : (G.walk y x) := W.reverse_aux nil

-- --def nil {x y : V} : G.walk x y := nil

-- def is_nil : Π {x y : V}, G.walk x y → Prop
-- | _ _ nil := true
-- | _ _ _ := false

-- lemma nil_is_nil : (nil: G.walk x x).is_nil :=
-- by tauto

-- def vertex_support : Π {x y : V}, G.walk x y → list V
-- | x _ nil := [x]
-- | _ _ (@cons _ _ _ a _ _ e he W) := list.cons a W.vertex_support

-- def edge_support : Π {x y : V}, G.walk x y → list E
-- | _ _ nil := list.nil
-- | _ _ (cons a e he W) := list.cons e W.edge_support

-- def vertex_at : Π {x y : V}, G.walk x y → ℕ → V
-- | x _ nil _ := x
-- | x _ (cons a e he W) 0 := x
-- | _ _ (cons a e he W) (n+1) := W.vertex_at n

-- -- gives last edge if out of bounds
-- noncomputable def edge_at : Π {x y : V} (W : G.walk x y) (hW : ¬W.is_nil), ℕ → E
-- | _ _ nil hW _              := (hW nil_is_nil).elim
-- | _ _ (cons a e he W) _ 0     := e
-- | _ _ (cons a e he W) _ (n+1) := dite (W.is_nil) (λ _, e) (λ h, W.edge_at h n)

-- -- gives `none` if out of bounds
-- def edge_at' : Π {x y : V} (W : G.walk x y), ℕ → option E
-- | _ _ nil _                 := none
-- | _ _ (cons a e he W) 0       := e
-- | _ _ (cons a e he W) (n+1)   := W.edge_at' n

-- lemma eq_cons_of_ne_nil : Π {x y : V} {W : G.walk x y} (hW : ¬W.is_nil),
--   ∃ e b he (W₀ : G.walk b y), W = cons x e he W₀
-- | _ _ nil h := (h nil_is_nil).elim
-- | x y (@cons _ _ _ _ b _ e he W₀) _ := ⟨e, b, he, W₀, rfl⟩


-- --def edge_at'' : Π {x y : V} (W : G.walk x y) (hW : ¬W.is_nil), ℕ → E :=


-- --@[simp] lemma edge_at_cons : Π {x y : V}

-- @[simp] lemma length_nil : (nil : G.walk x x).length = 0 := rfl

-- @[simp] lemma length_cons (W : G.walk x y) {e : E} (h : G.ends_are e a x):
--   (cons a e h W).length = W.length.succ := rfl

-- @[simp] lemma vertex_support_nil : (nil : G.walk x x).vertex_support = [x] := rfl

-- @[simp] lemma edge_support_nil : (nil : G.walk x x).edge_support = [] := rfl

-- @[simp] lemma vertex_support_cons (W : G.walk x y) (he : G.ends_are e a x):
--   (cons a e he W).vertex_support = list.cons a W.vertex_support := rfl

-- @[simp] lemma edge_support_cons (W : G.walk x y) (he : G.ends_are e a x):
--   (cons a e he W).edge_support = list.cons e W.edge_support := rfl

-- @[simp] lemma reverse_nil : (nil : G.walk x x).reverse = nil := rfl

-- @[simp] lemma nil_vertex_at (x : V) (n : ℕ):
--   (nil : G.walk x x).vertex_at n = x :=
-- rfl

-- @[simp] lemma vertex_at_zero (W : G.walk x y) : W.vertex_at 0 = x :=
--   by {cases W; refl}

-- @[simp] lemma vertex_at_cons (W : G.walk x y) (he : G.ends_are e a x) (n : ℕ):
--   (cons a e he W).vertex_at n.succ = W.vertex_at n :=
-- rfl

-- @[simp] lemma vertex_at_ge_length (W : G.walk x y) {n : ℕ} (hn : W.length ≤ n):
--   W.vertex_at n = y :=
-- begin
--   induction W with a b c d e he W0 IH generalizing n,
--     refl,
--   induction n with n hn,
--   { rw length_cons at hn,
--     exact (nat.not_succ_le_zero _ hn).elim},
--   rw length_cons at hn,
--   rw vertex_at_cons,
--   exact IH (nat.le_of_succ_le_succ hn),
-- end

-- lemma nil_iff_length_eq_zero {W : G.walk x x} :
--   W.length = 0 ↔ W = nil :=
-- begin

-- end

-- lemma edge_at'_cons {W : G.walk x y} (he : G.ends_are e a x) (n : ℕ):
--   (cons a e he W).edge_at' n.succ = W.edge_at' n := rfl

-- lemma edge_at'_ne_nil (W : G.walk x y) (hW : ¬W.is_nil) (n : ℕ):
--   ∃ e, W.edge_at' n = some e :=
-- begin
--   rcases eq_cons_of_ne_nil hW with ⟨e,b,he, W₀,rfl⟩,
--   induction n with n,
--   { exact ⟨e, rfl⟩},
--   rw edge_at'_cons,

-- end

-- lemma exists_eq_cons_of_ne : Π {x y : V} (hne : x ≠ y) (W : G.walk x y),
--   ∃ (e : E) (z : V) (he : G.ends_are e x z) (W₀ : G.walk z y), W = cons e he W₀
-- | _ _ hne nil := (hne rfl).elim
-- | _ _ _ (cons e he W₀) := ⟨e, _, he, W₀, rfl⟩

-- lemma vertex_support_length (W : G.walk x y) :
--   W.vertex_support.length = W.length + 1 :=
-- by {induction W with a b c d e he W0 IH, simp, simp [IH]}

-- lemma edge_support_length (W : G.walk x y) :
--   W.edge_support.length = W.length :=
-- by {induction W with a b c d e he W0 IH, simp, simp [IH]}

-- lemma ends_edge_at (W : G.walk x y) :

-- lemma reverse_length (W : G.walk x y) :
--   W.reverse.length = W.length :=
-- by {sorry }


end graph
