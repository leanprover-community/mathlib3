import .digraph

open_locale classical big_operators


noncomputable theory

variables {V E : Type*}

instance graph.setoid (V E : Type*) : setoid (digraph V E) :=
  setoid.mk _ (digraph.is_equivalence V E)

def graph (V E : Type*): Type* :=
  quotient (graph.setoid V E)

namespace graph

variables {G : graph V E} {u v w : V} {e f : E}

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

class finite_at (G : graph V E) (v : V) :=
  (fin : fintype (G.edge_nhd v))

lemma adj_symm (G : graph V E) (u v : V):
  G.adj u v → G.adj v u :=
by {induction G, exact digraph.adj_symm _ _, exact λ h, rfl}

lemma other_end_idem {G : graph V E} (v : V) (e : E):
  G.other_end (G.other_end v e) e = v :=
by {induction G, exact digraph.other_end_idem v e, refl}

lemma other_end_adj {G : digraph V E}{u : V}{e : E}(hve : G.inc u e):
  G.adj u (G.other_end u e) :=
by {induction G, exact digraph.other_end_adj hve}

theorem handshake [fintype V] [fintype E]:
  ∑ᶠ (v : V), G.deg v = 2 * (fintype.card E) :=
by {induction G, exact digraph.handshake G, refl}


end graph
