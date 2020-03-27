import graph_theory.paths

universes v u

variables {V : Type u} (G : multigraph.{v+1} V)

def subgraph := Π a b, set (G.edge a b)

variables (G) (root : V)

class arborescence :=
(path : Π t, G.path root t)
(unique : ∀ t (p : G.path root t), p = path t)

variable (h : ∀ t, nonempty (G.path root t))

include root h
def geodesic_subgraph : subgraph G := sorry

-- This coercion doesn't work and I don't know why...
instance subgraph.graph : has_coe (subgraph G) (multigraph V) :=
⟨λ H, ⟨λ a b, H a b⟩⟩

--def geodesic_arborescence : arborescence ↑(geodesic_subgraph G root h) root := sorry
