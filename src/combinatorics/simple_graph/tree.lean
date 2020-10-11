import combinatorics.simple_graph.default


open finset
open_locale big_operators
universes u v

--variables {V : Type u}

section classical
open_locale classical

namespace simple_graph

section finite

variables (T : simple_graph) (h : is_tree T) [fintype (T.V)]

def leaf (v : T.V) : Prop := degree v = 1

/- Theorem 3: TFAE
    (a) T is a tree
    (b) There exists a unique path between any two distinct vertices of T
    (c) T is a connected graph on n vertices with n-1 edges
    (d) T is an acyclic graph on n vertices with n-1 edges -/

-- Proof outline:
/- Lemma 1: (a) → (b) : T is a tree → there exists a unique path between any two distinct vertices -/
/-lemma tree_unique_path (v w : T.V) (n m : ℕ) (p : path T n v w) (q : path T m v w) : p = q :=
begin
  unfold exists_path,
-- Subproof outline:
    -- let u,v be distinct vertices in T
    -- T is a tree, so a uv path p exists
        -- we already have uv path guaranteed by definition of tree
    -- suppose for contradiction that another path uv path q exists, p ≠ q (negation of eq_of_vertices_eq?)
    -- there exists w s.t. w ∈ p and w ∈ q, where w is the last vertex before p and q diverge (maybe make a lemma for this)
        -- shit this is gonna be tricky
        -- (this doesn't cover the edge case that u is adjacent to v, which is false by the condition that we have a simple graph. this is a problem. fix the definition somehow)
    -- p.last = q.last, so we must have a vertex w' in p,q (could be v) such that (figure out how to say this correctly) w'.tail ∈ p ∧ w'.tail ∈ q (also this should probably be a path lemma)
    -- now, this means that we can build a path from w back to itself using the segments w to w' in p and q (do we have reversible paths in path.lean?)
    sorry,
end-/


lemma tree_rm_edge_disconnected {v w : V T} (h : v ~g w) : ¬ is_connected ↟(delete_edge T h) :=
begin
    sorry,
end


end finite

end simple_graph

end classical
