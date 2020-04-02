import graph_theory.paths
import order.basic

/-!
  We define subgraphs and (anti-)arborescences, or directed rooted trees.
    We show that any directed multigraph has a subarborescence coverging to `root : V`,
  assuming that every vertex has some path to `root` to begin with. The proof essentially
  works by assigning to each non-root vertex a parent vertex that is closer to `root`.
-/

open path directed_multigraph

universes v

variables {V : Type*}
          (G : directed_multigraph.{v+1} V)
          (root : V)

/-- An arborescence converging to `root` has a unique path to root from every node. -/
class arborescence :=
(path : Π s, G.path s root) -- reversing this would be non-trivial due to how paths are defined
(unique : ∀ s (p : G.path s root), p = path s)

/-- A subgraph of a directed multigraph, obtained by deleting edges. -/
def subgraph := Π a b, set (G.edge a b) -- how to allow for Prop-valued edge-sets?
instance : inhabited (subgraph G) := ⟨λ a b, ∅⟩

variable {G}

/-- A subgraph is genuinely a graph. -/
def graph_of_subgraph (S : subgraph G) : directed_multigraph V :=
⟨λ s t, S s t⟩

variables {root} (H : ∀ s, nonempty (G.path s root))
include H

/-- A path to `root` of minimal length. -/
noncomputable def shortest_path (s : V) : G.path s root :=
well_founded.min (measure_wf $ λ p : G.path s root, length p) set.univ
  (@set.univ_nonempty _ (H s))

/-- The length of a path is at least the length of the shortest path -/
lemma shortest_path_spec (s : V) (p : G.path s root) :
  length (shortest_path H s) ≤ length p :=
begin
  have : ¬ (length p < length (shortest_path H s)),
  exact well_founded.not_lt_min (measure_wf _) set.univ _ trivial,
  simpa using this,
end

/-- The shortest path from a non-root vertex is not nil.
We use this a to extract the head of the shortest path -/
lemma nnil {s} (h : s ≠ root) : ¬ is_nil (shortest_path H s) :=
by { cases shortest_path H s, { simpa using h }, { simp }, }

/-- The geodesic subgraph. For each non-root vertex, there is an edge to a parent:
some vertex that is closer to `root`. -/
inductive geodesic_subgraph : Π (s t : V) (e : G.edge s t), Prop
| intro (s : V) (h : s ≠ root) : geodesic_subgraph s _ (head (nnil H h))

/-- Can we find a better name for this? -/
def geodesic_graph : directed_multigraph V := graph_of_subgraph (geodesic_subgraph H)

/-- Distance to `root`: we use this to do well-founded recursion -/
noncomputable def height (s : V) : ℕ := length $ shortest_path H s

/-- The parent really is closer to `root` -/
lemma parent_height_lt {s} (h : s ≠ root) :
  height H (mid $ nnil H h) < height H s := begin
  have : height H _ ≤ length (tail $ nnil H h),
  { apply shortest_path_spec },
  apply lt_of_le_of_lt this,
  have : height H s = length (tail $ nnil H h) + 1,
  { apply length_eq_length_tail_plus_one },
  rw this,
  exact nat.lt.base _
end

variable [decidable_eq V]

/-- Following edges to parents gives a path to `root`. -/
noncomputable def geodesic_path : Π s, path (geodesic_graph H) s root
| s := dite (s = root) (λ h, path_of_eq h)
       (λ h, have _ := parent_height_lt H h,
            ⟨_, geodesic_subgraph.intro H s h⟩ :: geodesic_path _)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (height H)⟩], }

/-- The recursive definition of the path to `root`. -/
lemma geodesic_path_def : Π s, geodesic_path H s = dite (s = root) (λ h, path_of_eq h)
       (λ h, ⟨_, geodesic_subgraph.intro H s h⟩ :: geodesic_path H _) :=
well_founded.fix_eq _ _

/-- By induction, there is no other path to `root`. -/
lemma geodesic_path_unique (s) (p : path (geodesic_graph H) s root) :
  p = geodesic_path H s :=
@based_rec_on V (geodesic_graph H) root
(λ s p, p = geodesic_path H s) s p
(by { rw [geodesic_path_def, dif_pos rfl], simpa })
begin
  intros s m e l h,
  cases e with e p,
  cases p with _ n,
  rw geodesic_path_def,
  rw dif_neg n,
  simpa using h,
end

/-- Putting all this together, we've obtained an arborescence! -/
noncomputable instance geodesic_arboresence : arborescence (geodesic_graph H) root :=
{ path := geodesic_path H,
  unique := geodesic_path_unique H}
