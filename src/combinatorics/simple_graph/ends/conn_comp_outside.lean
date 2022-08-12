import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import category_theory.functor.basic

open function
open finset
open set
open classical
open simple_graph.walk
open relation

universes u v w



noncomputable theory

--local attribute [instance] prop_decidable

namespace simple_graph


variables  {V : Type u}
           (G : simple_graph V)
           [Gpc : preconnected G]
           (K : finset V)

section ends

def conn_comp_outside : Type u :=
((⊤ : G.subgraph).delete_verts K).coe.connected_component

def conn_comp_outside.to_vertex_set {G : simple_graph V} {K : finset V} (C : conn_comp_outside G K) :=
  {v // connected_component_mk _ v = C}

/- Alternative defintion. At this point, it is hard to tell which would be better -/
def conn_comp_outside.to_set (K : finset V) (C : conn_comp_outside G K) : set V :=
  { v : V | ∃ (p:v ∉ K), ((⊤ : G.subgraph).delete_verts K).coe.connected_component_mk (⟨v,by {simp,exact p}⟩) = C }

-- TODO: Define and prove theorems about infinite connected components
def inf_conn_comp_outside :=
 {C : G.conn_comp_outside K // infinite C.to_vertex_set}

def fin_conn_comp_outside :=
  {C : G.conn_comp_outside K // finite C.to_vertex_set}

namespace conn_comp_outside


def component_of (v : V) (hv : v ∉ K) :
  conn_comp_outside G K := sorry

-- TODO: Make an analog of the above function for any connected set.
-- TODO: Show that the corresponding component contains the set.


-- TODO: Define the boundary and related lemmas
def bdry := {v : V | v ∉ K ∧ ∃ k ∈ K, G.adj v k}

lemma bdry_finite [locally_finite G] : finite (bdry G K) := sorry

/- This is the portion of the connected component that is a part of the boundary -/
def border (C : conn_comp_outside G K) : set V := sorry

-- TODO: Show that the boundary is precisely the union of all the borders.

lemma finite_components [Glf : locally_finite G] [Gpc : preconnected G] (K : finset V) :
  fintype (conn_comp_outside G K) :=
begin
  by_cases Knempty : K.nonempty,
  {
     refine fintype_of_not_infinite _,
     intro hinf,
     sorry -- needs some lemmas about boundary
  },
  { rw [finset.not_nonempty_iff_eq_empty] at Knempty,
    subst Knempty,
    dsimp [conn_comp_outside, simple_graph.subgraph.delete_verts],
    have : (univ : set V) \ ∅ = univ := sdiff_bot,
    rw [this, ← simple_graph.induce_eq_coe_induce_top],
    refine ⟨{_}, _⟩,
    sorry, -- need to use `Gpc` here
    sorry
   }
end

lemma nonempty_components (Ginf : (@set.univ V).infinite) (K : finset V) :
  nonempty (conn_comp_outside G K) :=
begin
  by_contradiction,
  rw [not_nonempty_iff, conn_comp_outside] at h,
  apply Ginf, clear Ginf,
  sorry, -- needs the fact that the set of vertices is the union of `K` and all the connected components
end




lemma conn_comp_outside_back_unique {K L : finset V} (h : K ⊆ L) :
∀ C : conn_comp_outside G L,
  ∃! D : conn_comp_outside G K,
    (to_set G L C) ⊆ (conn_comp_outside.to_set G K D) := sorry

-- this is the `bwd_map`
def conn_comp_outside_back {K L : finset V} (h : K ⊆ L) (C : conn_comp_outside G L) : conn_comp_outside G K :=
  classical.some (exists_of_exists_unique (conn_comp_outside_back_unique G h C))

-- TODO(?): Maybe write a function taking a connected set disjoint from `K`
-- and expanding it to the connected component that it is contained in

def conn_comp_outside_back.iff {K L : finset V} (h : K ⊆ L) (C : conn_comp_outside G L) (D : conn_comp_outside G K):
  conn_comp_outside_back G h C = D ↔ (conn_comp_outside.to_set G L C) ⊆ (conn_comp_outside.to_set G K D) :=
begin
  split,
  { rintro equ, induction equ, exact (exists_of_exists_unique (conn_comp_outside_back_unique G h C)).some_spec},
  { exact unique_of_exists_unique (conn_comp_outside_back_unique G h C) (exists_of_exists_unique (conn_comp_outside_back_unique G h C)).some_spec},
end

lemma conn_comp_outside_back.refl (K : finset V) (C : conn_comp_outside G K) :
  conn_comp_outside_back G (finset.subset.refl K) C = C :=
unique_of_exists_unique
  (conn_comp_outside_back_unique G (finset.subset.refl K) C)
  (classical.some_spec (exists_of_exists_unique (conn_comp_outside_back_unique G (finset.subset.refl K) C)))
  (set.subset.refl (conn_comp_outside.to_set G K C))

lemma conn_comp_outside_back.comm  {J K L : finset V} (k : J ⊆ K) (h : K ⊆ L) (C : conn_comp_outside G L) :
  conn_comp_outside_back G k (conn_comp_outside_back G h C) = conn_comp_outside_back G (k.trans h) C :=
unique_of_exists_unique
  (conn_comp_outside_back_unique G (k.trans h) C)
  ((exists_of_exists_unique (conn_comp_outside_back_unique G h C)).some_spec.trans
     (exists_of_exists_unique (conn_comp_outside_back_unique G k (conn_comp_outside_back G h C))).some_spec)
  (classical.some_spec (exists_of_exists_unique (conn_comp_outside_back_unique G (k.trans h) C)))

-- TODO: An infinite graph has at least one infinite connected component
-- TODO: A locally finite graph has finitely many infinite connected components

-- def ends_system := category_theory.functor.mk (conn_comp_outside G) (conn_comp_outside_back G)

-- TODO: Mapping of connected sets under homomorphisms
-- TODO: Show that components are preserved under isomorphisms

-- Returns K ∪ (all finite connected components in the complement)
def conn_comp_outside.extend_fin [Glf : locally_finite G] (K : finset V) : finset V := sorry

-- TODO: Build all the associated lemmas. Mainly prove that the resulting set of connected components are precisely the infinite connected components of the original graph.

-- TODO: Prove lemmas about cofinite infinite components

end conn_comp_outside

end ends

end simple_graph
