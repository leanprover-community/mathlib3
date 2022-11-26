import combinatorics.simple_graph.basic
import data.set.finite
import data.sym.sym2

universes u v w

namespace simple_graph

variable (V : Type*)

lemma from_edge_set_le_from_edge_set_iff {s t : set (sym2 V)} :
  from_edge_set s ≤ from_edge_set t ↔ (s \ {e | e.is_diag}) ⊆ (t \ {e | e.is_diag}) :=
begin
  split,
  { rintros h ⟨u,v⟩,
    change ⟦(u,v)⟧ ∈ s \ set_of sym2.is_diag → ⟦(u,v)⟧ ∈ t \ set_of sym2.is_diag,
    simp { contextual := tt },
    exact λ uvs ne, (h ⟨uvs,ne⟩).left, },
  { rintro h u v a, refine ⟨_,a.ne⟩,
    refine (h _).left, exact ⟨a.left,a.right⟩, },
end

lemma from_edge_set_eq_from_edge_set_iff {s t : set (sym2 V)} :
  from_edge_set s = from_edge_set t ↔ (s \ (set_of sym2.is_diag)) = (t \ (set_of sym2.is_diag)) :=
by simp [le_antisymm_iff, from_edge_set_le_from_edge_set_iff]

lemma le_from_edge_set_iff  (s : set (sym2 V)) (G : simple_graph V) :
  G ≤ from_edge_set s ↔ G.edge_set ⊆ s :=
begin
  split,
  { rintro h ⟨u,v⟩ a, exact (h a).left, },
  { rintro h u v a, refine ⟨h _, a.ne⟩, exact a,},
end

lemma from_edge_set_le_iff (s : set (sym2 V)) (G : simple_graph V) :
  from_edge_set s ≤ G ↔ (s \ (set_of sym2.is_diag)) ⊆ G.edge_set :=
begin
  nth_rewrite 0 ←from_edge_set_edge_set G,
  rw from_edge_set_le_from_edge_set_iff,
  have : G.edge_set \ set_of sym2.is_diag = G.edge_set, by
  { ext ⟨u,v⟩, simp only [set.mem_diff, set.mem_set_of_eq, and_iff_left_iff_imp], exact adj.ne, },
  rw this,
end

lemma from_edge_set_le {s : set (sym2 V)} {G : simple_graph V} (h : s ⊆ G.edge_set) :
  from_edge_set s ≤ G :=
begin
  rw from_edge_set_le_iff,
  exact (set.diff_subset _ _).trans h,
end

lemma from_edge_set_eq_iff (s : set (sym2 V)) (G : simple_graph V) :
  from_edge_set s = G ↔ (s \ {e | e.is_diag}) = G.edge_set :=
begin
  nth_rewrite 0 ←from_edge_set_edge_set G,
  rw from_edge_set_eq_from_edge_set_iff,
  have : G.edge_set \ set_of sym2.is_diag = G.edge_set, by
  { ext ⟨u,v⟩, simp only [set.mem_diff, set.mem_set_of_eq, and_iff_left_iff_imp], exact adj.ne, },
  rw this,
end



end simple_graph

@[simp] lemma order.boolean_algebra.le_sdiff {α : Type u} {x y z : α} [generalized_boolean_algebra α] :
  x ≤ y \ z ↔ x ≤ y ∧ disjoint x z :=
begin
  split,
  { rintro h,
    exact ⟨h.trans sdiff_le, (@disjoint_sdiff_self_left _ z y _).mono_left h⟩, },
  { rintro ⟨h,k⟩,
    transitivity x \ z,
    { suffices : x ≤ x \ (x ⊓ z), { simpa [sdiff_inf] using this, },
      rw disjoint_iff at k,
      simp only [k, sdiff_bot], },
    { simp only [sdiff_le_iff, sup_sdiff_self],
      apply h.trans le_sup_right, }, },
end
