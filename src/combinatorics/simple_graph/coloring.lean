import combinatorics.simple_graph.basic
import data.nat.lattice

universes u v

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

abbreviation proper_coloring (α : Type v) := G →g complete_graph α

variables {G} {α : Type v} (C : G.proper_coloring α)

def proper_coloring.color (v : V) : α := C v

lemma proper_coloring.valid (v w : V) (h : G.adj v w) : C.color v ≠ C.color w :=
  C.map_rel h

@[pattern]
def proper_coloring.mk (color : V → α) (h : ∀ {v w : V}, G.adj v w → color v ≠ color w) :
  G.proper_coloring α := ⟨color, @h⟩

/-- Whether a graph can be colored by at most `n` colors. -/
def colorable (G : simple_graph V) (n : ℕ) : Prop :=
∃ (α : Type*) [fintype α] (C : G.proper_coloring α), by exactI fintype.card α ≤ n

/-- If `G` isn't colorable with finitely many colors, this will be 0. -/
noncomputable def chromatic_number (G : simple_graph V) :=
  Inf { n : ℕ | G.colorable n }

def complete_graph.of_embedding {α β : Type*} (f : α ↪ β) : complete_graph α ↪g complete_graph β :=
{ to_fun := f,
  inj' := f.inj',
  map_rel_iff' := by simp }

lemma colorable_if_nonempty_fin_coloring (G : simple_graph V) (n : ℕ) :
  G.colorable n ↔ nonempty (G.proper_coloring (fin n)) :=
begin
  split,
  { rintro ⟨α, αf, C, h⟩,
    tactic.unfreeze_local_instances,
    let f := (fintype.equiv_fin α).to_embedding.trans (fin.cast_le h).to_embedding,
    exact ⟨(complete_graph.of_embedding f).to_hom.comp C⟩, },
  { rintro ⟨C⟩,
    exact ⟨ulift (fin n), by apply_instance,
      (complete_graph.of_embedding equiv.ulift.symm.to_embedding).to_hom.comp C, by simp⟩, },
end

lemma proper_coloring.chromatic_number_le [fintype α] (C : G.proper_coloring α) :
  G.chromatic_number ≤ fintype.card α :=
begin
  sorry
end

lemma proper_coloring.zero_le_chromatic_number [nonempty V] [fintype α] (C : G.proper_coloring α) :
  0 < G.chromatic_number :=
begin
  sorry
end

lemma proper_coloring.chromatic_number_minimal [fintype α] (C : G.proper_coloring α)
  (h : ∀ (C' : G.proper_coloring α), set.range C'.color = set.univ) :
  G.chromatic_number = fintype.card α :=
begin
  sorry
end

end simple_graph
