import combinatorics.simple_graph.basic
import data.fin
import tactic.fin_cases

namespace simple_graph
universes u v
variables {V : Type u} (G : simple_graph V)

/-- A graph `G` is `β`-colorable if there is an assignment of elements of `β` to
vertices of `G` (allowing repetition) such that adjacent vertices have
distinct colors. -/
@[ext]
structure coloring (β : Type v) :=
(color : V → β)
(valid : ∀ ⦃v w : V⦄, G.adj v w → color v ≠ color w)

/-- A graph `G` is `β`-colorable if there is a `β`-coloring. -/
def colorable (β : Type v) : Prop := nonempty (G.coloring β)

def trivial_coloring : coloring G V :=
{ color := λ x, x,
  valid := λ x y, ne_of_adj _ }

instance : inhabited (coloring G V) := ⟨trivial_coloring G⟩

namespace coloring
variables {G} {β : Type v} (f : G.coloring β)

/-- Given the mere existence of a `β`-coloring, extract it. -/
noncomputable def some_coloring (h : G.colorable β) : G.coloring β := classical.choice h

/-- The set of vertices with the given color. -/
def color_set (c : β) : set V := f.color ⁻¹' {c}

def color_finset (c : β) [fintype (f.color_set c)] : finset V := (f.color_set c).to_finset

@[simp]
lemma mem_color_set_iff (c : β) (v : V) : v ∈ f.color_set c ↔ f.color v = c :=
iff.rfl

/--
If `V` is a `fintype` with `decidable_eq`, then this gives that `color_class f c` is a `fintype`.
-/
instance color_class.decidable_pred (c : β) [decidable_eq β] : decidable_pred (f.color_set c) :=
by { intro v, change decidable (f.color v = c), apply_instance }

lemma color_set_disjoint (c c' : β) (hn : c ≠ c') : f.color_set c ∩ f.color_set c' = ∅ :=
begin
  ext,
  simp only [set.mem_empty_eq, mem_color_set_iff, set.mem_inter_eq, not_and, iff_false],
  rintro rfl,
  exact hn,
end

end coloring

/--
Given a coloring and a larger set of colors, one can extend the coloring set.
-/
def extend_coloring {β β' : Type*} (f : β ↪ β') : coloring G β ↪ coloring G β' :=
{ to_fun := λ F,
  { color := λ v, f (F.color v),
    valid := λ v w h hc, F.valid h (f.injective hc) },
  inj' := λ F F' h,
  begin
    ext,
    apply f.injective,
    simp only at h,
    exact congr_fun h x,
  end }

lemma colorable_of_embedding {β β' : Type*} (f : β ↪ β') : G.colorable β → G.colorable β' :=
nonempty.map (G.extend_coloring f)

lemma colorable_iff_of_equiv {β β' : Type*} (e : β ≃ β') : G.colorable β ↔ G.colorable β' :=
⟨colorable_of_embedding G e.to_embedding, colorable_of_embedding G e.symm.to_embedding⟩

def nat_colorable (G : simple_graph V) (n : ℕ) : Prop := G.colorable (fin n)

lemma colorable_of_nat_colorable {G : simple_graph V} {β : Type*} [fintype β] :
  G.nat_colorable (fintype.card β) ↔ G.colorable β :=
begin
  classical,
  rcases fintype.equiv_fin β with ⟨e⟩,
  apply colorable_iff_of_equiv _ e.symm
end

-- if V isn't finite then there won't necessarily be a chromatic number
lemma fintype_colorable [fintype V] (G : simple_graph V) :
  ∃ (n : ℕ), nat_colorable G n :=
begin
  refine ⟨fintype.card V, _⟩,
  rw colorable_of_nat_colorable,
  exact ⟨trivial_coloring G⟩,
end

open_locale classical

noncomputable def chromatic_number [fintype V] (G : simple_graph V) : ℕ :=
nat.find (fintype_colorable G)

lemma chromatic_number_colorable [fintype V] (G : simple_graph V) :
  G.nat_colorable G.chromatic_number :=
nat.find_spec _

lemma colorable_iff_le_chromatic_number [fintype V] {n : ℕ} :
  G.chromatic_number ≤ n ↔ nat_colorable G n :=
begin
  split,
  { intro h,
    apply colorable_of_embedding _ (fin.cast_le h).to_embedding G.chromatic_number_colorable },
  { apply nat.find_min' _ }
end

end simple_graph
