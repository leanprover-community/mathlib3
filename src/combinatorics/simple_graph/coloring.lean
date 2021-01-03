import combinatorics.simple_graph.basic
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

def nat.colorable (G : simple_graph V) (n : ℕ)  :
  Prop := G.colorable (fin n)

-- if V isn't finite then there won't necessarily be a chromatic number
lemma fintype_colorable [fintype V] [decidable_eq V] (G : simple_graph V) : ∃ (n : ℕ), nat.colorable G n :=
begin
  use fintype.card V,
  rw nat.colorable,
  rw colorable, -- use bijection from V to (fin (fintype.card V))
  have f := fintype.equiv_fin V,
  apply nonempty_of_exists,

  --have h := equiv.injective f.to_fun,
  --ext v w,
  sorry,
  sorry,
end

-- ∃ (n : ℕ), G.nat.colorable n →
  -- ∀ (k : ℕ), G.nat.colorable k → n ≤ k
--def chromatic_number (G : simple_graph V) : nat := nat.find (λ (k : ℕ))

end simple_graph
