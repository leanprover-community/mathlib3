import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.hamiltonian
import combinatorics.simple_graph.matching

variables {V : Type*} (G : simple_graph V)

namespace simple_graph

@[simps]
def from_edge_set (s : set (sym2 V)) : simple_graph V :=
{ adj := λ x y, x ≠ y ∧ ⟦(x, y)⟧ ∈ s,
  symm := λ x y h, by rwa [ne_comm, sym2.eq_swap] }

lemma edge_set_gc {V : Type} : galois_connection edge_set (@from_edge_set V) :=
λ G s, ⟨λ hs v w h', ⟨G.ne_of_adj h', hs (by simpa)⟩, λ hG e, sym2.ind (λ x y h, (hG h).2) e⟩

def edge_set_gi {V : Type*} : galois_coinsertion edge_set (@from_edge_set V) :=
edge_set_gc.to_galois_coinsertion (λ G x y h, h.2)

@[simp] lemma subgraph.inf_adj {H₁ H₂ : subgraph G} {v w : V} :
  (H₁ ⊓ H₂).adj v w ↔ H₁.adj v w ∧ H₂.adj v w := iff.rfl

variables [decidable_eq V]

def is_cycle (s : set (sym2 V)) : Prop :=
∃ (u : V) (p : G.walk u u), s = p.edges.to_finset ∧ p.is_cycle

def is_path (s : set (sym2 V)) : Prop :=
∃ (u v : V) (p : G.walk u v), s = p.edges.to_finset ∧ p.is_path

lemma is_path_def {s : set (sym2 V)} :
  G.is_path s ↔ ∃ (u v : V) (p : G.walk u v), s = p.edges.to_finset ∧ p.is_path :=
iff.rfl

lemma is_cycle_def {s : set (sym2 V)} :
  G.is_cycle s ↔ ∃ (u : V) (p : G.walk u u), s = p.edges.to_finset ∧ p.is_cycle :=
iff.rfl

lemma is_cycle.finite {s : set (sym2 V)} (hs : G.is_cycle s) : s.finite :=
begin
  obtain ⟨u, w, rfl, -⟩ := hs,
  exact finset.finite_to_set _,
end

lemma is_path.finite {s : set (sym2 V)} (hs : G.is_path s) : s.finite :=
begin
  obtain ⟨u, v, w, rfl, -⟩ := hs,
  exact finset.finite_to_set _,
end

lemma list.to_finset_eq_empty_iff {α : Type*} [decidable_eq α] :
  ∀ (l : list α), l.to_finset = ∅ ↔ l = list.nil
| list.nil := by simp
| (list.cons x xs) := by simp

def is_disjoint_union_of_cycles (s : set (sym2 V)) : Prop :=
∃ (t : set (set (sym2 V))), ⋃₀ t = s ∧ t.pairwise_disjoint id ∧
  ∀ i ∈ t, G.is_cycle (i : set (sym2 V))

def is_disjoint_union_of_paths_and_cycles (s : set (sym2 V)) : Prop :=
∃ (t : set (set (sym2 V))), ⋃₀ t = s ∧ t.pairwise_disjoint id ∧
  ∀ i ∈ t, G.is_path i ∨ G.is_cycle i

lemma edge_set_mono {H₁ H₂ : subgraph G} (h : H₁ ≤ H₂) : H₁.edge_set ≤ H₂.edge_set :=
λ e, sym2.ind h.2 e

@[simp] lemma edge_set_bot : (⊥ : subgraph G).edge_set = ∅ :=
set.eq_empty_iff_forall_not_mem.2 (sym2.ind (by simp))

@[simp] lemma edge_set_inf {H₁ H₂ : subgraph G} : (H₁ ⊓ H₂).edge_set = H₁.edge_set ∩ H₂.edge_set :=
set.ext (λ e, sym2.ind (by simp) e)

lemma disjoint.subgraph_edge_set {H₁ H₂ : subgraph G}
  (h : disjoint H₁ H₂) : disjoint H₁.edge_set H₂.edge_set :=
by simpa using edge_set_mono _ h

-- lemma disjoint_union_of_paths_and_cycles_iff_aux
--   (G' : subgraph G) [∀ v, fintype (G'.neighbor_set v)] :
--     G.is_disjoint_union_of_paths_and_cycles G'.edge_set ↔
--       ∀ x ∈ G'.verts, G'.degree x ≤ 2 :=
-- begin

-- end

open_locale classical

@[simp] lemma set_coe_is_empty_iff {α : Type*} (s : set α) : is_empty s ↔ s = ∅ :=
begin
  rw [is_empty_iff, set.eq_empty_iff_forall_not_mem],
  apply set_coe.forall,
end

lemma coe_set_card_iff {α : Type*} (s : set α) [fintype s] : fintype.card s = 0 ↔ s = ∅ :=
begin
  rw fintype.card_eq_zero_iff,
  simp,
end

lemma support_eq_empty_iff_edge_set_eq_empty (G' : subgraph G) :
  G'.support = ∅ ↔ G'.edge_set = ∅ :=
by simp [set.eq_empty_iff_forall_not_mem, subgraph.mem_support, sym2.forall]

lemma edge_set_eq_empty_of_verts_eq_empty (G' : subgraph G) (hG' : G'.verts = ∅) :
  G'.edge_set = ∅ :=
(support_eq_empty_iff_edge_set_eq_empty _ G').1 (set.subset_eq_empty G'.support_subset_verts hG')

lemma disjoint_union_of_paths_and_cycles_iff [fintype V] :
  ∀ (G' : subgraph G), G.is_disjoint_union_of_paths_and_cycles G'.edge_set ↔
    ∀ x ∈ G'.verts, G'.degree x ≤ 2 :=
begin
  suffices : ∀ (n : ℕ), ∀ (G' : subgraph G), fintype.card G'.verts = n →
    (G.is_disjoint_union_of_paths_and_cycles G'.edge_set ↔ ∀ x ∈ G'.verts, G'.degree x ≤ 2),
  { intros G',
    exact this _ G' rfl },
  intro n,
  induction n with n ih,
  { intros G' hG',
    rw coe_set_card_iff at hG',
    rw [hG', edge_set_eq_empty_of_verts_eq_empty _ _ hG'],
    simp only [forall_false_left, set.mem_empty_eq, implies_true_iff, iff_true],
    exact ⟨∅, by simp⟩ },
  intros G' hG',
  simp only [finset.filter_congr_decidable, fintype.card_of_finset] at hG',
end

lemma two_perfect_matchings_induce_disjoint_union_of_cycles
  {m₁ m₂ : subgraph G} (hm₁ : m₁.is_perfect_matching) (hm₂ : m₂.is_perfect_matching) :
  G.is_disjoint_union_of_cycles (m₁.edge_set ∪ m₂.edge_set) :=
sorry

def disjoint_perfect_matchings : Prop :=
∀ m₁ m₂ : subgraph G, m₁.is_perfect_matching → m₂.is_perfect_matching →
  disjoint m₁.edge_set m₂.edge_set

lemma two_perfect_matchings_induce_cycle
  (hG : G.disjoint_perfect_matchings)
  {m₁ m₂ : subgraph G} (hm₁ : m₁.is_perfect_matching) (hm₂ : m₂.is_perfect_matching) :
  G.is_cycle (m₁.edge_set ∪ m₂.edge_set) :=
sorry


end simple_graph
