import data.finset.basic
import data.real.basic

noncomputable theory
open_locale classical
variables {V : Type*} [fintype V] {k n r : ℕ}

def is_down_closed (G : finset V → Prop) : Prop :=
∀ x y : finset V, x ≤ y → G y → G x

structure hypergraph (V : Type*) :=
(hedges : set (finset V))

namespace hypergraph
variables (G : hypergraph V) {A B A' B' : finset V}

def edge (x y : V) : Prop := x ≠ y ∧ {x, y} ∈ G.hedges

noncomputable def edges_pair (A B : finset V) : finset (V × V) :=
(finset.product A B).filter (λ e, G.edge e.1 e.2)

lemma edges_pair_mono_left (hA : A' ⊆ A) (B : finset V) : G.edges_pair A' B ⊆ G.edges_pair A B :=
begin
  rintro e he,
  unfold edges_pair at ⊢ he,
  rw [finset.mem_filter, finset.mem_product] at ⊢ he,
  exact ⟨⟨hA he.1.1, he.1.2⟩, he.2.1, he.2.2⟩,
end

noncomputable def density_pair (A B : finset V) : ℝ := (G.edges_pair A B).card/(A.card * B.card)

noncomputable def density_diff (A B A' B' : finset V) : ℝ :=
abs (G.density_pair A B - G.density_pair A' B')

def uniform_pair (A B : finset V) (ε : ℝ) : Prop :=
∀ A' ⊆ A, ε * A.card ≤ A'.card → ∀ B' ⊆ B, ε * B.card ≤ B'.card →
  G.density_diff A B A' B' < ε

def partition_index (A B : finset V) (ε : ℝ) : ℝ :=
sorry

--def uniform_partition (P : finset (finset V))

end hypergraph

structure finpartition (V : Type*) :=
(parts : finset (finset V))
(disj : ∀ A B ∈ parts, ∀ x ∈ A, x ∈ B → A = B)
(cover : ∀ x, ∃ A ∈ parts, x ∈ A)

namespace finpartition
variables (P : finpartition V)

protected def card : ℕ := P.parts.card

def is_equipartition : Prop := ∀ A : finset V, A ∈ P.parts → A.card = (fintype.card V)/P.card ∨
A.card = nat_ceil ((fintype.card V)/P.card : ℝ)

def is_uniform (ε : ℝ) : Prop := sorry

noncomputable def index : ℝ := (1)/P.card^2

end finpartition

open hypergraph
variables {A B A' B' : finset V} (G : hypergraph V)

lemma LemmaB {δ : ℝ} (hAA' : A' ⊆ A) (hA' : (1 - δ) * A.card ≤ A'.card) (hAnemp : A.nonempty)
  (hBB' : B' ⊆ B) (hB' : (1 - δ) * B.card ≤ B'.card) (hBnemp : B.nonempty) :
  (G.density_diff A B A' B' : ℝ) ≤ 2 * δ :=
begin
  unfold density_diff density_pair,
  rw abs_le,
  simp,
  sorry
end

def upper_bound (t : ℕ) : ℕ → ℕ
  | nat.zero     := t
  | (nat.succ n) := (upper_bound n)*4^(upper_bound n)

lemma szemeredi_regularity {ε : ℝ} (ε_pos : 0 < ε) (ε_lt_one : ε < 1) (l : ℕ) :
  ∃ L : ℕ, L = L := --, ∀ V : Type* fintype V → L ≤ fintype.card V →
begin
  sorry
end
