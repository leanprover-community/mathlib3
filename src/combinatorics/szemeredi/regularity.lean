import data.finset.basic
import data.real.basic

open_locale classical
variables {V : Type*} {k n r : ℕ}

def is_down_closed (G : finset V → Prop) : Prop :=
∀ x y : finset V, x ≤ y → G y → G x

structure hypergraph (V : Type*) :=
(edges : set (finset V))

namespace hypergraph
variables (G : hypergraph V) {A B A' B' : finset V}

noncomputable def edges_pair (A B : finset V) : finset (V × V) :=
(finset.product A B).filter (λ e, e.1 ≠ e.2 ∧ {e.1, e.2} ∈ G.edges)

lemma edges_pair_mono_left (hA : A' ⊆ A) (B : finset V) : G.edges_pair A' B ⊆ G.edges_pair A B :=
begin
  rintro e he,
  unfold edges_pair at ⊢ he,
  rw finset.mem_filter at ⊢ he,
  refine ⟨⟩
  have := finset.m
end

noncomputable def density_pair (A B : finset V) : ℝ := (G.edges_pair A B).card/(A.card * B.card)

noncomputable def density_diff (A B A' B' : finset V) : ℝ :=
abs (G.density_pair A B - G.density_pair A' B')

def uniform_pair (A B : finset V) (ε : ℝ) : Prop :=
∀ A' ⊆ A, ε * A.card ≤ A'.card → ∀ B' ⊆ B, ε * B.card ≤ B'.card →
  G.density_diff A B A' B' < ε

--def uniform_partition (P : finset (finset V))

end hypergraph

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
