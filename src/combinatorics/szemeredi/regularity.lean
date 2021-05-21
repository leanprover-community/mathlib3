import data.finset.basic
import data.real.basic

variables {V : Type*} {G : finset V → Prop} {k n r : ℕ}

structure partite_hypergraph (r : ℕ) :=
(G : finset V → Prop)
(ι : Type*)
(ι_fin : fintype ι)
(ι_card : fintype.card ι = r)
(X : ι → finset (finset V))
(partite : ∀ x₁ x₂, G x₁ → G x₂ → ∀ i₁ i₂, x₁ ∈ X i₁ → x₂ ∈ X i₂ → i₁ = i₂)

def is_uniform_hypergraph (G : finset V → Prop) (k : ℕ) : Prop :=
∀ x : finset V, G x → x.card = k

def is_partite (G : finset V → Prop) (k : ℕ) : Prop :=
∃ (ι : Type*) (X : ι → finset (finset V)), ∀ x₁ x₂, G x₁ → G x₂ →
  ∀ i₁ i₂, x₁ ∈ X i₁ → x₂ ∈ X i₂ → i₁ = i₂

def is_down_closed (G : finset V → Prop) : Prop :=
∀ x y : finset V, x ≤ y → G y → G x
--def is_partite_function

--def is_quasi_random :

--lemma szemeredi_regularity {G : finset V → Prop} (hG : is_partite G 2) {ε : ℝ} (ε_pos : 0 < ε) :

def edges_pair (A B : finset V) : ℕ := sorry

def density_pair (A B : finset V) : ℚ := (edges_pair A B : ℚ)/(A.card * B.card)

def density_diff (A B A' B' : finset V) : ℚ := abs (density_pair A B - density_pair A' B')

def uniform_pair (A B : finset V) (ε : ℝ): ∀ A' ⊆ A, ε * A.card ≤ A'.card → ∀ B' ⊆ B,
  ε * B.card ≤ B'.card → density_diff A B A' B' < ε

def uniform_partition (P : finset (finset V))

variables {A B A' B' : finset V}

lemma LemmaB {δ : ℝ} (hAA' : A' ⊆ A) (hA' : ε * A.card ≤ A'.card) (hAnemp : A.nonempty)
  (hBB' : B' ⊆ B) (hB' : (1 - δ) * B.card ≤ B'.card) (hBnemp : B.nonempty) :
  density_diff A B A' B' ≤ 2 * δ :=
begin
  sorry
end
