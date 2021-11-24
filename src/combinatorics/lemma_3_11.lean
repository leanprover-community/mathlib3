import combinatorics.simple_graph.basic
import analysis.special_functions.pow
import data.fintype.card

variables {V : Type*} (G : simple_graph V)

open_locale big_operators classical
open finset fintype
noncomputable theory

structure indexed_partition (k : ℕ) {α : Type*} (s : finset α) :=
(parts : fin k → finset α)
(disjoint : set.pairwise_disjoint set.univ parts)
(sup_eq : univ.sup parts = s)
(nonempty : ∀ i, parts i ≠ ∅)

instance {k : ℕ} {α : Type*} (s : finset α) :
  has_coe_to_fun (indexed_partition k s) (λ _, fin k → finset α) :=
⟨indexed_partition.parts⟩

def simple_graph.edge_density (A B : finset V) : ℝ :=
  ((A.product B).filter (λ (ab : V × V), G.adj ab.1 ab.2)).card / (A.card * B.card)

def simple_graph.is_regular_pair (ε : ℝ) (X Y : finset V) : Prop :=
∀ (A ⊆ X) (B ⊆ Y), ε * X.card ≤ A.card → ε * Y.card ≤ B.card →
  |G.edge_density A B - G.edge_density X Y| ≤ ε

variables {k : ℕ} [fintype V] (P : indexed_partition k (@univ V _))

def simple_graph.is_regular_partition (ε : ℝ) : Prop :=
  ∑ ij in univ.filter (λ (ij : fin k × fin k), ¬G.is_regular_pair ε (P ij.1) (P ij.2)),
    ((P ij.1).card : ℝ) * (P ij.2).card ≤ ε * (card V)^2

def simple_graph.energy (U W : finset V) : ℝ :=
  U.card * W.card / (card V)^2 * (G.edge_density U W)^2

def indexed_partition.energy {k l : ℕ} {U W : finset V}
  (PU : indexed_partition k U) (PW : indexed_partition l W) : ℝ :=
∑ i, ∑ j, G.energy (PU i) (PW j)

lemma three_eight {k l : ℕ} {U W : finset V}
  (PU : indexed_partition k U) (PW : indexed_partition l W)
