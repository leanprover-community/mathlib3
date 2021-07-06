/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import data.finset.basic
import data.real.basic

/-!
# Szemerédi's Theorem, the hypergraph way

In this file, we prove Szemerédi's theorem following Tim Gowers' hypergraph proof.
-/

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

--def is_partite_function

--def is_quasi_random :

--lemma szemeredi_regularity {G : finset V → Prop} (hG : is_partite G 2) {ε : ℝ} (ε_pos : 0 < ε) :s
