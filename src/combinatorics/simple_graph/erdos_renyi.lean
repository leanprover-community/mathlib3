/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import combinatorics.simple_graph.basic
import probability.density
import probability.probability_mass_function.constructions
import probability.notation

/-!
# Erdös-Rényi

## Notes

This is draft. Bhavik has a much better version somewhere for Kahn-Kalai.

-/

noncomputable theory

open measure_theory pmf
open_locale big_operators classical measure_theory probability_theory nnreal

variables {α Ω : Type*} [measure_space Ω] [is_probability_measure (ℙ : measure Ω)]

def erdos_renyi (α : Type*) [fintype α] (p : ℝ≥0) (hp : p ≤ 1) : pmf (simple_graph α) :=
of_fintype (λ G, p ^ G.edge_finset.card * (1 - p) ^ ((fintype.card α).choose 2 - G.edge_finset.card))
begin

end
