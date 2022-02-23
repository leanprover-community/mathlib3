/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.star.basic
import analysis.normed_space.spectrum

/-! # Spectral properties in C⋆-algebras
In this file, we establish various propreties related to the spectrum of elements in C⋆-algebras.
-/

section unitary_spectrum

variables
{𝕜 : Type*} [normed_field 𝕜]
{E : Type*} [normed_ring E] [star_ring E] [cstar_ring E]
[normed_algebra 𝕜 E] [complete_space E] [nontrivial E]

lemma unitary.spectrum_subset_circle (u : unitary E) :
  spectrum 𝕜 (u : E) ⊆ { k : 𝕜 | ∥k∥ = 1 } :=
begin
  refine λ k hk, le_antisymm _ _,
  { simpa only [cstar_ring.norm_coe_unitary u] using spectrum.norm_le_norm_of_mem hk },
  { let u' := unitary.to_units u,
    have hcoe : (u : E) = (u' : E), from rfl,
    rw hcoe at hk,
    have hnk := spectrum.not_eq_zero_of_mem_of_unit hk,
    rw [←inv_inv u', ←spectrum.map_inv, set.mem_inv] at hk,
    have : ∥k∥⁻¹ ≤ ∥↑(u'⁻¹)∥, by simpa only [norm_inv] using spectrum.norm_le_norm_of_mem hk,
    simpa using inv_le_of_inv_le (norm_pos_iff.mpr hnk) this }
end

lemma spectrum.subset_circle_of_unitary {u : E} (h : u ∈ unitary E) :
  spectrum 𝕜 u ⊆ { k : 𝕜 | ∥k∥ = 1 } :=
unitary.spectrum_subset_circle ⟨u, h⟩

end unitary_spectrum
