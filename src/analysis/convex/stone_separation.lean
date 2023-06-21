/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.join

/-!
# Stone's separation theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file prove Stone's separation theorem. This tells us that any two disjoint convex sets can be
separated by a convex set whose complement is also convex.

In locally convex real topological vector spaces, the Hahn-Banach separation theorems provide
stronger statements: one may find a separating hyperplane, instead of merely a convex set whose
complement is convex.
-/

open set
open_locale big_operators

variables {𝕜 E ι : Type*} [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] {s t : set E}

/-- In a tetrahedron with vertices `x`, `y`, `p`, `q`, any segment `[u, v]` joining the opposite
edges `[x, p]` and `[y, q]` passes through any triangle of vertices `p`, `q`, `z` where
`z ∈ [x, y]`. -/
lemma not_disjoint_segment_convex_hull_triple {p q u v x y z : E}
  (hz : z ∈ segment 𝕜 x y) (hu : u ∈ segment 𝕜 x p) (hv : v ∈ segment 𝕜 y q) :
  ¬ disjoint (segment 𝕜 u v) (convex_hull 𝕜 {p, q, z}) :=
begin
  rw not_disjoint_iff,
  obtain ⟨az, bz, haz, hbz, habz, rfl⟩ := hz,
  obtain rfl | haz' := haz.eq_or_lt,
  { rw zero_add at habz,
    rw [zero_smul, zero_add, habz, one_smul],
    refine ⟨v, right_mem_segment _ _ _, segment_subset_convex_hull _ _ hv⟩; simp },
  obtain ⟨av, bv, hav, hbv, habv, rfl⟩ := hv,
  obtain rfl | hav' := hav.eq_or_lt,
  { rw zero_add at habv,
    rw [zero_smul, zero_add, habv, one_smul],
    exact ⟨q, right_mem_segment _ _ _, subset_convex_hull _ _ $ by simp⟩ },
  obtain ⟨au, bu, hau, hbu, habu, rfl⟩ := hu,
  have hab : 0 < az * av + bz * au :=
    add_pos_of_pos_of_nonneg (mul_pos haz' hav') (mul_nonneg hbz hau),
  refine ⟨(az * av / (az * av + bz * au)) • (au • x + bu • p) +
          (bz * au / (az * av + bz * au)) • (av • y + bv • q), ⟨_, _, _, _, _, rfl⟩, _⟩,
  { exact div_nonneg (mul_nonneg haz hav) hab.le },
  { exact div_nonneg (mul_nonneg hbz hau) hab.le },
  { rw [←add_div, div_self hab.ne'] },
  rw [smul_add, smul_add, add_add_add_comm, add_comm, ←mul_smul, ←mul_smul],
  classical,
  let w : fin 3 → 𝕜 := ![az * av * bu, bz * au * bv, au * av],
  let z : fin 3 → E := ![p, q, az • x + bz • y],
  have hw₀ : ∀ i, 0 ≤ w i,
  { rintro i,
    fin_cases i,
    { exact mul_nonneg (mul_nonneg haz hav) hbu },
    { exact mul_nonneg (mul_nonneg hbz hau) hbv },
    { exact mul_nonneg hau hav } },
  have hw : ∑ i, w i = az * av + bz * au,
  { transitivity az * av * bu + (bz * au * bv + au * av),
    { simp [w, fin.sum_univ_succ, fin.sum_univ_zero] },
    rw [←one_mul (au * av), ←habz, add_mul, ←add_assoc, add_add_add_comm, mul_assoc, ←mul_add,
      mul_assoc, ←mul_add, mul_comm av, ←add_mul, ←mul_add, add_comm bu, add_comm bv, habu, habv,
      one_mul, mul_one] },
  have hz : ∀ i, z i ∈ ({p, q, az • x + bz • y} : set E),
  { rintro i,
    fin_cases i; simp [z] },
  convert finset.center_mass_mem_convex_hull (finset.univ : finset (fin 3)) (λ i _, hw₀ i)
    (by rwa hw) (λ i _, hz i),
  rw finset.center_mass,
  simp_rw [div_eq_inv_mul, hw, mul_assoc, mul_smul (az * av + bz * au)⁻¹, ←smul_add, add_assoc,
    ←mul_assoc],
  congr' 3,
  rw [←mul_smul, ←mul_rotate, mul_right_comm, mul_smul, ←mul_smul _ av, mul_rotate, mul_smul _ bz,
    ←smul_add],
  simp only [list.map, list.pmap, nat.add_def, add_zero, fin.mk_bit0,
    fin.mk_one, list.foldr_cons, list.foldr_nil],
  refl,
end

/-- **Stone's Separation Theorem** -/
lemma exists_convex_convex_compl_subset (hs : convex 𝕜 s) (ht : convex 𝕜 t) (hst : disjoint s t) :
  ∃ C : set E, convex 𝕜 C ∧ convex 𝕜 Cᶜ ∧ s ⊆ C ∧ t ⊆ Cᶜ :=
begin
  let S : set (set E) := {C | convex 𝕜 C ∧ disjoint C t},
  obtain ⟨C, hC, hsC, hCmax⟩ := zorn_subset_nonempty S
    (λ c hcS hc ⟨t, ht⟩, ⟨⋃₀ c, ⟨hc.directed_on.convex_sUnion (λ s hs, (hcS hs).1),
     disjoint_sUnion_left.2 $ λ c hc, (hcS hc).2⟩, λ s, subset_sUnion_of_mem⟩) s ⟨hs, hst⟩,
  refine ⟨C, hC.1, convex_iff_segment_subset.2 $ λ x hx y hy z hz hzC, _, hsC,
     hC.2.subset_compl_left⟩,
  suffices h : ∀ c ∈ Cᶜ, ∃ a ∈ C, (segment 𝕜 c a ∩ t).nonempty,
  { obtain ⟨p, hp, u, hu, hut⟩ := h x hx,
    obtain ⟨q, hq, v, hv, hvt⟩ := h y hy,
    refine not_disjoint_segment_convex_hull_triple hz hu hv
      (hC.2.symm.mono (ht.segment_subset hut hvt) $ convex_hull_min _ hC.1),
    simp [insert_subset, hp, hq, singleton_subset_iff.2 hzC] },
  rintro c hc,
  by_contra' h,
  suffices h : disjoint (convex_hull 𝕜 (insert c C)) t,
  { rw ←hCmax _ ⟨convex_convex_hull _ _, h⟩
      ((subset_insert _ _).trans $ subset_convex_hull _ _) at hc,
    exact hc (subset_convex_hull _ _ $ mem_insert _ _) },
  rw [convex_hull_insert ⟨z, hzC⟩, convex_join_singleton_left],
  refine disjoint_Union₂_left.2 (λ a ha, disjoint_iff_inf_le.mpr $ λ b hb, h a _ ⟨b, hb⟩),
  rwa ←hC.1.convex_hull_eq,
end
