/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.join

/-!
# Stone's separation theorem

This file prove Stone's separation theorem. This tells us that any two disjoint convex sets can be
separated by a convex set whose complement is also convex.

It can be seen as a "cheap" version of the geometric Hahn-Banach theorem, in the sense that the
separating set in Stone's separation corresponds to the halfspace in geometric Hahn-Banach, but in a
much broader class of spaces (any vector space, instead of real normed spaces).
-/

open set
open_locale big_operators

variables {𝕜 E ι : Type*} [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] {w x y z : E}
  {s t : set E}

/-- In a tetrahedron, any segment joining opposite edges passes through any triangle whose base is
another edge. -/
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
  simp only [list.map, list.pmap, nat.add_def, add_zero, fin.mk_eq_subtype_mk, fin.mk_bit0,
    fin.mk_one, list.foldr_cons, list.foldr_nil],
  refl,
end

/-- **Stone's Separation Theorem** -/
lemma exists_convex_convex_compl_subset (hs : convex 𝕜 s) (ht : convex 𝕜 t) (hst : disjoint s t) :
  ∃ C : set E, convex 𝕜 C ∧ convex 𝕜 Cᶜ ∧ s ⊆ C ∧ t ⊆ Cᶜ :=
begin
  let S : set (set E) := {C | convex 𝕜 C ∧ C ⊆ tᶜ},
  obtain ⟨C, hC, hsC, hCmax⟩ := zorn_subset_nonempty S
    (λ c hcS hc ⟨t, ht⟩, ⟨⋃₀ c, ⟨hc.directed_on.convex_sUnion (λ s hs, (hcS hs).1),
    sUnion_subset (λ C hC, (hcS hC).2)⟩, λ s, subset_sUnion_of_mem⟩) s
    ⟨hs, disjoint_iff_subset_compl_right.1 hst⟩,
  refine ⟨C, hC.1, convex_iff_segment_subset.2 $ λ x y hx hy z hz hzC, _, hsC,
    subset_compl_comm.1 hC.2⟩,
  suffices h : ∀ c ∈ Cᶜ, ∃ a ∈ C, (segment 𝕜 c a ∩ t).nonempty,
  { obtain ⟨p, hp, u, hu, hut⟩ := h x hx,
    obtain ⟨q, hq, v, hv, hvt⟩ := h y hy,
    refine not_disjoint_segment_convex_hull_triple hz hu hv ((disjoint_iff_subset_compl_left.2
      hC.2).mono (ht.segment_subset hut hvt) $ convex_hull_min _ hC.1),
    simp [insert_subset, hp, hq, singleton_subset_iff.2 hzC] },
  rintro c hc,
  by_contra' h,
  suffices h : convex_hull 𝕜 (insert c C) ⊆ tᶜ,
  { rw ←hCmax _ ⟨convex_convex_hull _ _, h⟩
      ((subset_insert _ _).trans $ subset_convex_hull _ _) at hc,
    exact hc (subset_convex_hull _ _ $ mem_insert _ _) },
  rw [convex_hull_insert ⟨z, hzC⟩, convex_join_singleton_left],
  refine Union₂_subset (λ a ha b hb hbt, h a _ ⟨b, hb, hbt⟩),
  rwa ←hC.1.convex_hull_eq,
end
