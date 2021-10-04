/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.independent
import combinatorics.simplicial_complex.to_move.default

/-!
# Convex independence
-/

open_locale affine big_operators classical
open finset

variables {𝕜 E ι : Type*} [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E]

lemma affine_independent.convex_independent {p : ι → E} (hp : affine_independent 𝕜 p) :
  convex_independent 𝕜 p :=
begin
  intros s x hx,
  by_contra,
  sorry
  /-
  rw [finset.convex_hull_eq] at hx,
  rcases hx with ⟨w, hw₀, hw₁, x_eq⟩,
  have : s.inj_on p := hp.injective.inj_on _,
  rw finset.center_mass_eq_of_sum_1 _ _ hw₁ at x_eq,
  rw finset.sum_image ‹set.inj_on p s› at hw₁,
  rw finset.sum_image ‹set.inj_on p s› at x_eq,
  dsimp at hw₁ x_eq,
  simp only [and_imp, finset.mem_image, forall_apply_eq_imp_iff₂, exists_imp_distrib] at hw₀,
  let w₀ : ι → ℝ := λ i, if i ∈ s then w (p i) else 0,
  let w₁ : ι → ℝ := λ i, if x = i then 1 else 0,
  have thing : _ = _ := unique_combination' (insert x s) hp w₀ w₁ _ _ _ _ (mem_insert_self _ _),
  { change ite _ _ _ = ite _ _ _ at thing,
    simpa [h] using thing },
  { rwa [sum_insert_of_eq_zero_if_not_mem, sum_extend_by_zero s],
    simp [h] },
  { simp [sum_ite_eq] },
  { simpa [sum_insert_of_eq_zero_if_not_mem, h, ite_smul, sum_extend_by_zero s] }-/
end
