/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import analysis.convex.basic
import topology.algebra.affine
import topology.local_extr

/-!
# Minima and maxima of convex functions

We show that if a function `f : E → β` is convex, then a local minimum is also
a global minimum, and likewise for concave functions.
-/

variables {𝕜 E β : Type*} [linear_ordered_semiring 𝕜] [densely_ordered 𝕜] [topological_space 𝕜] [order_topology 𝕜]
  [add_comm_group E]
  [topological_space E] [module 𝕜 E] [topological_add_group E] [has_continuous_smul 𝕜 E]
  [linear_ordered_add_comm_group β] [module 𝕜 β] [ordered_smul 𝕜 β]
  {s : set E}

open set filter
open_locale classical

/--
Helper lemma for the more general case: `is_min_on.of_is_local_min_on_of_convex_on`.
-/
lemma is_min_on.of_is_local_min_on_of_convex_on_Icc {f : 𝕜 → β} {a b : 𝕜} (a_lt_b : a < b)
  (h_local_min : is_local_min_on f (Icc a b) a) (h_conv : convex_on 𝕜 (Icc a b) f) :
  ∀ x ∈ Icc a b, f a ≤ f x :=
begin
  by_contradiction H_cont,
  push_neg at H_cont,
  rcases H_cont with ⟨x, ⟨h_ax, h_xb⟩, fx_lt_fa⟩,
  obtain ⟨z, hz, ge_on_nhd⟩ : ∃ z > a, ∀ y ∈ (Icc a z), f y ≥ f a,
  { rcases eventually_iff_exists_mem.mp h_local_min with ⟨U, U_in_nhds_within, fy_ge_fa⟩,
    rw [nhds_within_Icc_eq_nhds_within_Ici a_lt_b, mem_nhds_within_Ici_iff_exists_Icc_subset]
        at U_in_nhds_within,
    rcases U_in_nhds_within with ⟨ε, ε_in_Ioi, Ioc_in_U⟩,
    exact ⟨ε, mem_Ioi.mp ε_in_Ioi, λ y y_in_Ioc, fy_ge_fa y $ Ioc_in_U y_in_Ioc⟩ },
  have a_lt_x : a < x := lt_of_le_of_ne h_ax (λ H, by subst H; exact lt_irrefl (f a) fx_lt_fa),
  have lt_on_nhd : ∀ y ∈ Ioc a x, f y < f a,
  { intros y y_in_Ioc,
    rcases (convex.mem_Ioc a_lt_x).mp y_in_Ioc with ⟨ya, yx, ya_pos, yx_pos, yax, y_combo⟩,
    calc
      f y = f (ya * a + yx * x)       : by rw [y_combo]
      ... ≤ ya • f a + yx • f x
                : h_conv.2 (left_mem_Icc.mpr (le_of_lt a_lt_b)) ⟨h_ax, h_xb⟩ (ya_pos)
                    (le_of_lt yx_pos) yax
      ... < ya • f a + yx • f a       : add_lt_add_left (smul_lt_smul_of_pos fx_lt_fa yx_pos) _
      ... = f a                       : by rw [←add_smul, yax, one_smul] },
  by_cases h_xz : x ≤ z,
  { exact not_lt_of_ge (ge_on_nhd x (show x ∈ Icc a z, by exact ⟨h_ax, h_xz⟩)) fx_lt_fa, },
  { have h₁ : z ∈ Ioc a x := ⟨hz, le_of_not_ge h_xz⟩,
    have h₂ : z ∈ Icc a z := ⟨le_of_lt hz, le_refl z⟩,
    exact not_lt_of_ge (ge_on_nhd z h₂) (lt_on_nhd z h₁) }
end

/--
A local minimum of a convex function is a global minimum, restricted to a set `s`.
-/
lemma is_min_on.of_is_local_min_on_of_convex_on {f : E → β} {a : E}
  (a_in_s : a ∈ s) (h_localmin : is_local_min_on f s a) (h_conv : convex_on 𝕜 s f) :
  ∀ x ∈ s, f a ≤ f x :=
begin
  by_contradiction H_cont,
  push_neg at H_cont,
  rcases H_cont with ⟨x, ⟨x_in_s, fx_lt_fa⟩⟩,
  let g : 𝕜 →ᵃ[𝕜] E := affine_map.line_map a x,
  have hg0 : g 0 = a := affine_map.line_map_apply_zero a x,
  have hg1 : g 1 = x := affine_map.line_map_apply_one a x,
  have fg_local_min_on : is_local_min_on (f ∘ g) (g ⁻¹' s) 0,
  { rw ←hg0 at h_localmin,
    refine is_local_min_on.comp_continuous_on h_localmin subset.rfl
      (continuous.continuous_on (affine_map.line_map_continuous)) _,
    simp [mem_preimage, hg0, a_in_s] },
  have fg_min_on : ∀ x ∈ (Icc 0 1 : set 𝕜), (f ∘ g) 0 ≤ (f ∘ g) x,
  { have Icc_in_s' : Icc 0 1 ⊆ (g ⁻¹' s),
    { have h0 : (0 : 𝕜) ∈ (g ⁻¹' s) := by simp [mem_preimage, a_in_s],
      have h1 : (1 : 𝕜) ∈ (g ⁻¹' s) := by simp [mem_preimage, hg1, x_in_s],
      rw ←segment_eq_Icc (show (0 : 𝕜) ≤ 1, by linarith),
      exact (convex.affine_preimage g h_conv.1).segment_subset
        (by simp [mem_preimage, hg0, a_in_s]) (by simp [mem_preimage, hg1, x_in_s]) },
    have fg_local_min_on' : is_local_min_on (f ∘ g) (Icc 0 1) 0 :=
      is_local_min_on.on_subset fg_local_min_on Icc_in_s',
    refine is_min_on.of_is_local_min_on_of_convex_on_Icc (by linarith) fg_local_min_on' _,
    exact (convex_on.comp_affine_map g h_conv).subset Icc_in_s' (convex_Icc 0 1) },
  have gx_lt_ga : (f ∘ g) 1 < (f ∘ g) 0 := by simp [hg1, fx_lt_fa, hg0],
  exact not_lt_of_ge (fg_min_on 1 (mem_Icc.mpr ⟨zero_le_one, le_refl 1⟩)) gx_lt_ga,
end

/-- A local maximum of a concave function is a global maximum, restricted to a set `s`. -/
lemma is_max_on.of_is_local_max_on_of_concave_on {f : E → β} {a : E}
  (a_in_s : a ∈ s) (h_localmax: is_local_max_on f s a) (h_conc : concave_on 𝕜 s f) :
  ∀ x ∈ s, f x ≤ f a :=
@is_min_on.of_is_local_min_on_of_convex_on _
  _ _ (order_dual β) _ _ _ _ _ _ _ s f a a_in_s h_localmax h_conc

/-- A local minimum of a convex function is a global minimum. -/
lemma is_min_on.of_is_local_min_of_convex_univ {f : E → β} {a : E}
  (h_local_min : is_local_min f a) (h_conv : convex_on 𝕜 univ f) : ∀ x, f a ≤ f x :=
λ x, (is_min_on.of_is_local_min_on_of_convex_on (mem_univ a)
        (is_local_min.on h_local_min univ) h_conv) x (mem_univ x)

/-- A local maximum of a concave function is a global maximum. -/
lemma is_max_on.of_is_local_max_of_convex_univ {f : E → β} {a : E}
  (h_local_max : is_local_max f a) (h_conc : concave_on 𝕜 univ f) : ∀ x, f x ≤ f a :=
@is_min_on.of_is_local_min_of_convex_univ _ (order_dual β) _ _ _ _ _ _ _ _ f a h_local_max h_conc
