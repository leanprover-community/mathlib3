/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import analysis.convex.function
import topology.algebra.affine
import topology.local_extr
import topology.metric_space.basic

/-!
# Minima and maxima of convex functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show that if a function `f : E → β` is convex, then a local minimum is also
a global minimum, and likewise for concave functions.
-/

variables {E β : Type*} [add_comm_group E] [topological_space E]
  [module ℝ E] [topological_add_group E] [has_continuous_smul ℝ E]
  [ordered_add_comm_group β] [module ℝ β] [ordered_smul ℝ β]
  {s : set E}

open set filter function
open_locale classical topology

/--
Helper lemma for the more general case: `is_min_on.of_is_local_min_on_of_convex_on`.
-/
lemma is_min_on.of_is_local_min_on_of_convex_on_Icc {f : ℝ → β} {a b : ℝ} (a_lt_b : a < b)
  (h_local_min : is_local_min_on f (Icc a b) a) (h_conv : convex_on ℝ (Icc a b) f) :
  is_min_on f (Icc a b) a :=
begin
  rintro c hc, dsimp only [mem_set_of_eq],
  rw [is_local_min_on, nhds_within_Icc_eq_nhds_within_Ici a_lt_b] at h_local_min,
  rcases hc.1.eq_or_lt with rfl|a_lt_c, { exact le_rfl },
  have H₁ : ∀ᶠ y in 𝓝[>] a, f a ≤ f y,
    from h_local_min.filter_mono (nhds_within_mono _ Ioi_subset_Ici_self),
  have H₂ : ∀ᶠ y in 𝓝[>] a, y ∈ Ioc a c,
    from Ioc_mem_nhds_within_Ioi (left_mem_Ico.2 a_lt_c),
  rcases (H₁.and H₂).exists with ⟨y, hfy, hy_ac⟩,
  rcases (convex.mem_Ioc a_lt_c).mp hy_ac with ⟨ya, yc, ya₀, yc₀, yac, rfl⟩,
  suffices : ya • f a + yc • f a ≤ ya • f a + yc • f c,
    from (smul_le_smul_iff_of_pos yc₀).1 (le_of_add_le_add_left this),
  calc ya • f a + yc • f a = f a : by rw [← add_smul, yac, one_smul]
  ... ≤ f (ya * a + yc * c)      : hfy
  ... ≤ ya • f a + yc • f c      : h_conv.2 (left_mem_Icc.2 a_lt_b.le) hc ya₀ yc₀.le yac
end

/--
A local minimum of a convex function is a global minimum, restricted to a set `s`.
-/
lemma is_min_on.of_is_local_min_on_of_convex_on {f : E → β} {a : E}
  (a_in_s : a ∈ s) (h_localmin : is_local_min_on f s a) (h_conv : convex_on ℝ s f) :
  is_min_on f s a :=
begin
  intros x x_in_s,
  let g : ℝ →ᵃ[ℝ] E := affine_map.line_map a x,
  have hg0 : g 0 = a := affine_map.line_map_apply_zero a x,
  have hg1 : g 1 = x := affine_map.line_map_apply_one a x,
  have hgc : continuous g, from affine_map.line_map_continuous,
  have h_maps : maps_to g (Icc 0 1) s,
  { simpa only [maps_to', ← segment_eq_image_line_map]
      using h_conv.1.segment_subset a_in_s x_in_s },
  have fg_local_min_on : is_local_min_on (f ∘ g) (Icc 0 1) 0,
  { rw ← hg0 at h_localmin,
    exact h_localmin.comp_continuous_on h_maps hgc.continuous_on (left_mem_Icc.2 zero_le_one) },
  have fg_min_on : is_min_on (f ∘ g) (Icc 0 1 : set ℝ) 0,
  { refine is_min_on.of_is_local_min_on_of_convex_on_Icc one_pos fg_local_min_on _,
    exact (h_conv.comp_affine_map g).subset h_maps (convex_Icc 0 1) },
  simpa only [hg0, hg1, comp_app, mem_set_of_eq] using fg_min_on (right_mem_Icc.2 zero_le_one)
end

/-- A local maximum of a concave function is a global maximum, restricted to a set `s`. -/
lemma is_max_on.of_is_local_max_on_of_concave_on {f : E → β} {a : E}
  (a_in_s : a ∈ s) (h_localmax: is_local_max_on f s a) (h_conc : concave_on ℝ s f) :
  is_max_on f s a :=
@is_min_on.of_is_local_min_on_of_convex_on _ βᵒᵈ _ _ _ _ _ _ _ _ s f a a_in_s h_localmax h_conc

/-- A local minimum of a convex function is a global minimum. -/
lemma is_min_on.of_is_local_min_of_convex_univ {f : E → β} {a : E}
  (h_local_min : is_local_min f a) (h_conv : convex_on ℝ univ f) : ∀ x, f a ≤ f x :=
λ x, (is_min_on.of_is_local_min_on_of_convex_on (mem_univ a)
        (h_local_min.on univ) h_conv) (mem_univ x)

/-- A local maximum of a concave function is a global maximum. -/
lemma is_max_on.of_is_local_max_of_convex_univ {f : E → β} {a : E}
  (h_local_max : is_local_max f a) (h_conc : concave_on ℝ univ f) : ∀ x, f x ≤ f a :=
@is_min_on.of_is_local_min_of_convex_univ _ βᵒᵈ _ _ _ _ _ _ _ _ f a h_local_max h_conc
