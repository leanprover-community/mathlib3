/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.locally_convex.bounded
import analysis.normed_space.is_R_or_C

/-!
# Test

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

variables {𝕜 𝕜' E F ι : Type*}

open filter topological_space bornology
open_locale topological_space pointwise

variables [add_comm_group E] [uniform_space E] [uniform_add_group E]
variables [first_countable_topology E]
variables [add_comm_group F] [uniform_space F] [uniform_add_group F]
variables [is_R_or_C 𝕜] [is_R_or_C 𝕜']
variables [module 𝕜 E] [has_continuous_smul 𝕜 E]
variables [module 𝕜' F] [has_continuous_smul 𝕜' F]
variables {σ : 𝕜 →+* 𝕜'}

/-- Every Cauchy sequence over `ℕ` is totally bounded. -/
lemma totally_bounded_of_cauchy_seq {s : ℕ → E} (hs : cauchy_seq s): totally_bounded (set.range s) :=
begin
  sorry,
end

lemma continuous_at_zero_of_locally_bounded {f : E →ₛₗ[σ] F}
  (hf : ∀ (s : set E) (hs : is_vonN_bounded 𝕜 s), is_vonN_bounded 𝕜' (f '' s)) :
  continuous_at f 0 :=
begin
  -- Assume that f is not continuous at 0
  by_contradiction,
  -- We use the a decreasing balanced basis for 0 : E and a balanced basis for 0 : F
  -- and reformulate non-continuity in terms of these bases
  rcases (nhds_basis_balanced 𝕜 E).exists_antitone_subbasis with ⟨b, bE1, bE⟩,
  simp only [id.def] at bE,
  have bE' : (𝓝 (0 : E)).has_basis (λ (x : ℕ), x ≠ 0) (λ n : ℕ, (n : 𝕜)⁻¹ • b n) :=
  begin
    refine bE.1.to_has_basis _ _,
    { intros n _,
      use n+1,
      simp only [ne.def, nat.succ_ne_zero, not_false_iff, nat.cast_add, nat.cast_one, true_and],
      have h : b (n + 1) ⊆ b n := bE.2 (by simp),
      refine subset_trans _ h,
      rintros y ⟨x, hx, hy⟩,
      -- Here we need that the basis is balanced
      rw ←hy,
      refine (bE1 (n+1)).2.smul_mem  _ hx,
      have h' : 0 < (n : ℝ) + 1 := add_pos_of_nonneg_of_pos (nat.cast_nonneg _) zero_lt_one,
      rw [norm_inv, ←nat.cast_one, ←nat.cast_add, is_R_or_C.norm_eq_abs, is_R_or_C.abs_cast_nat,
        nat.cast_add, nat.cast_one, inv_le h' zero_lt_one],
      norm_cast,
      simp, },
    intros n hn,
    have hcont : continuous_at (λ (x : E), (n : 𝕜) • x) 0 :=
      (continuous_const_smul (n : 𝕜)).continuous_at,
    simp only [continuous_at, map_zero, smul_zero] at hcont,
    rw bE.1.tendsto_left_iff at hcont,
    rcases hcont (b n) (bE1 n).1 with ⟨i, _, hi⟩,
    use i,
    simp only [true_and],
    intros x hx,
    refine ⟨(n : 𝕜) • x, hi hx, _⟩,
    simp [←mul_smul, hn],
  end,
  rw [continuous_at, map_zero, bE'.tendsto_iff (nhds_basis_balanced 𝕜' F)] at h,
  push_neg at h,
  rcases h with ⟨V, ⟨hV, hV'⟩, h⟩,
  simp only [id.def, forall_true_left] at h,
  -- There exists `u : ℕ → E` such that for all `x : ℕ` we have `u x ∈ b x` and `f (u x) ∉ V`
  choose! u hu hu' using h,
  -- The sequence `(λ n, n • u n)` converges to `0`
  have h_tendsto : tendsto (λ n : ℕ, (n : 𝕜) • u n) at_top (𝓝 (0 : E)) :=
  begin
    apply bE.tendsto,
    intros n,
    by_cases h : n = 0,
    { rw [h, nat.cast_zero, zero_smul],
      refine mem_of_mem_nhds (bE.1.mem_of_mem $ by triv) },
    rcases hu n h with ⟨y, hy, hu1⟩,
    convert hy,
    rw [←hu1, ←mul_smul],
    simp only [h, mul_inv_cancel, ne.def, nat.cast_eq_zero, not_false_iff, one_smul],
  end,
  -- The image `(λ n, n • u n)` is totally bounded:
  have h_bounded : is_vonN_bounded 𝕜 (set.range (λ n : ℕ, (n : 𝕜) • u n)) :=
  (totally_bounded_of_cauchy_seq (filter.tendsto.cauchy_seq h_tendsto)).is_vonN_bounded 𝕜,
  -- Since `range u` is bounded it absorbs `V`
  rcases hf _ h_bounded hV with ⟨r, hr, h'⟩,
  cases exists_nat_gt r with n hn,
  have h1 : r ≤ ∥(n : 𝕜')∥ :=
  by { rw [is_R_or_C.norm_eq_abs, is_R_or_C.abs_cast_nat], exact hn.le },
  have hn' : (n : 𝕜') ≠ 0 :=
  by { rw ←norm_pos_iff, exact lt_of_lt_of_le hr h1 },
  specialize h' (n : 𝕜') h1,
  simp only [set.image_subset_iff] at h',
  specialize h' (set.mem_range_self n),
  simp only [set.mem_preimage, linear_map.map_smulₛₗ, map_nat_cast] at h',
  rcases h' with ⟨y, hy, h'⟩,
  apply_fun (λ y : F, (n : 𝕜')⁻¹ • y) at h',
  simp only [hn', inv_smul_smul₀, ne.def, not_false_iff] at h',
  rw h' at hy,
  norm_cast at hn',
  refine hu' n hn' hy,
end

lemma continuous_of_locally_bounded {f : E →ₛₗ[σ] F}
  (hf : ∀ (s : set E) (hs : is_vonN_bounded 𝕜 s), is_vonN_bounded 𝕜' (f '' s)) :
  continuous f :=
(uniform_continuous_of_continuous_at_zero f $ continuous_at_zero_of_locally_bounded hf).continuous
