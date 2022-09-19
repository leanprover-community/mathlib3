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

variables {𝕜 E F ι : Type*}

open filter topological_space bornology
open_locale topological_space pointwise

variables [add_comm_group E] [uniform_space E] [uniform_add_group E]
variables [first_countable_topology E]
variables [add_comm_group F] [topological_space F] [topological_add_group F]
variables --[nontrivially_normed_field 𝕜] -- we need that for the balanced nhds
  [is_R_or_C 𝕜]
variables [module 𝕜 E] [has_continuous_smul 𝕜 E]
variables [module 𝕜 F] [has_continuous_smul 𝕜 F]

lemma norm_nsmul (n : ℕ) (x : 𝕜) : ∥n • x∥ = n • ∥x∥ :=
begin
  rw ←smul_one_smul ℤ n x,
  rw nsmul_one,
  rw norm_zsmul ℝ,
  simp,
  apply_instance,
end

#check continuous_const_smul
#check continuous.continuous_at

lemma foo (f : E →ₗ[𝕜] F)
  (hf : ∀ {s : set E} (hs : is_vonN_bounded 𝕜 s), is_vonN_bounded 𝕜 (f '' s)) :
  continuous_at f 0 :=
begin
  have hn : ∀ n : ℕ, (n + 1 : 𝕜) ≠ 0 :=
  begin
    intros n,
    norm_cast,
    simp only [nat.succ_ne_zero, not_false_iff],
  end,
  -- Assume that f is not continuous at 0
  by_contradiction,
  -- We use the a decreasing balanced basis for 0 : E and a balanced basis for 0 : F
  -- and reformulate non-continuity in terms of these bases
  --cases (𝓝 (0 : E)).exists_antitone_basis with b bE,
  -- filter.has_basis.exists_antitone_subbasis
  -- nhds_basis_balanced
  rcases (nhds_basis_balanced 𝕜 E).exists_antitone_subbasis with ⟨b, bE1, bE⟩,
  simp only [id.def] at bE,
  have bE' : (𝓝 (0 : E)).has_basis (λ (_x : ℕ), true) (λ n : ℕ, (n + 1 : 𝕜)⁻¹ • b (n + 1)) :=
  begin
    refine bE.1.to_has_basis _ _,
    {
      intros n _,
      use n,
      simp only [true_and],
      have h : b (n + 1) ⊆ b n := bE.2 (by simp),
      refine subset_trans _ h,
      rintros y ⟨x, hx, hy⟩,
      -- Here, we need that the basis is balanced
      rw ←hy,
      refine (bE1 (n+1)).2.smul_mem  _ hx,
      rw norm_inv,
      rw inv_le _ zero_lt_one,
      { nth_rewrite 1 ←nat.cast_one,
        rw ←nat.cast_add,
        rw ←nsmul_one,
        rw norm_nsmul,
        simp, },
      exact norm_pos_iff.mpr (hn _),
      apply_instance,
    },
    intros n _,
    have hcont : continuous_at (λ (x : E), (n + 1 : 𝕜) • x) 0 :=
      (continuous_const_smul (n + 1 : 𝕜)).continuous_at,
    simp only [continuous_at, map_zero, smul_zero] at hcont,
    rw bE.1.tendsto_left_iff at hcont,
    rcases hcont (b (n+1)) (bE1 (n+1)).1 with ⟨i, _, hi⟩,
    use i,
    simp only [true_and],
    intros x hx,
    specialize hi hx,
    rw set.mem_smul_set,
    refine ⟨((n + 1): 𝕜) • x, hi, _⟩,
    rw ←mul_smul,
    simp [hn n],
  end,
  admit { rw [continuous_at, map_zero, bE'.tendsto_iff (nhds_basis_balanced 𝕜 F)] at h,
  push_neg at h,
  rcases h with ⟨V, ⟨hV, hV'⟩, h⟩,
  simp only [id.def, forall_true_left] at h,
  -- There exists `u : ℕ → E` such that for all `x : ℕ` we have `u x ∈ b x` and `f (u x) ∉ V`
  cases classical.skolem.mp h with u hu,
  have hu' : tendsto (λ n : ℕ, (n : 𝕜) • u n) at_top (𝓝 (0 : E)) :=
  begin
    apply bE.tendsto,
    intros n,
    by_cases h : n = 0,
    { rw [h, nat.cast_zero, zero_smul],
      refine mem_of_mem_nhds (bE.1.mem_of_mem $ by triv) },
    specialize hu n,
    --cases hu with hu1 hu2,
    rw set.mem_smul_set at hu,
    rcases hu with ⟨⟨y, hy, hu1⟩, hu2⟩,
    convert hy,
    rw ←hu1,
    rw ←mul_smul,
    simp only [h, mul_inv_cancel, ne.def, nat.cast_eq_zero, not_false_iff, one_smul],
  end,
  have hu'' : is_vonN_bounded 𝕜 (set.range (λ n : ℕ, (n : 𝕜) • u n)) :=
  begin
    refine totally_bounded.is_vonN_bounded 𝕜 _,
    sorry,
  end,
  -- Since `range u` is bounded it absorbs `V`
  rcases hf hu'' hV with ⟨r, hr, h'⟩,
  cases exists_nat_gt r with n hn,
  have hn' : (n : 𝕜) ≠ 0 :=
  begin
    rw ←norm_pos_iff,
    have := hr.trans hn,
    simp only [nat.cast_pos] at this,
    simp only [norm_pos_iff, ne.def, nat.cast_eq_zero],
    exact ne_of_gt this,
  end,
  cases hu n with hu1 hu2,
  have h1 : r ≤ ∥n • (1 : 𝕜)∥ :=
  begin
    rw norm_nsmul,
    simp [hn.le],
  end,
  specialize h' (n • (1 : 𝕜)) h1,
  simp only [nat.smul_one_eq_coe, set.image_subset_iff] at h',
  specialize h' (set.mem_range_self n),
  simp only [set.mem_preimage, linear_map.map_smulₛₗ, map_nat_cast] at h',
  rw set.mem_smul_set at h',
  rcases h' with ⟨y, hy, h'⟩,
  apply_fun (λ y : F, (n : 𝕜)⁻¹ • y) at h',
  simp only [hn', inv_smul_smul₀, ne.def, not_false_iff] at h',
  rw h' at hy,
  exact hu2 hy, }
end
