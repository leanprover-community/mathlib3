/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import analysis.locally_convex.bounded
import data.is_R_or_C.basic

/-!
# Continuity and Von Neumann boundedness

This files proves that for `E` and `F` two topological vector spaces over `ℝ` or `ℂ`,
if `E` is first countable, then every locally bounded linear map `E →ₛₗ[σ] F` is continuous
(this is `linear_map.continuous_of_locally_bounded`).

We keep this file separate from `analysis/locally_convex/bounded` in order not to import
`analysis/normed_space/is_R_or_C` there, because defining the strong topology on the space of
continuous linear maps will require importing `analysis/locally_convex/bounded` in
`analysis/normed_space/operator_norm`.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

-/

open topological_space bornology filter
open_locale topology pointwise

variables {𝕜 𝕜' E F : Type*}
variables [add_comm_group E] [uniform_space E] [uniform_add_group E]
variables [add_comm_group F] [uniform_space F]

section nontrivially_normed_field

variables [uniform_add_group F]
variables [nontrivially_normed_field 𝕜] [module 𝕜 E] [module 𝕜 F] [has_continuous_smul 𝕜 E]

/-- Construct a continuous linear map from a linear map `f : E →ₗ[𝕜] F` and the existence of a
neighborhood of zero that gets mapped into a bounded set in `F`. -/
def linear_map.clm_of_exists_bounded_image (f : E →ₗ[𝕜] F)
  (h : ∃ (V : set E) (hV : V ∈ 𝓝 (0 : E)), bornology.is_vonN_bounded 𝕜 (f '' V)) : E →L[𝕜] F :=
⟨f, begin
  -- It suffices to show that `f` is continuous at `0`.
  refine continuous_of_continuous_at_zero f _,
  rw [continuous_at_def, f.map_zero],
  intros U hU,
  -- Continuity means that `U ∈ 𝓝 0` implies that `f ⁻¹' U ∈ 𝓝 0`.
  rcases h with ⟨V, hV, h⟩,
  rcases h hU with ⟨r, hr, h⟩,
  rcases normed_field.exists_lt_norm 𝕜 r with ⟨x, hx⟩,
  specialize h x hx.le,
  -- After unfolding all the definitions, we know that `f '' V ⊆ x • U`. We use this to show the
  -- inclusion `x⁻¹ • V ⊆ f⁻¹' U`.
  have x_ne := norm_pos_iff.mp (hr.trans hx),
  have : x⁻¹ • V ⊆ f⁻¹' U :=
  calc x⁻¹ • V ⊆  x⁻¹ • (f⁻¹' (f '' V)) : set.smul_set_mono (set.subset_preimage_image ⇑f V)
  ... ⊆ x⁻¹ • (f⁻¹' (x • U)) : set.smul_set_mono (set.preimage_mono h)
  ... = f⁻¹' (x⁻¹ • (x • U)) :
      by ext; simp only [set.mem_inv_smul_set_iff₀ x_ne, set.mem_preimage, linear_map.map_smul]
  ... ⊆ f⁻¹' U : by rw inv_smul_smul₀ x_ne _,
  -- Using this inclusion, it suffices to show that `x⁻¹ • V` is in `𝓝 0`, which is trivial.
  refine mem_of_superset _ this,
  convert set_smul_mem_nhds_smul hV (inv_ne_zero x_ne),
  exact (smul_zero _).symm,
end⟩

lemma linear_map.clm_of_exists_bounded_image_coe {f : E →ₗ[𝕜] F}
  {h : ∃ (V : set E) (hV : V ∈ 𝓝 (0 : E)), bornology.is_vonN_bounded 𝕜 (f '' V)} :
  (f.clm_of_exists_bounded_image h : E →ₗ[𝕜] F) = f := rfl

@[simp] lemma linear_map.clm_of_exists_bounded_image_apply {f : E →ₗ[𝕜] F}
  {h : ∃ (V : set E) (hV : V ∈ 𝓝 (0 : E)), bornology.is_vonN_bounded 𝕜 (f '' V)} {x : E} :
  f.clm_of_exists_bounded_image h x = f x := rfl

end nontrivially_normed_field

section is_R_or_C

open topological_space bornology

variables [first_countable_topology E]
variables [is_R_or_C 𝕜] [module 𝕜 E] [has_continuous_smul 𝕜 E]
variables [is_R_or_C 𝕜'] [module 𝕜' F] [has_continuous_smul 𝕜' F]
variables {σ : 𝕜 →+* 𝕜'}

lemma linear_map.continuous_at_zero_of_locally_bounded (f : E →ₛₗ[σ] F)
  (hf : ∀ (s : set E) (hs : is_vonN_bounded 𝕜 s), is_vonN_bounded 𝕜' (f '' s)) :
  continuous_at f 0 :=
begin
  -- Assume that f is not continuous at 0
  by_contradiction,
  -- We use a decreasing balanced basis for 0 : E and a balanced basis for 0 : F
  -- and reformulate non-continuity in terms of these bases
  rcases (nhds_basis_balanced 𝕜 E).exists_antitone_subbasis with ⟨b, bE1, bE⟩,
  simp only [id.def] at bE,
  have bE' : (𝓝 (0 : E)).has_basis (λ (x : ℕ), x ≠ 0) (λ n : ℕ, (n : 𝕜)⁻¹ • b n) :=
  begin
    refine bE.1.to_has_basis _ _,
    { intros n _,
      use n+1,
      simp only [ne.def, nat.succ_ne_zero, not_false_iff, nat.cast_add, nat.cast_one, true_and],
      -- `b (n + 1) ⊆ b n` follows from `antitone`.
      have h : b (n + 1) ⊆ b n := bE.2 (by simp),
      refine subset_trans _ h,
      rintros y ⟨x, hx, hy⟩,
      -- Since `b (n + 1)` is balanced `(n+1)⁻¹ b (n + 1) ⊆ b (n + 1)`
      rw ←hy,
      refine (bE1 (n+1)).2.smul_mem  _ hx,
      have h' : 0 < (n : ℝ) + 1 := n.cast_add_one_pos,
      rw [norm_inv, ←nat.cast_one, ←nat.cast_add, is_R_or_C.norm_eq_abs, is_R_or_C.abs_cast_nat,
        nat.cast_add, nat.cast_one, inv_le h' zero_lt_one],
      norm_cast,
      simp, },
    intros n hn,
    -- The converse direction follows from continuity of the scalar multiplication
    have hcont : continuous_at (λ (x : E), (n : 𝕜) • x) 0 :=
    (continuous_const_smul (n : 𝕜)).continuous_at,
    simp only [continuous_at, map_zero, smul_zero] at hcont,
    rw bE.1.tendsto_left_iff at hcont,
    rcases hcont (b n) (bE1 n).1 with ⟨i, _, hi⟩,
    refine ⟨i, trivial, λ x hx, ⟨(n : 𝕜) • x, hi hx, _⟩⟩,
    simp [←mul_smul, hn],
  end,
  rw [continuous_at, map_zero, bE'.tendsto_iff (nhds_basis_balanced 𝕜' F)] at h,
  push_neg at h,
  rcases h with ⟨V, ⟨hV, hV'⟩, h⟩,
  simp only [id.def, forall_true_left] at h,
  -- There exists `u : ℕ → E` such that for all `n : ℕ` we have `u n ∈ n⁻¹ • b n` and `f (u n) ∉ V`
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
  -- The image `(λ n, n • u n)` is von Neumann bounded:
  have h_bounded : is_vonN_bounded 𝕜 (set.range (λ n : ℕ, (n : 𝕜) • u n)) :=
  h_tendsto.cauchy_seq.totally_bounded_range.is_vonN_bounded 𝕜,
  -- Since `range u` is bounded it absorbs `V`
  rcases hf _ h_bounded hV with ⟨r, hr, h'⟩,
  cases exists_nat_gt r with n hn,
  -- We now find a contradiction between `f (u n) ∉ V` and the absorbing property
  have h1 : r ≤ ‖(n : 𝕜')‖ :=
  by { rw [is_R_or_C.norm_eq_abs, is_R_or_C.abs_cast_nat], exact hn.le },
  have hn' : 0 < ‖(n : 𝕜')‖ := lt_of_lt_of_le hr h1,
  rw [norm_pos_iff, ne.def, nat.cast_eq_zero] at hn',
  have h'' : f (u n) ∈ V :=
  begin
    simp only [set.image_subset_iff] at h',
    specialize h' (n : 𝕜') h1 (set.mem_range_self n),
    simp only [set.mem_preimage, linear_map.map_smulₛₗ, map_nat_cast] at h',
    rcases h' with ⟨y, hy, h'⟩,
    apply_fun (λ y : F, (n : 𝕜')⁻¹ • y) at h',
    simp only [hn', inv_smul_smul₀, ne.def, nat.cast_eq_zero, not_false_iff] at h',
    rwa ←h',
  end,
  exact hu' n hn' h'',
end

/-- If `E` is first countable, then every locally bounded linear map `E →ₛₗ[σ] F` is continuous. -/
lemma linear_map.continuous_of_locally_bounded [uniform_add_group F] (f : E →ₛₗ[σ] F)
  (hf : ∀ (s : set E) (hs : is_vonN_bounded 𝕜 s), is_vonN_bounded 𝕜' (f '' s)) :
  continuous f :=
(uniform_continuous_of_continuous_at_zero f $ f.continuous_at_zero_of_locally_bounded hf).continuous

end is_R_or_C
