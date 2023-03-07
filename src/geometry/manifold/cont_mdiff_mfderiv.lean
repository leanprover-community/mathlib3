/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import geometry.manifold.mfderiv

/-!
### Interactions between differentiability, smoothness and manifold derivatives

We give the relation between `mdifferentiable`, `cont_mdiff`, `mfderiv`, `tangent_map`
and related notions.

## Main statements

* `cont_mdiff_on.cont_mdiff_on_tangent_map_within` states that the bundled derivative
  of a `Cⁿ` function in a domain is `Cᵐ` when `m + 1 ≤ n`.
* `cont_mdiff.cont_mdiff_tangent_map` states that the bundled derivative
  of a `Cⁿ` function is `Cᵐ` when `m + 1 ≤ n`.
-/

open set function filter charted_space smooth_manifold_with_corners
open_locale topology manifold bundle

noncomputable theory

namespace continuous_linear_map

variables {R₁ M₁ M₂ M₃ : Type*} [semiring R₁]
variables [topological_space M₁] [add_comm_monoid M₁]
variables [topological_space M₂] [add_comm_monoid M₂]
variables [topological_space M₃] [add_comm_monoid M₃]
variables [module R₁ M₁] [module R₁ M₂] [module R₁ M₃]

lemma fst_prod_zero_add_zero_prod_snd [has_continuous_add M₁] [has_continuous_add M₂] :
  (continuous_linear_map.fst R₁ M₁ M₂).prod 0 +
  continuous_linear_map.prod 0 (continuous_linear_map.snd R₁ M₁ M₂) =
  continuous_linear_map.id R₁ (M₁ × M₂) :=
begin
  rw [continuous_linear_map.ext_iff],
  intro x,
  simp_rw [continuous_linear_map.add_apply, continuous_linear_map.id_apply,
    continuous_linear_map.prod_apply, continuous_linear_map.coe_fst',
    continuous_linear_map.coe_snd', continuous_linear_map.zero_apply, prod.mk_add_mk, add_zero,
    zero_add, prod.mk.eta]
end

end continuous_linear_map


section fiber_bundle
open bundle (total_space total_space.proj) trivialization

variables {F B X : Type*} {E : B → Type*} [topological_space B] [topological_space F]
  [topological_space (total_space E)] [Π b, topological_space (E b)] [fiber_bundle F E]
  [topological_space X]

@[simp, mfld_simps]
lemma mem_trivialization_at_proj_source {x : total_space E} :
  x ∈ (trivialization_at F E x.proj).source :=
(trivialization.mem_source _).mpr $ mem_base_set_trivialization_at F E x.proj

@[simp, mfld_simps]
lemma trivialization_at_proj_fst {x : total_space E} :
  ((trivialization_at F E x.proj) x).1 = x.proj :=
coe_fst' _ $ mem_base_set_trivialization_at F E x.proj

variable (F)
/-- Characterization of continuous functions into a fiber bundle. -/
lemma continuous_within_at_total_space (f : X → total_space E) {s : set X} {x₀ : X} :
  continuous_within_at f s x₀ ↔
  continuous_within_at (λ x, (f x).proj) s x₀ ∧
  continuous_within_at (λ x, ((trivialization_at F E (f x₀).proj) (f x)).2) s x₀ :=
begin
  refine (and_iff_right_iff_imp.2 $ λ hf, _).symm.trans (and_congr_right $ λ hf, _),
  { refine (continuous_proj F E).continuous_within_at.comp hf (maps_to_image f s) },
  have h1 : (λ x, (f x).proj) ⁻¹' (trivialization_at F E (f x₀).proj).base_set ∈ 𝓝[s] x₀ :=
    hf.preimage_mem_nhds_within ((open_base_set _).mem_nhds (mem_base_set_trivialization_at F E _)),
  have h2 : continuous_within_at (λ x, (trivialization_at F E (f x₀).proj (f x)).1) s x₀,
  { refine hf.congr_of_eventually_eq (eventually_of_mem h1 $ λ x hx, _) trivialization_at_proj_fst,
    rw [coe_fst'],
    exact hx },
  rw [(trivialization_at F E (f x₀).proj).continuous_within_at_iff_continuous_within_at_comp_left],
  { simp_rw [continuous_within_at_prod_iff, function.comp, trivialization.coe_coe, h2, true_and] },
  { apply mem_trivialization_at_proj_source },
  { rwa [source_eq, preimage_preimage] }
end

/-- Characterization of continuous functions into a fiber bundle. -/
lemma continuous_at_total_space (f : X → total_space E) {x₀ : X} :
  continuous_at f x₀ ↔ continuous_at (λ x, (f x).proj) x₀ ∧
  continuous_at (λ x, ((trivialization_at F E (f x₀).proj) (f x)).2) x₀ :=
by { simp_rw [← continuous_within_at_univ], exact continuous_within_at_total_space F f }

end fiber_bundle

namespace local_homeomorph

variables {𝕜 E M H E' M' H' : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E] [topological_space H] [topological_space M]
  (f f' : local_homeomorph M H) (I : model_with_corners 𝕜 E H)
  [normed_add_comm_group E'] [normed_space 𝕜 E'] [topological_space H'] [topological_space M']
  (I' : model_with_corners 𝕜 E' H')
  (x : M) {s t : set M}
  [charted_space H M] [charted_space H' M']

lemma ext_chart_at_prod_apply (x y : M × M') :
  ext_chart_at (I.prod I') x y = (ext_chart_at I x.1 y.1, ext_chart_at I' x.2 y.2) :=
by simp only with mfld_simps


end local_homeomorph


/-! ### Definition of smooth functions between manifolds -/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
-- declare a smooth manifold `M` over the pair `(E, H)`.
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M]
-- declare a smooth manifold `M'` over the pair `(E', H')`.
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M']
-- declare a smooth manifold `N` over the pair `(F, G)`.
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
{G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
{N : Type*} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N]
-- declare a smooth manifold `N'` over the pair `(F', G')`.
{F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
{G' : Type*} [topological_space G'] {J' : model_with_corners 𝕜 F' G'}
{N' : Type*} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N']
-- declare some additional normed spaces, used for fibers of vector bundles
{F₁ : Type*} [normed_add_comm_group F₁] [normed_space 𝕜 F₁]
{F₂ : Type*} [normed_add_comm_group F₂] [normed_space 𝕜 F₂]
-- declare functions, sets, points and smoothness indices
{f f₁ : M → M'} {s s₁ t : set M} {x : M} {m n : ℕ∞}

-- move to cont_mdiff
lemma cont_mdiff_within_at.fst {f : N → M × M'} {s : set N} {x : N}
  (hf : cont_mdiff_within_at J (I.prod I') n f s x) :
  cont_mdiff_within_at J I n (λ x, (f x).1) s x :=
cont_mdiff_within_at_fst.comp x hf (maps_to_image f s)

lemma cont_mdiff_within_at.snd {f : N → M × M'} {s : set N} {x : N}
  (hf : cont_mdiff_within_at J (I.prod I') n f s x) :
  cont_mdiff_within_at J I' n (λ x, (f x).2) s x :=
cont_mdiff_within_at_snd.comp x hf (maps_to_image f s)

lemma cont_mdiff_within_at_prod_iff (f : M → M' × N') {s : set M} {x : M} :
  cont_mdiff_within_at I (I'.prod J') n f s x ↔
  cont_mdiff_within_at I I' n (prod.fst ∘ f) s x ∧
  cont_mdiff_within_at I J' n (prod.snd ∘ f) s x :=
by { refine ⟨λ h, ⟨h.fst, h.snd⟩, λ h, _⟩, simpa only [prod.mk.eta] using h.1.prod_mk h.2 }

lemma cont_mdiff_at_prod_iff (f : M → M' × N') {x : M} :
  cont_mdiff_at I (I'.prod J') n f x ↔
  cont_mdiff_at I I' n (prod.fst ∘ f) x ∧ cont_mdiff_at I J' n (prod.snd ∘ f) x :=
by { simp_rw [← cont_mdiff_within_at_univ], exact cont_mdiff_within_at_prod_iff f }

lemma cont_mdiff_at_congr (h : f₁ =ᶠ[𝓝 x] f) :
  cont_mdiff_at I I' n f₁ x ↔ cont_mdiff_at I I' n f x :=
(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_at_congr_iff_of_eventually_eq h

/-! ### Deducing differentiability from smoothness -/

lemma cont_mdiff_within_at.mdifferentiable_within_at
  (hf : cont_mdiff_within_at I I' n f s x) (hn : 1 ≤ n) :
  mdifferentiable_within_at I I' f s x :=
begin
  suffices h : mdifferentiable_within_at I I' f (s ∩ (f ⁻¹' (ext_chart_at I' (f x)).source)) x,
  { rwa mdifferentiable_within_at_inter' at h,
    apply (hf.1).preimage_mem_nhds_within,
    exact ext_chart_at_source_mem_nhds I' (f x) },
  rw mdifferentiable_within_at_iff,
  exact ⟨hf.1.mono (inter_subset_left _ _),
    (hf.2.differentiable_within_at hn).mono (by mfld_set_tac)⟩,
end

lemma cont_mdiff_at.mdifferentiable_at (hf : cont_mdiff_at I I' n f x) (hn : 1 ≤ n) :
  mdifferentiable_at I I' f x :=
mdifferentiable_within_at_univ.1 $ cont_mdiff_within_at.mdifferentiable_within_at hf hn

lemma cont_mdiff_on.mdifferentiable_on (hf : cont_mdiff_on I I' n f s) (hn : 1 ≤ n) :
  mdifferentiable_on I I' f s :=
λ x hx, (hf x hx).mdifferentiable_within_at hn

lemma cont_mdiff.mdifferentiable (hf : cont_mdiff I I' n f) (hn : 1 ≤ n) :
  mdifferentiable I I' f :=
λ x, (hf x).mdifferentiable_at hn

lemma smooth_within_at.mdifferentiable_within_at
  (hf : smooth_within_at I I' f s x) : mdifferentiable_within_at I I' f s x :=
hf.mdifferentiable_within_at le_top

lemma smooth_at.mdifferentiable_at (hf : smooth_at I I' f x) : mdifferentiable_at I I' f x :=
hf.mdifferentiable_at le_top

lemma smooth_on.mdifferentiable_on (hf : smooth_on I I' f s) : mdifferentiable_on I I' f s :=
hf.mdifferentiable_on le_top

lemma smooth.mdifferentiable (hf : smooth I I' f) : mdifferentiable I I' f :=
cont_mdiff.mdifferentiable hf le_top

lemma smooth.mdifferentiable_at (hf : smooth I I' f) : mdifferentiable_at I I' f x :=
hf.mdifferentiable x

lemma smooth.mdifferentiable_within_at (hf : smooth I I' f) :
  mdifferentiable_within_at I I' f s x :=
hf.mdifferentiable_at.mdifferentiable_within_at


/-! ### Smoothness of the projection in a basic smooth bundle -/

namespace vector_bundle_core

-- cont_mdiff_at_iff_target doesn't hold anymore!?

-- /-- A version of `cont_mdiff_at_iff_target` when the codomain is the total space of
--   a smooth vector bundle. The continuity condition in the RHS is weaker. -/
-- lemma cont_mdiff_at_iff_target {ι} (Z : vector_bundle_core 𝕜 M E' ι) {f : N → Z.total_space}
--   {x : N} {n : ℕ∞} :
--   cont_mdiff_at J (I.prod 𝓘(𝕜, E')) n f x ↔ continuous_at (bundle.total_space.proj ∘ f) x ∧
--     cont_mdiff_at J 𝓘(𝕜, E × E') n (ext_chart_at (I.prod 𝓘(𝕜, E')) (f x) ∘ f) x :=
-- begin
--   rw [cont_mdiff_at_iff_target, and.congr_left_iff],
--   refine λ hf, ⟨λ h, Z.continuous_proj.continuous_at.comp h, λ h, _⟩,
--   exact (Z.local_triv (achart _ (f x).1))
--     .continuous_at_of_comp_left h (mem_chart_source _ _) (h.prod hf.continuous_at.snd),
--   refine Z.local_triv .continuous_at_of_comp_left h
--     (mem_base_set_trivialization_at E' Z _) _,
--   suffices : continuous_at (λ x, ((f x).1, (trivialization_at E' Z (f x).proj (f x)).2)) x,
--   { refine this.congr sorry, },
--   refine h.prod _, sorry,
-- end


end vector_bundle_core

namespace bundle -- move to vector_bundle.basic

variables
  {Z : M → Type*} [topological_space (total_space Z)] [∀ b, topological_space (Z b)]
  [∀ b, add_comm_monoid (Z b)] [∀ b, module 𝕜 (Z b)]
  [fiber_bundle F₁ Z] [vector_bundle 𝕜 F₁ Z] [smooth_vector_bundle F₁ Z I]

/-- Characterization of C^n functions into a smooth vector bundle. -/
lemma cont_mdiff_within_at_total_space (f : N → total_space Z) {s : set N} {x₀ : N} :
  cont_mdiff_within_at J (I.prod (𝓘(𝕜, F₁))) n f s x₀ ↔
  cont_mdiff_within_at J I n (λ x, (f x).proj) s x₀ ∧
  cont_mdiff_within_at J 𝓘(𝕜, F₁) n (λ x, (trivialization_at F₁ Z (f x₀).proj (f x)).2) s x₀ :=
begin
  simp only [cont_mdiff_within_at_iff_target] {single_pass := tt},
  rw [and_and_and_comm, ← continuous_within_at_total_space, and.congr_right_iff],
  intros hf,
  simp_rw [model_with_corners_self_prod, fiber_bundle.ext_chart_at, function.comp,
    local_equiv.trans_apply, local_equiv.prod_coe, local_equiv.refl_coe,
    ext_chart_at_self_apply, model_with_corners_self_coe, id_def],
  refine (cont_mdiff_within_at_prod_iff _).trans _, -- rw doesn't do this?
  have h1 : (λ x, (f x).proj) ⁻¹' (trivialization_at F₁ Z (f x₀).proj).base_set ∈ 𝓝[s] x₀ :=
    ((continuous_proj F₁ Z).continuous_within_at.comp hf (maps_to_image f s))
      .preimage_mem_nhds_within
      ((trivialization.open_base_set _).mem_nhds (mem_base_set_trivialization_at F₁ Z _)),
  refine and_congr (eventually_eq.cont_mdiff_within_at_iff (eventually_of_mem h1 $ λ x hx, _) _)
    iff.rfl,
  { simp_rw [function.comp, local_homeomorph.coe_coe, trivialization.coe_coe],
    rw [trivialization.coe_fst'],
    exact hx },
  { simp only with mfld_simps },
end

/-- Characterization of C^n functions into a smooth vector bundle. -/
lemma cont_mdiff_at_total_space (f : N → total_space Z) (x₀ : N) :
  cont_mdiff_at J (I.prod (𝓘(𝕜, F₁))) n f x₀ ↔
  cont_mdiff_at J I n (λ x, (f x).proj) x₀ ∧
  cont_mdiff_at J 𝓘(𝕜, F₁) n (λ x, (trivialization_at F₁ Z (f x₀).proj (f x)).2) x₀ :=
by { simp_rw [← cont_mdiff_within_at_univ], exact cont_mdiff_within_at_total_space f }

variables (Z)
lemma cont_mdiff_proj : cont_mdiff (I.prod 𝓘(𝕜, F₁)) I n (π Z) :=
begin
  intro x,
  rw [cont_mdiff_at, cont_mdiff_within_at_iff'],
  refine ⟨(continuous_proj F₁ Z).continuous_within_at, _⟩,
  simp_rw [(∘), fiber_bundle.ext_chart_at],
  apply cont_diff_within_at_fst.congr,
  { rintros ⟨a, b⟩ hab,
    simp only with mfld_simps at hab,
    have : ((chart_at H x.1).symm (I.symm a), b) ∈ (trivialization_at F₁ Z x.fst).target,
    { simp only [hab] with mfld_simps },
    simp only [trivialization.proj_symm_apply _ this, hab] with mfld_simps },
  { simp only with mfld_simps }
end

lemma smooth_proj : smooth (I.prod 𝓘(𝕜, F₁)) I (π Z) :=
cont_mdiff_proj Z

lemma cont_mdiff_on_proj {s : set (total_space Z)} :
  cont_mdiff_on (I.prod 𝓘(𝕜, F₁)) I n (π Z) s :=
(bundle.cont_mdiff_proj Z).cont_mdiff_on

lemma smooth_on_proj {s : set (total_space Z)} :
  smooth_on (I.prod 𝓘(𝕜, F₁)) I (π Z) s :=
cont_mdiff_on_proj Z

lemma cont_mdiff_at_proj {p : total_space Z} :
  cont_mdiff_at (I.prod 𝓘(𝕜, F₁)) I n
    (π Z) p :=
(bundle.cont_mdiff_proj Z).cont_mdiff_at

lemma smooth_at_proj {p : total_space Z} :
  smooth_at (I.prod 𝓘(𝕜, F₁)) I (π Z) p :=
bundle.cont_mdiff_at_proj Z

lemma cont_mdiff_within_at_proj
  {s : set (total_space Z)}
  {p : total_space Z} :
  cont_mdiff_within_at (I.prod 𝓘(𝕜, F₁)) I n (π Z) s p :=
(bundle.cont_mdiff_at_proj Z).cont_mdiff_within_at

lemma smooth_within_at_proj
  {s : set (total_space Z)}
  {p : total_space Z} :
  smooth_within_at (I.prod 𝓘(𝕜, F₁)) I (π Z) s p :=
bundle.cont_mdiff_within_at_proj Z

section mfderiv

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']
   [smooth_manifold_with_corners J N]

/-! ### Computations with `mfderiv` -/

/-- The derivative of the projection `M × M' → M` is the projection `TM × TM' → TM` -/
lemma mfderiv_fst (x : M × M') :
  mfderiv (I.prod I') I prod.fst x = continuous_linear_map.fst 𝕜 E E' :=
begin
  simp_rw [mfderiv, if_pos smooth_at_fst.mdifferentiable_at, written_in_ext_chart_at,
    ext_chart_at_prod, function.comp, local_equiv.prod_coe, local_equiv.prod_coe_symm],
  have : unique_diff_within_at 𝕜 (range (I.prod I')) (ext_chart_at (I.prod I') x x) :=
  (I.prod I').unique_diff _ (mem_range_self _),
  refine (filter.eventually_eq.fderiv_within_eq this _ _).trans _,
  swap 3,
  { exact (ext_chart_at I x.1).right_inv ((ext_chart_at I x.1).maps_to $
      mem_ext_chart_source I x.1) },
  { refine eventually_of_mem (ext_chart_at_target_mem_nhds_within (I.prod I') x)
      (λ y hy, local_equiv.right_inv _ _),
    rw [ext_chart_at_prod] at hy,
    exact hy.1 },
  exact fderiv_within_fst this,
end

/-- The derivative of the projection `M × M' → M'` is the projection `TM × TM' → TM'` -/
lemma mfderiv_snd (x : M × M') :
  mfderiv (I.prod I') I' prod.snd x = continuous_linear_map.snd 𝕜 E E' :=
begin
  simp_rw [mfderiv, if_pos smooth_at_snd.mdifferentiable_at, written_in_ext_chart_at,
    ext_chart_at_prod, function.comp, local_equiv.prod_coe, local_equiv.prod_coe_symm],
  have : unique_diff_within_at 𝕜 (range (I.prod I')) (ext_chart_at (I.prod I') x x) :=
  (I.prod I').unique_diff _ (mem_range_self _),
  refine (filter.eventually_eq.fderiv_within_eq this _ _).trans _,
  swap 3,
  { exact (ext_chart_at I' x.2).right_inv ((ext_chart_at I' x.2).maps_to $
      mem_ext_chart_source I' x.2) },
  { refine eventually_of_mem (ext_chart_at_target_mem_nhds_within (I.prod I') x)
      (λ y hy, local_equiv.right_inv _ _),
    rw [ext_chart_at_prod] at hy,
    exact hy.2 },
  exact fderiv_within_snd this,
end

lemma mfderiv_prod_eq_add {f : N × M → M'} {p : N × M}
  (hf : mdifferentiable_at (J.prod I) I' f p) :
  mfderiv (J.prod I) I' f p =
  (show F × E →L[𝕜] E', from mfderiv (J.prod I) I' (λ (z : N × M), f (z.1, p.2)) p +
  mfderiv (J.prod I) I' (λ (z : N × M), f (p.1, z.2)) p) :=
begin
  dsimp only,
  rw [← @prod.mk.eta _ _ p] at hf,
  rw [mfderiv_comp p (by apply hf) (smooth_fst.prod_mk smooth_const).mdifferentiable_at,
    mfderiv_comp p (by apply hf) (smooth_const.prod_mk smooth_snd).mdifferentiable_at,
    ← continuous_linear_map.comp_add,
    smooth_fst.mdifferentiable_at.mfderiv_prod smooth_const.mdifferentiable_at,
    smooth_const.mdifferentiable_at.mfderiv_prod smooth_snd.mdifferentiable_at,
    mfderiv_fst, mfderiv_snd, mfderiv_const, mfderiv_const],
  symmetry,
  convert continuous_linear_map.comp_id _,
  { exact continuous_linear_map.fst_prod_zero_add_zero_prod_snd },
  simp_rw [prod.mk.eta],
end

open bundle
variables
  {Z₂ : M' → Type*} [topological_space (total_space Z₂)] [∀ b, topological_space (Z₂ b)]
  [∀ b, add_comm_monoid (Z₂ b)] [∀ b, module 𝕜 (Z₂ b)]
  [fiber_bundle F₂ Z₂] [vector_bundle 𝕜 F₂ Z₂] [smooth_vector_bundle F₂ Z₂ I']

variables (I I' Z Z₂ F₁ F₂)

/-- When `ϕ` is a continuous linear map that changes vectors in charts around `x` to vectors
  in charts around `y`, `in_coordinates' Z Z₂ x₀ x y₀ y ϕ` is a coordinate change of this continuous
  linear map that makes sense from charts around `x₀` to charts around `y₀`
  by composing it with appropriate coordinate changes given by smooth vector bundles `Z` and `Z₂`.
-/
def in_coordinates' (x₀ x : M) (y₀ y : M') (ϕ : F₁ →L[𝕜] F₂) : F₁ →L[𝕜] F₂ :=
((trivialization_at F₂ Z₂ y).coord_changeL 𝕜 (trivialization_at F₂ Z₂ y₀) y : F₂ →L[𝕜] F₂) ∘L ϕ ∘L
((trivialization_at F₁ Z x₀).coord_changeL 𝕜 (trivialization_at F₁ Z x) x : F₁ →L[𝕜] F₁)

/-- When `ϕ x` is a continuous linear map that changes vectors in charts around `f x` to vectors
  in charts around `g x`, `in_coordinates I I' f g ϕ x₀ x` is a coordinate change of this continuous
  linear map that makes sense from charts around `f x₀` to charts around `g x₀`
  by composing it with appropriate coordinate changes. -/
noncomputable def in_coordinates (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') :
  N → N → E →L[𝕜] E' :=
λ x₀ x, in_coordinates' E E' (tangent_space I) (tangent_space I') (f x₀) (f x) (g x₀) (g x) (ϕ x)

-- /-- The map `in_coordinates'` is trivial if `M'` is the -/
-- lemma in_coordinates'_tangent_bundle_core_model_space
--   (x₀ x : H) (y₀ y : H') (ϕ : E →L[𝕜] E') :
--     in_coordinates' E E' (tangent_space I) (tangent_space I') x₀ x y₀ y ϕ = ϕ :=
-- by simp_rw [in_coordinates', tangent_bundle_core_coord_change_achart,
--   continuous_linear_map.id_comp, continuous_linear_map.comp_id]

variables {I I'}

lemma cont_mdiff_within_at.mfderiv {s : set N} {x : N} (f : N → M → M') (g : N → M)
  (hf : cont_mdiff_within_at (J.prod I) I' n (function.uncurry f) (s ×ˢ univ) (x, g x))
  (hg : cont_mdiff_within_at J I m g s x) (hmn : m + 1 ≤ n) :
  cont_mdiff_within_at J 𝓘(𝕜, E →L[𝕜] E') m
    (in_coordinates I I' g (λ x, f x (g x)) (λ x', mfderiv I I' (f x') (g x')) x) s x :=
sorry

/-- The appropriate (more general) formulation of `cont_mdiff_at.mfderiv''`. -/
lemma cont_mdiff_at.mfderiv''' {x : N} (f : N → M → M') (g : N → M)
  (hf : cont_mdiff_at (J.prod I) I' n (function.uncurry f) (x, g x))
  (hg : cont_mdiff_at J I m g x) (hmn : m + 1 ≤ n) :
  cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (in_coordinates I I' g (λ x, f x (g x)) (λ x', mfderiv I I' (f x') (g x')) x) x :=
begin
  sorry
  -- have h4f : continuous_at (λ x, f x (g x)) x,
  -- { apply continuous_at.comp (by apply hf.continuous_at) (continuous_at_id.prod hg.continuous_at) },
  -- have h3f := cont_mdiff_at_iff_cont_mdiff_at_nhds.mp (hf.of_le $ (self_le_add_left 1 m).trans hmn),
  -- have h2f : ∀ᶠ x₂ in 𝓝 x, cont_mdiff_at I I' 1 (f x₂) (g x₂),
  -- { refine ((continuous_at_id.prod hg.continuous_at).tendsto.eventually h3f).mono (λ x hx, _),
  --   exact hx.comp (g x) (cont_mdiff_at_const.prod_mk cont_mdiff_at_id) },
  -- have h2g := hg.continuous_at.preimage_mem_nhds (ext_chart_at_source_mem_nhds I (g x)),
  -- have : cont_diff_within_at 𝕜 m (λ x', fderiv_within 𝕜
  --   (ext_chart_at I' (f x (g x)) ∘ f ((ext_chart_at J x).symm x') ∘ (ext_chart_at I (g x)).symm)
  --   (range I) (ext_chart_at I (g x) (g ((ext_chart_at J x).symm x'))))
  --   (range J) (ext_chart_at J x x),
  -- { rw [cont_mdiff_at_iff] at hf hg,
  --   simp_rw [function.comp, uncurry, ext_chart_at_prod, local_equiv.prod_coe_symm] at hf ⊢,
  --   refine (cont_diff_within_at_fderiv_within _
  --     (hg.2.mono_of_mem _) I.unique_diff hmn _ _ _ _).mono_of_mem _,
  --   swap 3,
  --   { simp_rw [function.comp, ext_chart_at_to_inv], exact hf.2 },
  --   { refine (ext_chart_at J x).target ∩
  --     (λ x', (ext_chart_at J x).symm x') ⁻¹' (g ⁻¹' (ext_chart_at I (g x)).source) },
  --   { exact mem_of_superset self_mem_nhds_within
  --       ((inter_subset_left _ _).trans $ ext_chart_at_target_subset_range J x) },
  --   { simp_rw [mem_inter_iff, mem_preimage, ext_chart_at_to_inv],
  --     exact ⟨local_equiv.maps_to _ (mem_ext_chart_source J x), mem_ext_chart_source I (g x)⟩ },
  --   { simp_rw [model_with_corners.range_prod],
  --     exact set.prod_mono ((inter_subset_left _ _).trans $ ext_chart_at_target_subset_range J x)
  --       subset_rfl },
  --   { refine eventually_of_forall (λ x', mem_range_self _) },
  --   swap 2,
  --   { refine inter_mem (ext_chart_at_target_mem_nhds_within J x) _,
  --     refine nhds_within_le_nhds (ext_chart_preimage_mem_nhds' _ _ (mem_ext_chart_source J x) _),
  --     exact hg.1.preimage_mem_nhds (ext_chart_at_source_mem_nhds I (g x)) },
  --   simp_rw [function.comp, model_with_corners.range_prod, ext_chart_at_to_inv],
  --   refine mem_of_superset self_mem_nhds_within _,
  --   refine image_prod_mk_subset_prod.trans (prod_mono _ _),
  --   { rw [image_id'],
  --     exact ((inter_subset_left _ _).trans $ ext_chart_at_target_subset_range J x) },
  --   rintro _ ⟨x', hx', rfl⟩,
  --   refine ext_chart_at_target_subset_range I (g x) _,
  --   exact (ext_chart_at I (g x)).maps_to hx'.2 },
  -- have : cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
  --   (λ x', fderiv_within 𝕜 (ext_chart_at I' (f x (g x)) ∘ f x' ∘ (ext_chart_at I (g x)).symm)
  --   (range I) (ext_chart_at I (g x) (g x'))) x,
  -- { simp_rw [cont_mdiff_at_iff_source_of_mem_source (mem_chart_source G x),
  --     cont_mdiff_within_at_iff_cont_diff_within_at, function.comp],
  --   exact this },
  -- have : cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
  --   (λ x', fderiv_within 𝕜 (ext_chart_at I' (f x (g x)) ∘ (ext_chart_at I' (f x' (g x'))).symm ∘
  --     written_in_ext_chart_at I I' (g x') (f x') ∘ ext_chart_at I (g x') ∘
  --     (ext_chart_at I (g x)).symm) (range I) (ext_chart_at I (g x) (g x'))) x,
  -- { refine this.congr_of_eventually_eq _,
  --   filter_upwards [h2g, h2f],
  --   intros x₂ hx₂ h2x₂,
  --   have : ∀ x' ∈ (ext_chart_at I (g x)).symm ⁻¹' (ext_chart_at I (g x₂)).source ∩
  --       (ext_chart_at I (g x)).symm ⁻¹' (f x₂ ⁻¹' (ext_chart_at I' (f x₂ (g x₂))).source),
  --     (ext_chart_at I' (f x (g x)) ∘ (ext_chart_at I' (f x₂ (g x₂))).symm ∘
  --     written_in_ext_chart_at I I' (g x₂) (f x₂) ∘ ext_chart_at I (g x₂) ∘
  --     (ext_chart_at I (g x)).symm) x' =
  --     ext_chart_at I' (f x (g x)) (f x₂ ((ext_chart_at I (g x)).symm x')),
  --   { rintro x' ⟨hx', h2x'⟩,
  --     simp_rw [written_in_ext_chart_at, function.comp_apply],
  --     rw [(ext_chart_at I (g x₂)).left_inv hx', (ext_chart_at I' (f x₂ (g x₂))).left_inv h2x'] },
  --   refine filter.eventually_eq.fderiv_within_eq_nhds (I.unique_diff _ $ mem_range_self _) _,
  --   refine eventually_of_mem (inter_mem _ _) this,
  --   { exact ext_chart_preimage_mem_nhds' _ _ hx₂ (ext_chart_at_source_mem_nhds I (g x₂)) },
  --   refine ext_chart_preimage_mem_nhds' _ _ hx₂ _,
  --   exact (h2x₂.continuous_at).preimage_mem_nhds (ext_chart_at_source_mem_nhds _ _) },
  -- /- The conclusion is the same as the following, when unfolding coord_change of
  --   `tangent_bundle_core` -/
  -- change cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
  --   (λ x', (fderiv_within 𝕜 (ext_chart_at I' (f x (g x)) ∘ (ext_chart_at I' (f x' (g x'))).symm)
  --       (range I') (ext_chart_at I' (f x' (g x')) (f x' (g x')))).comp
  --       ((mfderiv I I' (f x') (g x')).comp (fderiv_within 𝕜 (ext_chart_at I (g x') ∘
  --       (ext_chart_at I (g x)).symm) (range I) (ext_chart_at I (g x) (g x'))))) x,
  -- refine this.congr_of_eventually_eq _,
  -- filter_upwards [h2g, h2f,
  --   h4f.preimage_mem_nhds (ext_chart_at_source_mem_nhds I' (f x (g x)))],
  -- intros x₂ hx₂ h2x₂ h3x₂,
  -- symmetry,
  -- rw [(h2x₂.mdifferentiable_at le_rfl).mfderiv],
  -- have hI := (cont_diff_within_at_ext_coord_change I (g x₂) (g x) $
  --   local_equiv.mem_symm_trans_source _ hx₂ $ mem_ext_chart_source I (g x₂))
  --   .differentiable_within_at le_top,
  -- have hI' := (cont_diff_within_at_ext_coord_change I' (f x (g x)) (f x₂ (g x₂)) $
  --   local_equiv.mem_symm_trans_source _
  --   (mem_ext_chart_source I' (f x₂ (g x₂))) h3x₂).differentiable_within_at le_top,
  -- have h3f := (h2x₂.mdifferentiable_at le_rfl).2,
  -- refine fderiv_within.comp₃ _ hI' h3f hI _ _ _ _ (I.unique_diff _ $ mem_range_self _),
  -- { exact λ x _, mem_range_self _ },
  -- { exact λ x _, mem_range_self _ },
  -- { simp_rw [written_in_ext_chart_at, function.comp_apply,
  --     (ext_chart_at I (g x₂)).left_inv (mem_ext_chart_source I (g x₂))] },
  -- { simp_rw [function.comp_apply, (ext_chart_at I (g x)).left_inv hx₂] }
end

end mfderiv

/-! ### The tangent map of a smooth function is smooth -/

section tangent_map

include Is I's

/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative
is `C^m` when `m+1 ≤ n`. -/
theorem cont_mdiff_on.cont_mdiff_on_tangent_map_within
  (hf : cont_mdiff_on I I' n f s) (hmn : m + 1 ≤ n) (hs : unique_mdiff_on I s) :
  cont_mdiff_on I.tangent I'.tangent m (tangent_map_within I I' f s)
  (π (tangent_space I) ⁻¹' s) :=
begin
  intros x hx,
  have hm' : m ≤ n := (self_le_add_right m 1).trans hmn,
  rw [cont_mdiff_within_at_total_space],
  refine ⟨(hf.of_le hm' x.proj hx).comp _ (cont_mdiff_proj (tangent_space I)).cont_mdiff_at
    .cont_mdiff_within_at (maps_to_preimage _ s), _⟩,
  simp only with mfld_simps,
  simp only [tangent_map_within],
  sorry
end

/-- If a function is `C^n` on a domain with unique derivatives, with `1 ≤ n`, then its bundled
derivative is continuous there. -/
theorem cont_mdiff_on.continuous_on_tangent_map_within
  (hf : cont_mdiff_on I I' n f s) (hmn : 1 ≤ n) (hs : unique_mdiff_on I s) :
  continuous_on (tangent_map_within I I' f s) (π (tangent_space I) ⁻¹' s) :=
(hf.cont_mdiff_on_tangent_map_within (show 0 + 1 ≤ n, from hmn) hs).continuous_on

/-- If a function is `C^n`, then its bundled derivative is `C^m` when `m+1 ≤ n`. -/
theorem cont_mdiff.cont_mdiff_tangent_map
  (hf : cont_mdiff I I' n f) (hmn : m + 1 ≤ n) :
  cont_mdiff I.tangent I'.tangent m (tangent_map I I' f) :=
begin
  rw ← cont_mdiff_on_univ at hf ⊢,
  convert hf.cont_mdiff_on_tangent_map_within hmn unique_mdiff_on_univ,
  rw tangent_map_within_univ
end

/-- If a function is `C^n`, with `1 ≤ n`, then its bundled derivative is continuous. -/
theorem cont_mdiff.continuous_tangent_map
  (hf : cont_mdiff I I' n f) (hmn : 1 ≤ n) :
  continuous (tangent_map I I' f) :=
begin
  rw ← cont_mdiff_on_univ at hf,
  rw continuous_iff_continuous_on_univ,
  convert hf.continuous_on_tangent_map_within hmn unique_mdiff_on_univ,
  rw tangent_map_within_univ
end

end tangent_map

-- don't port
-- /-- If an element of `E'` is invariant under all coordinate changes, then one can define a
-- corresponding section of the fiber bundle, which is smooth. This applies in particular to the
-- zero section of a vector bundle. Another example (not yet defined) would be the identity
-- section of the endomorphism bundle of a vector bundle. -/
-- lemma smooth_const_section {ι} (Z : vector_bundle_core 𝕜 M F ι) (v : E')
--   (h : ∀ (i j : atlas H M), ∀ x ∈ i.1.source ∩ j.1.source, Z.coord_change i j (i.1 x) v = v) :
--   smooth I (I.prod 𝓘(𝕜, E'))
--     (show M → total_space Z, from λ x, ⟨x, v⟩) :=
-- begin
--   assume x,
--   rw [cont_mdiff_at, cont_mdiff_within_at_iff'],
--   split,
--   { apply continuous.continuous_within_at,
--     apply fiber_bundle_core.continuous_const_section,
--     assume i j y hy,
--     exact h _ _ _ hy },
--   { have : cont_diff 𝕜 ⊤ (λ (y : E), (y, v)) := cont_diff_id.prod cont_diff_const,
--     apply this.cont_diff_within_at.congr,
--     { assume y hy,
--       simp only with mfld_simps at hy,
--       simp only [chart, hy, chart_at, prod.mk.inj_iff, to_vector_bundle_core]
--         with mfld_simps,
--       apply h,
--       simp only [hy, subtype.val_eq_coe] with mfld_simps },
--     { simp only [chart, chart_at, prod.mk.inj_iff, to_vector_bundle_core]
--         with mfld_simps,
--       apply h,
--       simp only [subtype.val_eq_coe] with mfld_simps } }
-- end

end bundle
open bundle

/-! ### Smoothness of the tangent bundle projection -/

namespace tangent_bundle

include Is

-- lemma cont_mdiff_proj :
--   cont_mdiff I.tangent I n (proj I M) :=
-- bundle.cont_mdiff_proj _

-- lemma smooth_proj : smooth I.tangent I (proj I M) :=
-- bundle.smooth_proj _

-- lemma cont_mdiff_on_proj {s : set (tangent_bundle I M)} :
--   cont_mdiff_on I.tangent I n (proj I M) s :=
-- bundle.cont_mdiff_on_proj _

-- lemma smooth_on_proj {s : set (tangent_bundle I M)} :
--   smooth_on I.tangent I (proj I M) s :=
-- bundle.smooth_on_proj _

-- lemma cont_mdiff_at_proj {p : tangent_bundle I M} :
--   cont_mdiff_at I.tangent I n
--     (proj I M) p :=
-- bundle.cont_mdiff_at_proj _

-- lemma smooth_at_proj {p : tangent_bundle I M} :
--   smooth_at I.tangent I (proj I M) p :=
-- bundle.smooth_at_proj _

-- lemma cont_mdiff_within_at_proj
--   {s : set (tangent_bundle I M)} {p : tangent_bundle I M} :
--   cont_mdiff_within_at I.tangent I n
--     (proj I M) s p :=
-- bundle.cont_mdiff_within_at_proj _

-- lemma smooth_within_at_proj
--   {s : set (tangent_bundle I M)} {p : tangent_bundle I M} :
--   smooth_within_at I.tangent I
--     (proj I M) s p :=
-- bundle.smooth_within_at_proj _

variables (I M)
/-- The zero section of the tangent bundle -/
def zero_section : M → tangent_bundle I M := λ x, ⟨x, 0⟩
variables {I M}


lemma smooth_zero_section : smooth I I.tangent (zero_section I M) :=
begin
  intro x,
  rw [bundle.cont_mdiff_at_total_space],
  refine ⟨cont_mdiff_at_id, _⟩,
  sorry,
  -- simp only [tangent_bundle_core, continuous_linear_map.map_zero, continuous_linear_map.coe_coe]
  --   with mfld_simps,
end

open bundle

/-- The derivative of the zero section of the tangent bundle maps `⟨x, v⟩` to `⟨⟨x, 0⟩, ⟨v, 0⟩⟩`.

Note that, as currently framed, this is a statement in coordinates, thus reliant on the choice
of the coordinate system we use on the tangent bundle.

However, the result itself is coordinate-dependent only to the extent that the coordinates
determine a splitting of the tangent bundle.  Moreover, there is a canonical splitting at each
point of the zero section (since there is a canonical horizontal space there, the tangent space
to the zero section, in addition to the canonical vertical space which is the kernel of the
derivative of the projection), and this canonical splitting is also the one that comes from the
coordinates on the tangent bundle in our definitions. So this statement is not as crazy as it
may seem.

TODO define splittings of vector bundles; state this result invariantly. -/
lemma tangent_map_tangent_bundle_pure (p : tangent_bundle I M) :
  tangent_map I I.tangent (tangent_bundle.zero_section I M) p = ⟨⟨p.1, 0⟩, ⟨p.2, 0⟩⟩ :=
begin
  rcases p with ⟨x, v⟩,
  have N : I.symm ⁻¹' (chart_at H x).target ∈ 𝓝 (I ((chart_at H x) x)),
  { apply is_open.mem_nhds,
    apply (local_homeomorph.open_target _).preimage I.continuous_inv_fun,
    simp only with mfld_simps },
  have A : mdifferentiable_at I I.tangent (λ x, @total_space_mk M (tangent_space I) x 0) x :=
    tangent_bundle.smooth_zero_section.mdifferentiable_at,
  have B : fderiv_within 𝕜 (λ (x_1 : E), (x_1, (0 : E))) (set.range ⇑I) (I ((chart_at H x) x)) v
    = (v, 0),
  { rw [fderiv_within_eq_fderiv, differentiable_at.fderiv_prod],
    { simp },
    { exact differentiable_at_id' },
    { exact differentiable_at_const _ },
    { exact model_with_corners.unique_diff_at_image I },
    { exact differentiable_at_id'.prod (differentiable_at_const _) } },
  simp only [tangent_bundle.zero_section, tangent_map, mfderiv,
    A, if_pos, chart_at, fiber_bundle.charted_space_chart_at,
    tangent_bundle_core, function.comp, continuous_linear_map.map_zero] with mfld_simps,
  rw ← fderiv_within_inter N (I.unique_diff (I ((chart_at H x) x)) (set.mem_range_self _)) at B,
  rw [← fderiv_within_inter N (I.unique_diff (I ((chart_at H x) x)) (set.mem_range_self _)), ← B],
  congr' 2,
  apply fderiv_within_congr _ (λ y hy, _),
  { simp only [prod.mk.inj_iff] with mfld_simps, sorry },
  { apply unique_diff_within_at.inter (I.unique_diff _ _) N,
    simp only with mfld_simps },
  { simp only with mfld_simps at hy,
    simp only [hy, prod.mk.inj_iff] with mfld_simps, sorry },
end

end tangent_bundle
