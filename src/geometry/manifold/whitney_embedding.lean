/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import geometry.manifold.partition_of_unity

/-!
# Whitney embedding theorem

In this file we prove a version of the Whitney embedding theorem: for any compact real manifold `M`,
for sufficiently large `n` there exists a smooth embedding `M → ℝ^n`.

## TODO

* Prove the weak Whitney embedding theorem: any `σ`-compact smooth `m`-dimensional manifold can be
  embedded into `ℝ^(2m+1)`. This requires a version of Sard's theorem: for a locally Lipschitz
  continuous map `f : ℝ^m → ℝ^n`, `m < n`, the range has Hausdorff dimension at most `m`, hence it
  has measure zero.

## Tags

partition of unity, smooth bump function, whitney theorem
-/

universes uE uF uH uM
variables
{E : Type uE} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
{H : Type uH} [topological_space H] {I : model_with_corners ℝ E H}
{M : Type uM} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

open function filter finite_dimensional set
open_locale topological_space manifold classical filter big_operators

noncomputable theory

namespace smooth_bump_covering

variables {s : set M} {U : M → set M} (fs : smooth_bump_covering I s)

variables [t2_space M] [fintype fs.ι] (f : smooth_bump_covering I (univ : set M))
  [fintype f.ι]

/-- Smooth embedding of `M` into `(E × ℝ) ^ f.ι`. -/
def embedding_pi_tangent : C^∞⟮I, M; 𝓘(ℝ, fs.ι → (E × ℝ)), fs.ι → (E × ℝ)⟯ :=
{ to_fun := λ x i, (fs i x • ext_chart_at I (fs.c i) x, fs i x),
  times_cont_mdiff_to_fun := times_cont_mdiff_pi_space.2 $ λ i,
    ((fs i).smooth_smul times_cont_mdiff_on_ext_chart_at).prod_mk_space ((fs i).smooth) }

local attribute [simp] lemma embedding_pi_tangent_coe :
  ⇑fs.embedding_pi_tangent = λ x i, (fs i x • ext_chart_at I (fs.c i) x, fs i x) :=
rfl

lemma embedding_pi_tangent_inj_on : inj_on fs.embedding_pi_tangent s :=
begin
  intros x hx y hy h,
  simp only [embedding_pi_tangent_coe, funext_iff] at h,
  obtain ⟨h₁, h₂⟩ := prod.mk.inj_iff.1 (h (fs.ind x hx)),
  rw [fs.apply_ind x hx] at h₂,
  rw [← h₂, fs.apply_ind x hx, one_smul, one_smul] at h₁,
  have := fs.mem_ext_chart_at_source_of_eq_one h₂.symm,
  exact (ext_chart_at I (fs.c _)).inj_on (fs.mem_ext_chart_at_ind_source x hx) this h₁
end

lemma embedding_pi_tangent_injective :
  injective f.embedding_pi_tangent :=
injective_iff_inj_on_univ.2 f.embedding_pi_tangent_inj_on

lemma comp_embedding_pi_tangent_mfderiv (x : M) (hx : x ∈ s) :
  ((continuous_linear_map.fst ℝ E ℝ).comp
    (@continuous_linear_map.proj ℝ _ fs.ι (λ _, E × ℝ) _ _
      (λ _, infer_instance) (fs.ind x hx))).comp
      (mfderiv I 𝓘(ℝ, fs.ι → (E × ℝ)) fs.embedding_pi_tangent x) =
  mfderiv I I (chart_at H (fs.c (fs.ind x hx))) x :=
begin
  set L := ((continuous_linear_map.fst ℝ E ℝ).comp
    (@continuous_linear_map.proj ℝ _ fs.ι (λ _, E × ℝ) _ _ (λ _, infer_instance) (fs.ind x hx))),
  have := (L.has_mfderiv_at.comp x (fs.embedding_pi_tangent.mdifferentiable_at.has_mfderiv_at)),
  convert has_mfderiv_at_unique this _,
  refine (has_mfderiv_at_ext_chart_at I (fs.mem_chart_at_ind_source x hx)).congr_of_eventually_eq _,
  refine (fs.eventually_eq_one x hx).mono (λ y hy, _),
  simp only [embedding_pi_tangent_coe, continuous_linear_map.coe_comp', (∘),
    continuous_linear_map.coe_fst', continuous_linear_map.proj_apply],
  rw [hy, pi.one_apply, one_smul]
end

lemma embedding_pi_tangent_ker_mfderiv (x : M) (hx : x ∈ s) :
  (mfderiv I 𝓘(ℝ, fs.ι → (E × ℝ)) fs.embedding_pi_tangent x).ker = ⊥ :=
begin
  apply bot_unique,
  rw [← (mdifferentiable_chart I (fs.c (fs.ind x hx))).ker_mfderiv_eq_bot
    (fs.mem_chart_at_ind_source x hx), ← comp_embedding_pi_tangent_mfderiv],
  exact linear_map.ker_le_ker_comp _ _
end

lemma embedding_pi_tangent_injective_mfderiv (x : M) (hx : x ∈ s) :
  injective (mfderiv I 𝓘(ℝ, fs.ι → (E × ℝ)) fs.embedding_pi_tangent x) :=
linear_map.ker_eq_bot.1 (fs.embedding_pi_tangent_ker_mfderiv x hx)

/-- Baby version of the Whitney weak embedding theorem: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be immersed into the `n`-dimensional
Euclidean space. -/
lemma exists_immersion_finrank (f : smooth_bump_covering I (univ : set M))
  [fintype f.ι] :
  ∃ (n : ℕ) (e : M → euclidean_space ℝ (fin n)), smooth I (𝓡 n) e ∧
    injective e ∧ ∀ x : M, injective (mfderiv I (𝓡 n) e x) :=
begin
  set F := euclidean_space ℝ (fin $ finrank ℝ (f.ι → (E × ℝ))),
  letI : finite_dimensional ℝ (E × ℝ) := by apply_instance,
  set eEF : (f.ι → (E × ℝ)) ≃L[ℝ] F :=
    continuous_linear_equiv.of_finrank_eq finrank_euclidean_space_fin.symm,
  refine ⟨_, eEF ∘ f.embedding_pi_tangent,
    eEF.to_diffeomorph.smooth.comp f.embedding_pi_tangent.smooth,
    eEF.injective.comp f.embedding_pi_tangent_injective, λ x, _⟩,
  rw [mfderiv_comp _ eEF.differentiable_at.mdifferentiable_at
    f.embedding_pi_tangent.mdifferentiable_at, eEF.mfderiv_eq],
  exact eEF.injective.comp (f.embedding_pi_tangent_injective_mfderiv _ trivial)
end

end smooth_bump_covering

/-- Baby version of the Whitney weak embedding theorem: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be embedded into the `n`-dimensional
Euclidean space. -/
lemma exists_embedding_finrank_of_compact [t2_space M] [compact_space M] :
  ∃ (n : ℕ) (e : M → euclidean_space ℝ (fin n)), smooth I (𝓡 n) e ∧
    closed_embedding e ∧ ∀ x : M, injective (mfderiv I (𝓡 n) e x) :=
begin
  rcases (smooth_bump_covering.choice I M).exists_immersion_finrank
    with ⟨n, e, hsmooth, hinj, hinj_mfderiv⟩,
  exact ⟨n, e, hsmooth, hsmooth.continuous.closed_embedding hinj, hinj_mfderiv⟩
end
