/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.normed_space.operator_norm
import analysis.locally_convex.bounded

/-!
# Compact operators

In this file we define compact linear operators between two topological vector spaces (TVS).

## Main definitions

* `is_compact_operator` : predicate for compact operators

## Main statements

* `is_compact_operator_iff_is_compact_closure_image_closed_ball` : the usual characterization of
  compact operators from a normed space to a T2 TVS.
* `is_compact_operator.comp_clm` : precomposing a compact operator by a continuous linear map gives
  a compact operator
* `is_compact_operator.clm_comp` : postcomposing a compact operator by a continuous linear map
  gives a compact operator
* `is_compact_operator.continuous` : compact operators are automatically continuous
* `is_closed_set_of_is_compact_operator` : the set of compact operators is closed for the operator
  norm

## Implementation details

We define `is_compact_operator` as a predicate, because the space of compact operators inherits all
of its structures from the space of continuous linear maps (e.g we want to have the usual operator
norm on compact operators).

The two natural options then would be to make it a predicate over linear maps or continuous linear
maps. Instead we define it as a predicate over bare functions, although it really only makes sense
for linear functions, because Lean is really good at finding coercions to bare functions (whereas
coercing from continuous linear maps to linear maps often needs type ascriptions).

## TODO

Once we have the strong operator topology on spaces of linear maps between to TVSs,
`is_closed_set_of_is_compact_operator` should be generalized to this setup.

## References

* Bourbaki, *Spectral Theory*, chapters 3 to 5, to be published (2022)

## Tags

Compact operator
-/

open function set filter bornology metric

open_locale pointwise big_operators topological_space

/-- A compact operator between two TVSs. This definition is usually given as "there exists a
neighborhood of zero whose image is contained in a compact set", but we choose a definition which
involves fewer existential quantifiers and replaces images with preimages.

We prove the equivalence in `is_compact_operator_iff_exists_mem_nhds_image_subset_compact`. -/
def is_compact_operator {M₁ M₂ : Type*} [has_zero M₁] [topological_space M₁]
  [topological_space M₂] (f : M₁ → M₂) : Prop :=
∃ K, is_compact K ∧ f ⁻¹' K ∈ (𝓝 0 : filter M₁)

lemma is_compact_operator_zero {M₁ M₂ : Type*} [has_zero M₁] [topological_space M₁]
  [topological_space M₂] [has_zero M₂] : is_compact_operator (0 : M₁ → M₂) :=
⟨{0}, is_compact_singleton, mem_of_superset univ_mem (λ x _, rfl)⟩

section characterizations

section

variables {R₁ R₂ : Type*} [semiring R₁] [semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ M₂ : Type*}
  [topological_space M₁] [add_comm_monoid M₁] [topological_space M₂]

lemma is_compact_operator_iff_exists_mem_nhds_image_subset_compact (f : M₁ → M₂) :
  is_compact_operator f ↔ ∃ V ∈ (𝓝 0 : filter M₁), ∃ (K : set M₂), is_compact K ∧ f '' V ⊆ K :=
⟨λ ⟨K, hK, hKf⟩, ⟨f ⁻¹' K, hKf, K, hK, image_preimage_subset _ _⟩,
 λ ⟨V, hV, K, hK, hVK⟩, ⟨K, hK, mem_of_superset hV (image_subset_iff.mp hVK)⟩⟩

lemma is_compact_operator_iff_exists_mem_nhds_is_compact_closure_image [t2_space M₂]
  (f : M₁ → M₂) :
  is_compact_operator f ↔ ∃ V ∈ (𝓝 0 : filter M₁), is_compact (closure $ f '' V) :=
begin
  rw is_compact_operator_iff_exists_mem_nhds_image_subset_compact,
  exact ⟨λ ⟨V, hV, K, hK, hKV⟩, ⟨V, hV, compact_closure_of_subset_compact hK hKV⟩,
         λ ⟨V, hV, hVc⟩, ⟨V, hV, closure (f '' V), hVc, subset_closure⟩⟩,
end

end

section bounded

variables {𝕜₁ 𝕜₂ : Type*} [nontrivially_normed_field 𝕜₁] [semi_normed_ring 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂}
  {M₁ M₂ : Type*} [topological_space M₁] [add_comm_monoid M₁] [topological_space M₂]
  [add_comm_monoid M₂] [module 𝕜₁ M₁] [module 𝕜₂ M₂] [has_continuous_const_smul 𝕜₂ M₂]

lemma is_compact_operator.image_subset_compact_of_vonN_bounded {f : M₁ →ₛₗ[σ₁₂] M₂}
  (hf : is_compact_operator f) {S : set M₁} (hS : is_vonN_bounded 𝕜₁ S) :
  ∃ (K : set M₂), is_compact K ∧ f '' S ⊆ K :=
let ⟨K, hK, hKf⟩ := hf,
    ⟨r, hr, hrS⟩ := hS hKf,
    ⟨c, hc⟩ := normed_field.exists_lt_norm 𝕜₁ r,
    this := ne_zero_of_norm_ne_zero (hr.trans hc).ne.symm in
⟨σ₁₂ c • K, hK.image $ continuous_id.const_smul (σ₁₂ c),
  by rw [image_subset_iff, preimage_smul_setₛₗ _ _ _ f this.is_unit]; exact hrS c hc.le⟩

lemma is_compact_operator.is_compact_closure_image_of_vonN_bounded [t2_space M₂]
  {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : is_compact_operator f) {S : set M₁}
  (hS : is_vonN_bounded 𝕜₁ S) : is_compact (closure $ f '' S) :=
let ⟨K, hK, hKf⟩ := hf.image_subset_compact_of_vonN_bounded hS in
compact_closure_of_subset_compact hK hKf

end bounded

section normed_space

variables {𝕜₁ 𝕜₂ : Type*} [nontrivially_normed_field 𝕜₁] [semi_normed_ring 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂}
  {M₁ M₂ M₃ : Type*} [seminormed_add_comm_group M₁] [topological_space M₂]
  [add_comm_monoid M₂] [normed_space 𝕜₁ M₁] [module 𝕜₂ M₂]

lemma is_compact_operator.image_ball_subset_compact [has_continuous_const_smul 𝕜₂ M₂]
  {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : is_compact_operator f) (r : ℝ) :
  ∃ (K : set M₂), is_compact K ∧ f '' metric.ball 0 r ⊆ K :=
hf.image_subset_compact_of_vonN_bounded (normed_space.is_vonN_bounded_ball 𝕜₁ M₁ r)

lemma is_compact_operator.image_closed_ball_subset_compact [has_continuous_const_smul 𝕜₂ M₂]
  {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : is_compact_operator f) (r : ℝ) :
  ∃ (K : set M₂), is_compact K ∧ f '' metric.closed_ball 0 r ⊆ K :=
hf.image_subset_compact_of_vonN_bounded (normed_space.is_vonN_bounded_closed_ball 𝕜₁ M₁ r)

lemma is_compact_operator.is_compact_closure_image_ball [has_continuous_const_smul 𝕜₂ M₂]
  [t2_space M₂] {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : is_compact_operator f) (r : ℝ) :
  is_compact (closure $ f '' metric.ball 0 r) :=
hf.is_compact_closure_image_of_vonN_bounded (normed_space.is_vonN_bounded_ball 𝕜₁ M₁ r)

lemma is_compact_operator.is_compact_closure_image_closed_ball [has_continuous_const_smul 𝕜₂ M₂]
  [t2_space M₂] {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : is_compact_operator f) (r : ℝ) :
  is_compact (closure $ f '' metric.closed_ball 0 r) :=
hf.is_compact_closure_image_of_vonN_bounded (normed_space.is_vonN_bounded_closed_ball 𝕜₁ M₁ r)

lemma is_compact_operator_iff_image_ball_subset_compact [has_continuous_const_smul 𝕜₂ M₂]
  (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
  is_compact_operator f ↔ ∃ (K : set M₂), is_compact K ∧ f '' metric.ball 0 r ⊆ K :=
⟨λ hf, hf.image_ball_subset_compact r,
 λ ⟨K, hK, hKr⟩, (is_compact_operator_iff_exists_mem_nhds_image_subset_compact f).mpr
  ⟨metric.ball 0 r, ball_mem_nhds _ hr, K, hK, hKr⟩⟩

lemma is_compact_operator_iff_image_closed_ball_subset_compact [has_continuous_const_smul 𝕜₂ M₂]
  (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
  is_compact_operator f ↔ ∃ (K : set M₂), is_compact K ∧ f '' metric.closed_ball 0 r ⊆ K :=
⟨λ hf, hf.image_closed_ball_subset_compact r,
 λ ⟨K, hK, hKr⟩, (is_compact_operator_iff_exists_mem_nhds_image_subset_compact f).mpr
  ⟨metric.closed_ball 0 r, closed_ball_mem_nhds _ hr, K, hK, hKr⟩⟩

lemma is_compact_operator_iff_is_compact_closure_image_ball [has_continuous_const_smul 𝕜₂ M₂]
  [t2_space M₂] (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
  is_compact_operator f ↔ is_compact (closure $ f '' metric.ball 0 r) :=
⟨λ hf, hf.is_compact_closure_image_ball r,
 λ hf, (is_compact_operator_iff_exists_mem_nhds_is_compact_closure_image f).mpr
  ⟨metric.ball 0 r, ball_mem_nhds _ hr, hf⟩⟩

lemma is_compact_operator_iff_is_compact_closure_image_closed_ball
  [has_continuous_const_smul 𝕜₂ M₂] [t2_space M₂] (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
  is_compact_operator f ↔ is_compact (closure $ f '' metric.closed_ball 0 r) :=
⟨λ hf, hf.is_compact_closure_image_closed_ball r,
 λ hf, (is_compact_operator_iff_exists_mem_nhds_is_compact_closure_image f).mpr
  ⟨metric.closed_ball 0 r, closed_ball_mem_nhds _ hr, hf⟩⟩

end normed_space

end characterizations

section operations

variables {R₁ R₂ R₃ R₄ : Type*} [semiring R₁] [semiring R₂] [comm_semiring R₃] [comm_semiring R₄]
  {σ₁₂ : R₁ →+* R₂} {σ₃₄ : R₃ →+* R₄} {M₁ M₂ M₃ M₄ : Type*} [topological_space M₁]
  [add_comm_monoid M₁] [topological_space M₂] [add_comm_monoid M₂] [topological_space M₃]
  [add_comm_group M₃] [topological_space M₄] [add_comm_group M₄]

lemma is_compact_operator.smul {S : Type*} [monoid S] [distrib_mul_action S M₂]
  [has_continuous_const_smul S M₂] {f : M₁ → M₂}
  (hf : is_compact_operator f) (c : S) :
  is_compact_operator (c • f) :=
let ⟨K, hK, hKf⟩ := hf in ⟨c • K, hK.image $ continuous_id.const_smul c,
  mem_of_superset hKf (λ x hx, smul_mem_smul_set hx)⟩

lemma is_compact_operator.add [has_continuous_add M₂] {f g : M₁ → M₂}
  (hf : is_compact_operator f) (hg : is_compact_operator g) :
  is_compact_operator (f + g) :=
let ⟨A, hA, hAf⟩ := hf, ⟨B, hB, hBg⟩ := hg in
⟨A + B, hA.add hB, mem_of_superset (inter_mem hAf hBg) (λ x ⟨hxA, hxB⟩, set.add_mem_add hxA hxB)⟩

lemma is_compact_operator.neg [has_continuous_neg M₄] {f : M₁ → M₄}
  (hf : is_compact_operator f) : is_compact_operator (-f) :=
let ⟨K, hK, hKf⟩ := hf in
⟨-K, hK.neg, mem_of_superset hKf $ λ x (hx : f x ∈ K), set.neg_mem_neg.mpr hx⟩

lemma is_compact_operator.sub [topological_add_group M₄] {f g : M₁ → M₄}
  (hf : is_compact_operator f) (hg : is_compact_operator g) : is_compact_operator (f - g) :=
by rw sub_eq_add_neg; exact hf.add hg.neg

end operations

section comp

variables {R₁ R₂ R₃ : Type*} [semiring R₁] [semiring R₂] [semiring R₃] {σ₁₂ : R₁ →+* R₂}
  {σ₂₃ : R₂ →+* R₃} {M₁ M₂ M₃ : Type*} [topological_space M₁] [topological_space M₂]
  [topological_space M₃] [add_comm_monoid M₁] [module R₁ M₁]

lemma is_compact_operator.comp_clm [add_comm_monoid M₂] [module R₂ M₂] {f : M₂ → M₃}
  (hf : is_compact_operator f) (g : M₁ →SL[σ₁₂] M₂) :
  is_compact_operator (f ∘ g) :=
begin
  have := g.continuous.tendsto 0,
  rw map_zero at this,
  rcases hf with ⟨K, hK, hKf⟩,
  exact ⟨K, hK, this hKf⟩
end

lemma is_compact_operator.continuous_comp {f : M₁ → M₂} (hf : is_compact_operator f) {g : M₂ → M₃}
  (hg : continuous g) :
  is_compact_operator (g ∘ f) :=
begin
  rcases hf with ⟨K, hK, hKf⟩,
  refine ⟨g '' K, hK.image hg, mem_of_superset hKf _⟩,
  nth_rewrite 1 preimage_comp,
  exact preimage_mono (subset_preimage_image _ _)
end

lemma is_compact_operator.clm_comp [add_comm_monoid M₂] [module R₂ M₂] [add_comm_monoid M₃]
  [module R₃ M₃] {f : M₁ → M₂} (hf : is_compact_operator f) (g : M₂ →SL[σ₂₃] M₃) :
  is_compact_operator (g ∘ f) :=
hf.continuous_comp g.continuous

lemma is_compact_operator.continuous_on_comp [t2_space M₂] {f : M₁ → M₂}
  (hf : is_compact_operator f) {g : M₂ → M₃} (hg : continuous_on g (closure $ range f)) :
  is_compact_operator (g ∘ f) :=
begin
  rw is_compact_operator_iff_exists_mem_nhds_is_compact_closure_image at hf,
  rcases hf with ⟨V, hV, hVf⟩,
  refine ⟨g '' (closure $ f '' V),
          hVf.image_of_continuous_on (hg.mono $ closure_mono $ image_subset_range _ _),
          mem_of_superset hV _⟩,
  calc
    V ⊆ f ⁻¹' (f '' V) : subset_preimage_image _ _
  ... ⊆ f ⁻¹' (closure $ f '' V) : preimage_mono subset_closure
  ... ⊆ f ⁻¹' (g ⁻¹' (g '' (closure $ f '' V))) : preimage_mono (subset_preimage_image _ _)
end

end comp

section cod_restrict

variables {R₁ R₂ : Type*} [semiring R₁] [semiring R₂] {σ₁₂ : R₁ →+* R₂}
  {M₁ M₂ : Type*} [topological_space M₁] [topological_space M₂]
  [add_comm_monoid M₁] [add_comm_monoid M₂] [module R₁ M₁] [module R₂ M₂]

lemma is_compact_operator.cod_restrict {f : M₁ → M₂} (hf : is_compact_operator f)
  {V : submodule R₂ M₂} (hV : ∀ x, f x ∈ V) (h_closed : is_closed (V : set M₂)):
  is_compact_operator (set.cod_restrict f V hV) :=
let ⟨K, hK, hKf⟩ := hf in
⟨coe ⁻¹' K, (closed_embedding_subtype_coe h_closed).is_compact_preimage hK, hKf⟩

end cod_restrict

section restrict_invariant

variables {R₁ R₂ R₃ : Type*} [semiring R₁] [semiring R₂] [semiring R₃] {σ₁₂ : R₁ →+* R₂}
  {σ₂₃ : R₂ →+* R₃} {M₁ M₂ M₃ : Type*} [topological_space M₁] [uniform_space M₂]
  [topological_space M₃] [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₃]
  [module R₁ M₁] [module R₂ M₂] [module R₃ M₃]

/-- If a compact operator preserves a closed submodule, its restriction to that submodule is
compact. -/
lemma is_compact_operator.restrict_invariant {f : M₁ →ₗ[R₁] M₁} (hf : is_compact_operator f)
  {V : submodule R₁ M₁} (hV : ∀ v ∈ V, f v ∈ V) (h_closed : is_closed (V : set M₁)):
  is_compact_operator (f.restrict hV) :=
(hf.comp_clm V.subtypeL).cod_restrict (set_like.forall.2 hV) h_closed

/-- If a compact operator preserves a complete submodule, its restriction to that submodule is
compact. -/
lemma is_compact_operator.restrict_invariant' [separated_space M₂] {f : M₂ →ₗ[R₂] M₂}
  (hf : is_compact_operator f) {V : submodule R₂ M₂} (hV : ∀ v ∈ V, f v ∈ V)
  [hcomplete : complete_space V] : is_compact_operator (f.restrict hV) :=
hf.restrict_invariant hV (complete_space_coe_iff_is_complete.mp hcomplete).is_closed

end restrict_invariant

section continuous

variables {𝕜₁ 𝕜₂ : Type*} [nontrivially_normed_field 𝕜₁] [nontrivially_normed_field 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [ring_hom_isometric σ₁₂] {M₁ M₂ : Type*} [topological_space M₁]
  [add_comm_group M₁] [topological_space M₂] [add_comm_group M₂] [module 𝕜₁ M₁] [module 𝕜₂ M₂]
  [topological_add_group M₁] [has_continuous_const_smul 𝕜₁ M₁]
  [topological_add_group M₂] [has_continuous_smul 𝕜₂ M₂]

@[continuity] lemma is_compact_operator.continuous {f : M₁ →ₛₗ[σ₁₂] M₂}
  (hf : is_compact_operator f) : continuous f :=
begin
  letI : uniform_space M₂ := topological_add_group.to_uniform_space _,
  haveI : uniform_add_group M₂ := topological_add_group_is_uniform,
  refine continuous_of_continuous_at_zero f (λ U hU, _),
  rw map_zero at hU,
  rcases hf with ⟨K, hK, hKf⟩,
  rcases hK.totally_bounded.is_vonN_bounded 𝕜₂ hU with ⟨r, hr, hrU⟩,
  rcases normed_field.exists_lt_norm 𝕜₁ r with ⟨c, hc⟩,
  have hcnz : c ≠ 0 := ne_zero_of_norm_ne_zero (hr.trans hc).ne.symm,
  suffices : (σ₁₂ $ c⁻¹) • K ⊆ U,
  { refine mem_of_superset _ this,
    have : is_unit c⁻¹ := hcnz.is_unit.inv,
    rwa [mem_map, preimage_smul_setₛₗ _ _ _ f this, set_smul_mem_nhds_zero_iff (inv_ne_zero hcnz)],
    apply_instance },
  rw [σ₁₂.map_inv, ← subset_set_smul_iff₀ (σ₁₂.map_ne_zero.mpr hcnz)],
  refine hrU (σ₁₂ c) _,
  rw ring_hom_isometric.is_iso,
  exact hc.le
end

/-- Upgrade a compact `linear_map` to a `continuous_linear_map`. -/
def continuous_linear_map.mk_of_is_compact_operator {f : M₁ →ₛₗ[σ₁₂] M₂}
  (hf : is_compact_operator f) : M₁ →SL[σ₁₂] M₂ :=
⟨f, hf.continuous⟩

end continuous

lemma is_closed_set_of_is_compact_operator {𝕜₁ 𝕜₂ : Type*} [nontrivially_normed_field 𝕜₁]
  [nontrivially_normed_field 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} [ring_hom_isometric σ₁₂] {M₁ M₂ : Type*}
  [seminormed_add_comm_group M₁] [normed_add_comm_group M₂] [normed_space 𝕜₁ M₁]
  [normed_space 𝕜₂ M₂] [complete_space M₂] :
  is_closed {f : M₁ →SL[σ₁₂] M₂ | is_compact_operator f} :=
begin
  refine is_closed_of_closure_subset _,
  rintros u hu,
  rw metric.mem_closure_iff at hu,
  suffices : totally_bounded (u '' metric.closed_ball 0 1),
  { change is_compact_operator (u : M₁ →ₛₗ[σ₁₂] M₂),
    rw is_compact_operator_iff_is_compact_closure_image_closed_ball (u : M₁ →ₛₗ[σ₁₂] M₂)
      zero_lt_one,
    exact compact_of_totally_bounded_is_closed this.closure is_closed_closure },
  rw metric.totally_bounded_iff,
  intros ε hε,
  rcases hu (ε/2) (by linarith) with ⟨v, hv, huv⟩,
  rcases (hv.is_compact_closure_image_closed_ball 1).finite_cover_balls
    (show 0 < ε/2, by linarith) with ⟨T, -, hT, hTv⟩,
  have hTv : v '' closed_ball 0 1 ⊆ _ := subset_closure.trans hTv,
  refine ⟨T, hT, _⟩,
  rw image_subset_iff at ⊢ hTv,
  intros x hx,
  specialize hTv hx,
  rw [mem_preimage, mem_Union₂] at ⊢ hTv,
  rcases hTv with ⟨t, ht, htx⟩,
  refine ⟨t, ht, _⟩,
  suffices : dist (u x) (v x) < ε/2,
  { rw mem_ball at *,
    linarith [dist_triangle (u x) (v x) t] },
  rw mem_closed_ball_zero_iff at hx,
  calc dist (u x) (v x)
      = ∥u x - v x∥ : dist_eq_norm _ _
  ... = ∥(u - v) x∥ : by rw continuous_linear_map.sub_apply; refl
  ... ≤ ∥u - v∥ : (u - v).unit_le_op_norm x hx
  ... = dist u v : (dist_eq_norm _ _).symm
  ... < ε/2 : huv
end

lemma is_compact_operator_of_tendsto {ι 𝕜₁ 𝕜₂ : Type*} [nontrivially_normed_field 𝕜₁]
  [nontrivially_normed_field 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} [ring_hom_isometric σ₁₂] {M₁ M₂ : Type*}
  [seminormed_add_comm_group M₁] [normed_add_comm_group M₂] [normed_space 𝕜₁ M₁]
  [normed_space 𝕜₂ M₂] [complete_space M₂] {l : filter ι} [l.ne_bot] {F : ι → M₁ →SL[σ₁₂] M₂}
  {f : M₁ →SL[σ₁₂] M₂} (hf : tendsto F l (𝓝 f)) (hF : ∀ᶠ i in l, is_compact_operator (F i)) :
  is_compact_operator f :=
is_closed_set_of_is_compact_operator.mem_of_tendsto hf hF
