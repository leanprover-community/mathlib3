/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
import algebra.algebra.tower
import analysis.asymptotics.asymptotics
import analysis.normed_space.continuous_linear_map
import analysis.normed_space.linear_isometry
import topology.algebra.module.strong_topology

/-!
# Operator norm on the space of continuous linear maps

Define the operator norm on the space of continuous (semi)linear maps between normed spaces, and
prove its basic properties. In particular, show that this space is itself a normed space.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory for `seminormed_add_comm_group` and we specialize to `normed_add_comm_group` at the end.

Note that most of statements that apply to semilinear maps only hold when the ring homomorphism
is isometric, as expressed by the typeclass `[ring_hom_isometric σ]`.

-/

noncomputable theory
open_locale classical nnreal topology

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variables {𝕜 𝕜₂ 𝕜₃ E Eₗ F Fₗ G Gₗ 𝓕 : Type*}

section semi_normed

open metric continuous_linear_map

variables [seminormed_add_comm_group E] [seminormed_add_comm_group Eₗ] [seminormed_add_comm_group F]
  [seminormed_add_comm_group Fₗ] [seminormed_add_comm_group G] [seminormed_add_comm_group Gₗ]

variables [nontrivially_normed_field 𝕜] [nontrivially_normed_field 𝕜₂]
  [nontrivially_normed_field 𝕜₃] [normed_space 𝕜 E] [normed_space 𝕜 Eₗ] [normed_space 𝕜₂ F]
  [normed_space 𝕜 Fₗ] [normed_space 𝕜₃ G] [normed_space 𝕜 Gₗ]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃]

/-- If `‖x‖ = 0` and `f` is continuous then `‖f x‖ = 0`. -/
lemma norm_image_of_norm_zero [semilinear_map_class 𝓕 σ₁₂ E F] (f : 𝓕)
  (hf : continuous f) {x : E} (hx : ‖x‖ = 0) : ‖f x‖ = 0 :=
begin
  refine le_antisymm (le_of_forall_pos_le_add (λ ε hε, _)) (norm_nonneg (f x)),
  rcases normed_add_comm_group.tendsto_nhds_nhds.1 (hf.tendsto 0) ε hε with ⟨δ, δ_pos, hδ⟩,
  replace hδ := hδ x,
  rw [sub_zero, hx] at hδ,
  replace hδ := le_of_lt (hδ δ_pos),
  rw [map_zero, sub_zero] at hδ,
  rwa [zero_add]
end

section

variables [ring_hom_isometric σ₁₂] [ring_hom_isometric σ₂₃]

lemma semilinear_map_class.bound_of_shell_semi_normed [semilinear_map_class 𝓕 σ₁₂ E F]
  (f : 𝓕) {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
  (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) {x : E} (hx : ‖x‖ ≠ 0) :
  ‖f x‖ ≤ C * ‖x‖ :=
begin
  rcases rescale_to_shell_semi_normed hc ε_pos hx with ⟨δ, hδ, δxle, leδx, δinv⟩,
  have := hf (δ • x) leδx δxle,
  simpa only [map_smulₛₗ, norm_smul, mul_left_comm C, mul_le_mul_left (norm_pos_iff.2 hδ),
              ring_hom_isometric.is_iso] using hf (δ • x) leδx δxle
end

/-- A continuous linear map between seminormed spaces is bounded when the field is nontrivially
normed. The continuity ensures boundedness on a ball of some radius `ε`. The nontriviality of the
norm is then used to rescale any element into an element of norm in `[ε/C, ε]`, whose image has a
controlled norm. The norm control for the original element follows by rescaling. -/
lemma semilinear_map_class.bound_of_continuous [semilinear_map_class 𝓕 σ₁₂ E F] (f : 𝓕)
  (hf : continuous f) : ∃ C, 0 < C ∧ (∀ x : E, ‖f x‖ ≤ C * ‖x‖) :=
begin
  rcases normed_add_comm_group.tendsto_nhds_nhds.1 (hf.tendsto 0) 1 zero_lt_one with ⟨ε, ε_pos, hε⟩,
  simp only [sub_zero, map_zero] at hε,
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  have : 0 < ‖c‖ / ε, from div_pos (zero_lt_one.trans hc) ε_pos,
  refine ⟨‖c‖ / ε, this, λ x, _⟩,
  by_cases hx : ‖x‖ = 0,
  { rw [hx, mul_zero],
    exact le_of_eq (norm_image_of_norm_zero f hf hx) },
  refine semilinear_map_class.bound_of_shell_semi_normed f ε_pos hc (λ x hle hlt, _) hx,
  refine (hε _ hlt).le.trans _,
  rwa [← div_le_iff' this, one_div_div]
end

end

namespace continuous_linear_map

theorem bound [ring_hom_isometric σ₁₂] (f : E →SL[σ₁₂] F) :
  ∃ C, 0 < C ∧ (∀ x : E, ‖f x‖ ≤ C * ‖x‖) :=
semilinear_map_class.bound_of_continuous f f.2

section
open filter

variables (𝕜 E)
/-- Given a unit-length element `x` of a normed space `E` over a field `𝕜`, the natural linear
    isometry map from `𝕜` to `E` by taking multiples of `x`.-/
def _root_.linear_isometry.to_span_singleton {v : E} (hv : ‖v‖ = 1) : 𝕜 →ₗᵢ[𝕜] E :=
{ norm_map' := λ x, by simp [norm_smul, hv],
  .. linear_map.to_span_singleton 𝕜 E v }
variables {𝕜 E}

@[simp] lemma _root_.linear_isometry.to_span_singleton_apply {v : E} (hv : ‖v‖ = 1) (a : 𝕜) :
  linear_isometry.to_span_singleton 𝕜 E hv a = a • v :=
rfl

@[simp] lemma _root_.linear_isometry.coe_to_span_singleton {v : E} (hv : ‖v‖ = 1) :
  (linear_isometry.to_span_singleton 𝕜 E hv).to_linear_map = linear_map.to_span_singleton 𝕜 E v :=
rfl

end

section op_norm
open set real

/-- The operator norm of a continuous linear map is the inf of all its bounds. -/
def op_norm (f : E →SL[σ₁₂] F) := Inf {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖}
instance has_op_norm : has_norm (E →SL[σ₁₂] F) := ⟨op_norm⟩

lemma norm_def (f : E →SL[σ₁₂] F) : ‖f‖ = Inf {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} := rfl

-- So that invocations of `le_cInf` make sense: we show that the set of
-- bounds is nonempty and bounded below.
lemma bounds_nonempty [ring_hom_isometric σ₁₂] {f : E →SL[σ₁₂] F} :
  ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
let ⟨M, hMp, hMb⟩ := f.bound in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below {f : E →SL[σ₁₂] F} :
  bdd_below { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
⟨0, λ _ ⟨hn, _⟩, hn⟩

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
lemma op_norm_le_bound (f : E →SL[σ₁₂] F) {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) :
  ‖f‖ ≤ M :=
cInf_le bounds_bdd_below ⟨hMp, hM⟩

/-- If one controls the norm of every `A x`, `‖x‖ ≠ 0`, then one controls the norm of `A`. -/
lemma op_norm_le_bound' (f : E →SL[σ₁₂] F) {M : ℝ} (hMp: 0 ≤ M)
  (hM : ∀ x, ‖x‖ ≠ 0 → ‖f x‖ ≤ M * ‖x‖) :
  ‖f‖ ≤ M :=
op_norm_le_bound f hMp $ λ x, (ne_or_eq (‖x‖) 0).elim (hM x) $
  λ h, by simp only [h, mul_zero, norm_image_of_norm_zero f f.2 h]

theorem op_norm_le_of_lipschitz {f : E →SL[σ₁₂] F} {K : ℝ≥0} (hf : lipschitz_with K f) :
  ‖f‖ ≤ K :=
f.op_norm_le_bound K.2 $ λ x, by simpa only [dist_zero_right, f.map_zero] using hf.dist_le_mul x 0

lemma op_norm_eq_of_bounds {φ : E →SL[σ₁₂] F} {M : ℝ} (M_nonneg : 0 ≤ M)
  (h_above : ∀ x, ‖φ x‖ ≤ M*‖x‖) (h_below : ∀ N ≥ 0, (∀ x, ‖φ x‖ ≤ N*‖x‖) → M ≤ N) :
  ‖φ‖ = M :=
le_antisymm (φ.op_norm_le_bound M_nonneg h_above)
  ((le_cInf_iff continuous_linear_map.bounds_bdd_below ⟨M, M_nonneg, h_above⟩).mpr $
   λ N ⟨N_nonneg, hN⟩, h_below N N_nonneg hN)

lemma op_norm_neg (f : E →SL[σ₁₂] F) : ‖-f‖ = ‖f‖ := by simp only [norm_def, neg_apply, norm_neg]

section

variables [ring_hom_isometric σ₁₂] [ring_hom_isometric σ₂₃]
  (f g : E →SL[σ₁₂] F) (h : F →SL[σ₂₃] G) (x : E)

lemma op_norm_nonneg : 0 ≤ ‖f‖ :=
le_cInf bounds_nonempty (λ _ ⟨hx, _⟩, hx)

/-- The fundamental property of the operator norm: `‖f x‖ ≤ ‖f‖ * ‖x‖`. -/
theorem le_op_norm : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
begin
  obtain ⟨C, Cpos, hC⟩ := f.bound,
  replace hC := hC x,
  by_cases h : ‖x‖ = 0,
  { rwa [h, mul_zero] at ⊢ hC },
  have hlt : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (ne.symm h),
  exact  (div_le_iff hlt).mp (le_cInf bounds_nonempty (λ c ⟨_, hc⟩,
    (div_le_iff hlt).mpr $ by { apply hc })),
end

theorem dist_le_op_norm (x y : E) : dist (f x) (f y) ≤ ‖f‖ * dist x y :=
by simp_rw [dist_eq_norm, ← map_sub, f.le_op_norm]

theorem le_op_norm_of_le {c : ℝ} {x} (h : ‖x‖ ≤ c) : ‖f x‖ ≤ ‖f‖ * c :=
le_trans (f.le_op_norm x) (mul_le_mul_of_nonneg_left h f.op_norm_nonneg)

theorem le_of_op_norm_le {c : ℝ} (h : ‖f‖ ≤ c) (x : E) : ‖f x‖ ≤ c * ‖x‖ :=
(f.le_op_norm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))

lemma ratio_le_op_norm : ‖f x‖ / ‖x‖ ≤ ‖f‖ :=
div_le_of_nonneg_of_le_mul (norm_nonneg _) f.op_norm_nonneg (le_op_norm _ _)

/-- The image of the unit ball under a continuous linear map is bounded. -/
lemma unit_le_op_norm : ‖x‖ ≤ 1 → ‖f x‖ ≤ ‖f‖ :=
mul_one ‖f‖ ▸ f.le_op_norm_of_le

lemma op_norm_le_of_shell {f : E →SL[σ₁₂] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C)
  {c : 𝕜} (hc : 1 < ‖c‖) (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) :
  ‖f‖ ≤ C :=
f.op_norm_le_bound' hC $ λ x hx, semilinear_map_class.bound_of_shell_semi_normed f ε_pos hc hf hx

lemma op_norm_le_of_ball {f : E →SL[σ₁₂] F} {ε : ℝ} {C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C)
  (hf : ∀ x ∈ ball (0 : E) ε, ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
begin
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  refine op_norm_le_of_shell ε_pos hC hc (λ x _ hx, hf x _),
  rwa ball_zero_eq
end

lemma op_norm_le_of_nhds_zero {f : E →SL[σ₁₂] F} {C : ℝ} (hC : 0 ≤ C)
  (hf : ∀ᶠ x in 𝓝 (0 : E), ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
let ⟨ε, ε0, hε⟩ := metric.eventually_nhds_iff_ball.1 hf in op_norm_le_of_ball ε0 hC hε

lemma op_norm_le_of_shell' {f : E →SL[σ₁₂] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C)
  {c : 𝕜} (hc : ‖c‖ < 1) (hf : ∀ x, ε * ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) :
  ‖f‖ ≤ C :=
begin
  by_cases h0 : c = 0,
  { refine op_norm_le_of_ball ε_pos hC (λ x hx, hf x _ _),
    { simp [h0] },
    { rwa ball_zero_eq at hx } },
  { rw [← inv_inv c, norm_inv,
      inv_lt_one_iff_of_pos (norm_pos_iff.2 $ inv_ne_zero h0)] at hc,
    refine op_norm_le_of_shell ε_pos hC hc _,
    rwa [norm_inv, div_eq_mul_inv, inv_inv] }
end

/-- For a continuous real linear map `f`, if one controls the norm of every `f x`, `‖x‖ = 1`, then
one controls the norm of `f`. -/
lemma op_norm_le_of_unit_norm [normed_space ℝ E] [normed_space ℝ F] {f : E →L[ℝ] F} {C : ℝ}
  (hC : 0 ≤ C) (hf : ∀ x, ‖x‖ = 1 → ‖f x‖ ≤ C) : ‖f‖ ≤ C :=
begin
  refine op_norm_le_bound' f hC (λ x hx, _),
  have H₁ : ‖(‖x‖⁻¹ • x)‖ = 1, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel hx],
  have H₂ := hf _ H₁,
  rwa [map_smul, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul, div_le_iff] at H₂,
  exact (norm_nonneg x).lt_of_ne' hx
end

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
(f + g).op_norm_le_bound (add_nonneg f.op_norm_nonneg g.op_norm_nonneg) $
  λ x, (norm_add_le_of_le (f.le_op_norm x) (g.le_op_norm x)).trans_eq (add_mul _ _ _).symm

/-- The norm of the `0` operator is `0`. -/
theorem op_norm_zero : ‖(0 : E →SL[σ₁₂] F)‖ = 0 :=
le_antisymm (cInf_le bounds_bdd_below
    ⟨le_rfl, λ _, le_of_eq (by { rw [zero_mul], exact norm_zero })⟩)
    (op_norm_nonneg _)

/-- The norm of the identity is at most `1`. It is in fact `1`, except when the space is trivial
where it is `0`. It means that one can not do better than an inequality in general. -/
lemma norm_id_le : ‖id 𝕜 E‖ ≤ 1 :=
op_norm_le_bound _ zero_le_one (λx, by simp)

/-- If there is an element with norm different from `0`, then the norm of the identity equals `1`.
(Since we are working with seminorms supposing that the space is non-trivial is not enough.) -/
lemma norm_id_of_nontrivial_seminorm (h : ∃ (x : E), ‖x‖ ≠ 0) : ‖id 𝕜 E‖ = 1 :=
le_antisymm norm_id_le $ let ⟨x, hx⟩ := h in
have _ := (id 𝕜 E).ratio_le_op_norm x,
by rwa [id_apply, div_self hx] at this

lemma op_norm_smul_le {𝕜' : Type*} [normed_field 𝕜'] [normed_space 𝕜' F]
  [smul_comm_class 𝕜₂ 𝕜' F] (c : 𝕜') (f : E →SL[σ₁₂] F) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ :=
((c • f).op_norm_le_bound
  (mul_nonneg (norm_nonneg _) (op_norm_nonneg _)) (λ _,
  begin
    erw [norm_smul, mul_assoc],
    exact mul_le_mul_of_nonneg_left (le_op_norm _ _) (norm_nonneg _)
  end))

/-- Continuous linear maps themselves form a seminormed space with respect to
the operator norm. This is only a temporary definition because we want to replace the topology
with `continuous_linear_map.topological_space` to avoid diamond issues.
See Note [forgetful inheritance] -/
protected def tmp_seminormed_add_comm_group : seminormed_add_comm_group (E →SL[σ₁₂] F) :=
add_group_seminorm.to_seminormed_add_comm_group
{ to_fun := norm,
  map_zero' := op_norm_zero,
  add_le' := op_norm_add_le,
  neg' := op_norm_neg }

/-- The `pseudo_metric_space` structure on `E →SL[σ₁₂] F` coming from
`continuous_linear_map.tmp_seminormed_add_comm_group`.
See Note [forgetful inheritance] -/
protected def tmp_pseudo_metric_space : pseudo_metric_space (E →SL[σ₁₂] F) :=
continuous_linear_map.tmp_seminormed_add_comm_group.to_pseudo_metric_space

/-- The `uniform_space` structure on `E →SL[σ₁₂] F` coming from
`continuous_linear_map.tmp_seminormed_add_comm_group`.
See Note [forgetful inheritance] -/
protected def tmp_uniform_space : uniform_space (E →SL[σ₁₂] F) :=
continuous_linear_map.tmp_pseudo_metric_space.to_uniform_space

/-- The `topological_space` structure on `E →SL[σ₁₂] F` coming from
`continuous_linear_map.tmp_seminormed_add_comm_group`.
See Note [forgetful inheritance] -/
protected def tmp_topological_space : topological_space (E →SL[σ₁₂] F) :=
continuous_linear_map.tmp_uniform_space.to_topological_space

section tmp

local attribute [-instance] continuous_linear_map.topological_space
local attribute [-instance] continuous_linear_map.uniform_space
local attribute [instance] continuous_linear_map.tmp_seminormed_add_comm_group

protected lemma tmp_topological_add_group : topological_add_group (E →SL[σ₁₂] F) :=
infer_instance

protected lemma tmp_closed_ball_div_subset {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
  closed_ball (0 : E →SL[σ₁₂] F) (a / b) ⊆
  {f | ∀ x ∈ closed_ball (0 : E) b, f x ∈ closed_ball (0 : F) a} :=
begin
  intros f hf x hx,
  rw mem_closed_ball_zero_iff at ⊢ hf hx,
  calc ‖f x‖
      ≤ ‖f‖ * ‖x‖ : le_op_norm _ _
  ... ≤ (a/b) * b : mul_le_mul hf hx (norm_nonneg _) (div_pos ha hb).le
  ... = a : div_mul_cancel a hb.ne.symm
end

end tmp

protected theorem tmp_topology_eq :
  (continuous_linear_map.tmp_topological_space : topological_space (E →SL[σ₁₂] F)) =
  continuous_linear_map.topological_space :=
begin
  refine continuous_linear_map.tmp_topological_add_group.ext infer_instance
    ((@metric.nhds_basis_closed_ball _ continuous_linear_map.tmp_pseudo_metric_space 0).ext
      (continuous_linear_map.has_basis_nhds_zero_of_basis metric.nhds_basis_closed_ball) _ _),
  { rcases normed_field.exists_norm_lt_one 𝕜 with ⟨c, hc₀, hc₁⟩,
    refine λ ε hε, ⟨⟨closed_ball 0 (1 / ‖c‖), ε⟩,
      ⟨normed_space.is_vonN_bounded_closed_ball _ _ _, hε⟩, λ f hf, _⟩,
    change ∀ x, _ at hf,
    simp_rw mem_closed_ball_zero_iff at hf,
    rw @mem_closed_ball_zero_iff _ seminormed_add_comm_group.to_seminormed_add_group,
    refine op_norm_le_of_shell' (div_pos one_pos hc₀) hε.le hc₁ (λ x hx₁ hxc, _),
    rw div_mul_cancel 1 hc₀.ne.symm at hx₁,
    exact (hf x hxc.le).trans (le_mul_of_one_le_right hε.le hx₁) },
  { rintros ⟨S, ε⟩ ⟨hS, hε⟩,
    rw [normed_space.is_vonN_bounded_iff, ← bounded_iff_is_bounded] at hS,
    rcases hS.subset_ball_lt 0 0 with ⟨δ, hδ, hSδ⟩,
    exact ⟨ε/δ, div_pos hε hδ, (continuous_linear_map.tmp_closed_ball_div_subset hε hδ).trans $
      λ f hf x hx, hf x $ hSδ hx⟩ }
end

protected theorem tmp_uniform_space_eq :
  (continuous_linear_map.tmp_uniform_space : uniform_space (E →SL[σ₁₂] F)) =
  continuous_linear_map.uniform_space :=
begin
  rw [← @uniform_add_group.to_uniform_space_eq _ continuous_linear_map.tmp_uniform_space,
      ← @uniform_add_group.to_uniform_space_eq _ continuous_linear_map.uniform_space],
  congr' 1,
  exact continuous_linear_map.tmp_topology_eq
end

instance to_pseudo_metric_space : pseudo_metric_space (E →SL[σ₁₂] F) :=
continuous_linear_map.tmp_pseudo_metric_space.replace_uniformity
  (congr_arg _ continuous_linear_map.tmp_uniform_space_eq.symm)

/-- Continuous linear maps themselves form a seminormed space with respect to
    the operator norm. -/
instance to_seminormed_add_comm_group : seminormed_add_comm_group (E →SL[σ₁₂] F) :=
{ dist_eq := continuous_linear_map.tmp_seminormed_add_comm_group.dist_eq }

lemma nnnorm_def (f : E →SL[σ₁₂] F) : ‖f‖₊ = Inf {c | ∀ x, ‖f x‖₊ ≤ c * ‖x‖₊} :=
begin
  ext,
  rw [nnreal.coe_Inf, coe_nnnorm, norm_def, nnreal.coe_image],
  simp_rw [← nnreal.coe_le_coe, nnreal.coe_mul, coe_nnnorm, mem_set_of_eq, subtype.coe_mk,
    exists_prop],
end

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
lemma op_nnnorm_le_bound (f : E →SL[σ₁₂] F) (M : ℝ≥0) (hM : ∀ x, ‖f x‖₊ ≤ M * ‖x‖₊) :
  ‖f‖₊ ≤ M :=
op_norm_le_bound f (zero_le M) hM

/-- If one controls the norm of every `A x`, `‖x‖₊ ≠ 0`, then one controls the norm of `A`. -/
lemma op_nnnorm_le_bound' (f : E →SL[σ₁₂] F) (M : ℝ≥0) (hM : ∀ x, ‖x‖₊ ≠ 0 → ‖f x‖₊ ≤ M * ‖x‖₊) :
  ‖f‖₊ ≤ M :=
op_norm_le_bound' f (zero_le M) $ λ x hx, hM x $ by rwa [← nnreal.coe_ne_zero]

/-- For a continuous real linear map `f`, if one controls the norm of every `f x`, `‖x‖₊ = 1`, then
one controls the norm of `f`. -/
lemma op_nnnorm_le_of_unit_nnnorm [normed_space ℝ E] [normed_space ℝ F] {f : E →L[ℝ] F} {C : ℝ≥0}
  (hf : ∀ x, ‖x‖₊ = 1 → ‖f x‖₊ ≤ C) : ‖f‖₊ ≤ C :=
op_norm_le_of_unit_norm C.coe_nonneg $ λ x hx, hf x $ by rwa [← nnreal.coe_eq_one]

theorem op_nnnorm_le_of_lipschitz {f : E →SL[σ₁₂] F} {K : ℝ≥0} (hf : lipschitz_with K f) :
  ‖f‖₊ ≤ K :=
op_norm_le_of_lipschitz hf

lemma op_nnnorm_eq_of_bounds {φ : E →SL[σ₁₂] F} (M : ℝ≥0)
  (h_above : ∀ x, ‖φ x‖ ≤ M*‖x‖) (h_below : ∀ N, (∀ x, ‖φ x‖₊ ≤ N*‖x‖₊) → M ≤ N) :
  ‖φ‖₊ = M :=
subtype.ext $ op_norm_eq_of_bounds (zero_le M) h_above $ subtype.forall'.mpr h_below

instance to_normed_space {𝕜' : Type*} [normed_field 𝕜'] [normed_space 𝕜' F]
  [smul_comm_class 𝕜₂ 𝕜' F] : normed_space 𝕜' (E →SL[σ₁₂] F) :=
⟨op_norm_smul_le⟩

include σ₁₃
/-- The operator norm is submultiplicative. -/
lemma op_norm_comp_le (f : E →SL[σ₁₂] F) : ‖h.comp f‖ ≤ ‖h‖ * ‖f‖ :=
(cInf_le bounds_bdd_below
  ⟨mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _), λ x,
    by { rw mul_assoc, exact h.le_op_norm_of_le (f.le_op_norm x) } ⟩)

lemma op_nnnorm_comp_le [ring_hom_isometric σ₁₃] (f : E →SL[σ₁₂] F) : ‖h.comp f‖₊ ≤ ‖h‖₊ * ‖f‖₊ :=
op_norm_comp_le h f
omit σ₁₃

/-- Continuous linear maps form a seminormed ring with respect to the operator norm. -/
instance to_semi_normed_ring : semi_normed_ring (E →L[𝕜] E) :=
{ norm_mul := λ f g, op_norm_comp_le f g,
  .. continuous_linear_map.to_seminormed_add_comm_group, .. continuous_linear_map.ring }

/-- For a normed space `E`, continuous linear endomorphisms form a normed algebra with
respect to the operator norm. -/
instance to_normed_algebra : normed_algebra 𝕜 (E →L[𝕜] E) :=
{ .. continuous_linear_map.to_normed_space,
  .. continuous_linear_map.algebra }

end

end op_norm

end continuous_linear_map

namespace linear_map

/-- If a continuous linear map is constructed from a linear map via the constructor `mk_continuous`,
then its norm is bounded by the bound given to the constructor if it is nonnegative. -/
lemma mk_continuous_norm_le (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (hC : 0 ≤ C) (h : ∀x, ‖f x‖ ≤ C * ‖x‖) :
  ‖f.mk_continuous C h‖ ≤ C :=
continuous_linear_map.op_norm_le_bound _ hC h

/-- If a continuous linear map is constructed from a linear map via the constructor `mk_continuous`,
then its norm is bounded by the bound or zero if bound is negative. -/
lemma mk_continuous_norm_le' (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (h : ∀x, ‖f x‖ ≤ C * ‖x‖) :
  ‖f.mk_continuous C h‖ ≤ max C 0 :=
continuous_linear_map.op_norm_le_bound _ (le_max_right _ _) $ λ x, (h x).trans $
  mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x)

variables [ring_hom_isometric σ₂₃]

/-- Create a bilinear map (represented as a map `E →L[𝕜] F →L[𝕜] G`) from the corresponding linear
map and a bound on the norm of the image. The linear map can be constructed using
`linear_map.mk₂`. -/
def mk_continuous₂ (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (C : ℝ)
  (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) :
  E →SL[σ₁₃] F →SL[σ₂₃] G :=
linear_map.mk_continuous
  { to_fun := λ x, (f x).mk_continuous (C * ‖x‖) (hC x),
    map_add' := λ x y,
    begin
      ext z,
      rw [continuous_linear_map.add_apply, mk_continuous_apply, mk_continuous_apply,
          mk_continuous_apply, map_add, add_apply]
    end,
    map_smul' := λ c x,
    begin
      ext z,
      rw [continuous_linear_map.smul_apply, mk_continuous_apply, mk_continuous_apply, map_smulₛₗ,
          smul_apply]
    end, }
  (max C 0) $ λ x, (mk_continuous_norm_le' _ _).trans_eq $
    by rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]

@[simp] lemma mk_continuous₂_apply (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
  (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) (x : E) (y : F) :
  f.mk_continuous₂ C hC x y = f x y :=
rfl

lemma mk_continuous₂_norm_le' (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
  (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) :
  ‖f.mk_continuous₂ C hC‖ ≤ max C 0 :=
mk_continuous_norm_le _ (le_max_iff.2 $ or.inr le_rfl) _

lemma mk_continuous₂_norm_le (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
  (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) :
  ‖f.mk_continuous₂ C hC‖ ≤ C :=
(f.mk_continuous₂_norm_le' hC).trans_eq $ max_eq_left h0

end linear_map

end semi_normed

section normed

variables [normed_add_comm_group E] [normed_add_comm_group F] [normed_add_comm_group G]
  [normed_add_comm_group Fₗ]

open metric continuous_linear_map

section
variables [nontrivially_normed_field 𝕜] [nontrivially_normed_field 𝕜₂]
  [nontrivially_normed_field 𝕜₃] [normed_space 𝕜 E] [normed_space 𝕜₂ F] [normed_space 𝕜₃ G]
  [normed_space 𝕜 Fₗ] (c : 𝕜)
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃}
  (f g : E →SL[σ₁₂] F) (x y z : E)

namespace continuous_linear_map

section op_norm
open set real

/-- An operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff [ring_hom_isometric σ₁₂] : ‖f‖ = 0 ↔ f = 0 :=
iff.intro
  (λ hn, continuous_linear_map.ext (λ x, norm_le_zero_iff.1
    (calc _ ≤ ‖f‖ * ‖x‖ : le_op_norm _ _
     ...     = _ : by rw [hn, zero_mul])))
  (by { rintro rfl, exact op_norm_zero })

/-- If a normed space is non-trivial, then the norm of the identity equals `1`. -/
@[simp] lemma norm_id [nontrivial E] : ‖id 𝕜 E‖ = 1 :=
begin
  refine norm_id_of_nontrivial_seminorm _,
  obtain ⟨x, hx⟩ := exists_ne (0 : E),
  exact ⟨x, ne_of_gt (norm_pos_iff.2 hx)⟩,
end

instance norm_one_class [nontrivial E] : norm_one_class (E →L[𝕜] E) := ⟨norm_id⟩

/-- Continuous linear maps themselves form a normed space with respect to
    the operator norm. -/
instance to_normed_add_comm_group [ring_hom_isometric σ₁₂] : normed_add_comm_group (E →SL[σ₁₂] F) :=
normed_add_comm_group.of_separation (λ f, (op_norm_zero_iff f).mp)

/-- Continuous linear maps form a normed ring with respect to the operator norm. -/
instance to_normed_ring : normed_ring (E →L[𝕜] E) :=
{ .. continuous_linear_map.to_normed_add_comm_group, .. continuous_linear_map.to_semi_normed_ring }

end op_norm

end continuous_linear_map

end

end normed
