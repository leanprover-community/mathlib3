/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.asymptotics.asymptotic_equivalent
import analysis.normed_space.affine_isometry
import analysis.normed_space.operator_norm
import analysis.normed_space.riesz_lemma
import linear_algebra.matrix.to_lin
import topology.instances.matrix

/-!
# Finite dimensional normed spaces over complete fields

Over a complete nondiscrete field, in finite dimension, all norms are equivalent and all linear maps
are continuous. Moreover, a finite-dimensional subspace is always complete and closed.

## Main results:

* `linear_map.continuous_of_finite_dimensional` : a linear map on a finite-dimensional space over a
  complete field is continuous.
* `finite_dimensional.complete` : a finite-dimensional space over a complete field is complete. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution.
* `submodule.closed_of_finite_dimensional` : a finite-dimensional subspace over a complete field is
  closed
* `finite_dimensional.proper` : a finite-dimensional space over a proper field is proper. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution. It is however registered as an instance for `𝕜 = ℝ` and `𝕜 = ℂ`. As properness
  implies completeness, there is no need to also register `finite_dimensional.complete` on `ℝ` or
  `ℂ`.
* `finite_dimensional_of_is_compact_closed_ball`: Riesz' theorem: if the closed unit ball is
  compact, then the space is finite-dimensional.

## Implementation notes

The fact that all norms are equivalent is not written explicitly, as it would mean having two norms
on a single space, which is not the way type classes work. However, if one has a
finite-dimensional vector space `E` with a norm, and a copy `E'` of this type with another norm,
then the identities from `E` to `E'` and from `E'`to `E` are continuous thanks to
`linear_map.continuous_of_finite_dimensional`. This gives the desired norm equivalence.
-/

universes u v w x

noncomputable theory

open set finite_dimensional topological_space filter asymptotics
open_locale classical big_operators filter topological_space asymptotics nnreal

namespace linear_isometry

open linear_map

variables {R : Type*} [semiring R]

variables {F E₁ : Type*} [semi_normed_group F]
  [normed_group E₁] [module R E₁]

variables {R₁ : Type*} [field R₁] [module R₁ E₁] [module R₁ F]
  [finite_dimensional R₁ E₁] [finite_dimensional R₁ F]

/-- A linear isometry between finite dimensional spaces of equal dimension can be upgraded
    to a linear isometry equivalence. -/
def to_linear_isometry_equiv
  (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) : E₁ ≃ₗᵢ[R₁] F :=
{ to_linear_equiv :=
    li.to_linear_map.linear_equiv_of_injective li.injective h,
  norm_map' := li.norm_map' }

@[simp] lemma coe_to_linear_isometry_equiv
  (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
  (li.to_linear_isometry_equiv h : E₁ → F) = li := rfl

@[simp] lemma to_linear_isometry_equiv_apply
  (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) (x : E₁) :
  (li.to_linear_isometry_equiv h) x = li x := rfl

end linear_isometry

namespace affine_isometry

open affine_map

variables {𝕜 : Type*} {V₁ V₂  : Type*} {P₁ P₂ : Type*}
  [normed_field 𝕜]
  [normed_group V₁] [semi_normed_group V₂]
  [normed_space 𝕜 V₁] [normed_space 𝕜 V₂]
  [metric_space P₁] [pseudo_metric_space P₂]
  [normed_add_torsor V₁ P₁] [normed_add_torsor V₂ P₂]

variables [finite_dimensional 𝕜 V₁] [finite_dimensional 𝕜 V₂]

/-- An affine isometry between finite dimensional spaces of equal dimension can be upgraded
    to an affine isometry equivalence. -/
def to_affine_isometry_equiv [inhabited P₁]
  (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) : P₁ ≃ᵃⁱ[𝕜] P₂ :=
affine_isometry_equiv.mk' li (li.linear_isometry.to_linear_isometry_equiv h) (arbitrary P₁)
  (λ p, by simp)

@[simp] lemma coe_to_affine_isometry_equiv [inhabited P₁]
  (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) :
  (li.to_affine_isometry_equiv h : P₁ → P₂) = li := rfl

@[simp] lemma to_affine_isometry_equiv_apply [inhabited P₁]
  (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) (x : P₁) :
  (li.to_affine_isometry_equiv h) x = li x := rfl

end affine_isometry

/-- A linear map on `ι → 𝕜` (where `ι` is a fintype) is continuous -/
lemma linear_map.continuous_on_pi {ι : Type w} [fintype ι] {𝕜 : Type u} [normed_field 𝕜]
  {E : Type v}  [add_comm_group E] [module 𝕜 E] [topological_space E]
  [topological_add_group E] [has_continuous_smul 𝕜 E] (f : (ι → 𝕜) →ₗ[𝕜] E) : continuous f :=
begin
  -- for the proof, write `f` in the standard basis, and use that each coordinate is a continuous
  -- function.
  have : (f : (ι → 𝕜) → E) =
         (λx, ∑ i : ι, x i • (f (λj, if i = j then 1 else 0))),
    by { ext x, exact f.pi_apply_eq_sum_univ x },
  rw this,
  refine continuous_finset_sum _ (λi hi, _),
  exact (continuous_apply i).smul continuous_const
end

/-- The space of continuous linear maps between finite-dimensional spaces is finite-dimensional. -/
instance {𝕜 E F : Type*} [field 𝕜] [topological_space 𝕜]
  [topological_space E] [add_comm_group E] [module 𝕜 E] [finite_dimensional 𝕜 E]
  [topological_space F] [add_comm_group F] [module 𝕜 F] [topological_add_group F]
  [has_continuous_smul 𝕜 F] [finite_dimensional 𝕜 F] :
  finite_dimensional 𝕜 (E →L[𝕜] F) :=
finite_dimensional.of_injective
  (continuous_linear_map.coe_lm 𝕜 : (E →L[𝕜] F) →ₗ[𝕜] (E →ₗ[𝕜] F))
  continuous_linear_map.coe_injective

section complete_field

variables {𝕜 : Type u} [nondiscrete_normed_field 𝕜]
{E : Type v} [normed_group E] [normed_space 𝕜 E]
{F : Type w} [normed_group F] [normed_space 𝕜 F]
{F' : Type x} [add_comm_group F'] [module 𝕜 F'] [topological_space F']
[topological_add_group F'] [has_continuous_smul 𝕜 F']
[complete_space 𝕜]

/-- In finite dimension over a complete field, the canonical identification (in terms of a basis)
with `𝕜^n` together with its sup norm is continuous. This is the nontrivial part in the fact that
all norms are equivalent in finite dimension.

This statement is superceded by the fact that every linear map on a finite-dimensional space is
continuous, in `linear_map.continuous_of_finite_dimensional`. -/
lemma continuous_equiv_fun_basis {ι : Type v} [fintype ι] (ξ : basis ι 𝕜 E) :
  continuous ξ.equiv_fun :=
begin
  unfreezingI { induction hn : fintype.card ι with n IH generalizing ι E },
  { apply ξ.equiv_fun.to_linear_map.continuous_of_bound 0 (λx, _),
    have : ξ.equiv_fun x = 0,
      by { ext i, exact (fintype.card_eq_zero_iff.1 hn).elim i },
    change ∥ξ.equiv_fun x∥ ≤ 0 * ∥x∥,
    rw this,
    simp [norm_nonneg] },
  { haveI : finite_dimensional 𝕜 E := of_fintype_basis ξ,
    -- first step: thanks to the inductive assumption, any n-dimensional subspace is equivalent
    -- to a standard space of dimension n, hence it is complete and therefore closed.
    have H₁ : ∀s : submodule 𝕜 E, finrank 𝕜 s = n → is_closed (s : set E),
    { assume s s_dim,
      let b := basis.of_vector_space 𝕜 s,
      have U : uniform_embedding b.equiv_fun.symm.to_equiv,
      { have : fintype.card (basis.of_vector_space_index 𝕜 s) = n,
          by { rw ← s_dim, exact (finrank_eq_card_basis b).symm },
        have : continuous b.equiv_fun := IH b this,
        exact b.equiv_fun.symm.uniform_embedding b.equiv_fun.symm.to_linear_map.continuous_on_pi
          this },
      have : is_complete (s : set E),
        from complete_space_coe_iff_is_complete.1 ((complete_space_congr U).1 (by apply_instance)),
      exact this.is_closed },
    -- second step: any linear form is continuous, as its kernel is closed by the first step
    have H₂ : ∀f : E →ₗ[𝕜] 𝕜, continuous f,
    { assume f,
      have : finrank 𝕜 f.ker = n ∨ finrank 𝕜 f.ker = n.succ,
      { have Z := f.finrank_range_add_finrank_ker,
        rw [finrank_eq_card_basis ξ, hn] at Z,
        by_cases H : finrank 𝕜 f.range = 0,
        { right,
          rw H at Z,
          simpa using Z },
        { left,
          have : finrank 𝕜 f.range = 1,
          { refine le_antisymm _ (zero_lt_iff.mpr H),
            simpa [finrank_self] using f.range.finrank_le },
          rw [this, add_comm, nat.add_one] at Z,
          exact nat.succ.inj Z } },
      have : is_closed (f.ker : set E),
      { cases this,
        { exact H₁ _ this },
        { have : f.ker = ⊤,
            by { apply eq_top_of_finrank_eq, rw [finrank_eq_card_basis ξ, hn, this] },
          simp [this] } },
      exact linear_map.continuous_iff_is_closed_ker.2 this },
    -- third step: applying the continuity to the linear form corresponding to a coefficient in the
    -- basis decomposition, deduce that all such coefficients are controlled in terms of the norm
    have : ∀i:ι, ∃C, 0 ≤ C ∧ ∀(x:E), ∥ξ.equiv_fun x i∥ ≤ C * ∥x∥,
    { assume i,
      let f : E →ₗ[𝕜] 𝕜 := (linear_map.proj i) ∘ₗ ↑ξ.equiv_fun,
      let f' : E →L[𝕜] 𝕜 := { cont := H₂ f, ..f },
      exact ⟨∥f'∥, norm_nonneg _, λx, continuous_linear_map.le_op_norm f' x⟩ },
    -- fourth step: combine the bound on each coefficient to get a global bound and the continuity
    choose C0 hC0 using this,
    let C := ∑ i, C0 i,
    have C_nonneg : 0 ≤ C := finset.sum_nonneg (λi hi, (hC0 i).1),
    have C0_le : ∀i, C0 i ≤ C :=
      λi, finset.single_le_sum (λj hj, (hC0 j).1) (finset.mem_univ _),
    apply ξ.equiv_fun.to_linear_map.continuous_of_bound C (λx, _),
    rw pi_norm_le_iff,
    { exact λi, le_trans ((hC0 i).2 x) (mul_le_mul_of_nonneg_right (C0_le i) (norm_nonneg _)) },
    { exact mul_nonneg C_nonneg (norm_nonneg _) } }
end

/-- Any linear map on a finite dimensional space over a complete field is continuous. -/
theorem linear_map.continuous_of_finite_dimensional [finite_dimensional 𝕜 E] (f : E →ₗ[𝕜] F') :
  continuous f :=
begin
  -- for the proof, go to a model vector space `b → 𝕜` thanks to `continuous_equiv_fun_basis`, and
  -- argue that all linear maps there are continuous.
  let b := basis.of_vector_space 𝕜 E,
  have A : continuous b.equiv_fun :=
    continuous_equiv_fun_basis b,
  have B : continuous (f.comp (b.equiv_fun.symm : (basis.of_vector_space_index 𝕜 E → 𝕜) →ₗ[𝕜] E)) :=
    linear_map.continuous_on_pi _,
  have : continuous ((f.comp (b.equiv_fun.symm : (basis.of_vector_space_index 𝕜 E → 𝕜) →ₗ[𝕜] E))
                      ∘ b.equiv_fun) := B.comp A,
  convert this,
  ext x,
  dsimp,
  rw [basis.equiv_fun_symm_apply, basis.sum_repr]
end

section affine

variables  {PE PF : Type*} [metric_space PE] [normed_add_torsor E PE] [metric_space PF]
  [normed_add_torsor F PF] [finite_dimensional 𝕜 E]

include E F

theorem affine_map.continuous_of_finite_dimensional (f : PE →ᵃ[𝕜] PF) : continuous f :=
affine_map.continuous_linear_iff.1 f.linear.continuous_of_finite_dimensional

theorem affine_equiv.continuous_of_finite_dimensional (f : PE ≃ᵃ[𝕜] PF) : continuous f :=
f.to_affine_map.continuous_of_finite_dimensional

/-- Reinterpret an affine equivalence as a homeomorphism. -/
def affine_equiv.to_homeomorph_of_finite_dimensional (f : PE ≃ᵃ[𝕜] PF) : PE ≃ₜ PF :=
{ to_equiv := f.to_equiv,
  continuous_to_fun := f.continuous_of_finite_dimensional,
  continuous_inv_fun :=
    begin
      haveI : finite_dimensional 𝕜 F, from f.linear.finite_dimensional,
      exact f.symm.continuous_of_finite_dimensional
    end }

@[simp] lemma affine_equiv.coe_to_homeomorph_of_finite_dimensional (f : PE ≃ᵃ[𝕜] PF) :
  ⇑f.to_homeomorph_of_finite_dimensional = f := rfl

@[simp] lemma affine_equiv.coe_to_homeomorph_of_finite_dimensional_symm (f : PE ≃ᵃ[𝕜] PF) :
  ⇑f.to_homeomorph_of_finite_dimensional.symm = f.symm := rfl

end affine

lemma continuous_linear_map.continuous_det :
  continuous (λ (f : E →L[𝕜] E), f.det) :=
begin
  change continuous (λ (f : E →L[𝕜] E), (f : E →ₗ[𝕜] E).det),
  by_cases h : ∃ (s : finset E), nonempty (basis ↥s 𝕜 E),
  { rcases h with ⟨s, ⟨b⟩⟩,
    haveI : finite_dimensional 𝕜 E := finite_dimensional.of_finset_basis b,
    simp_rw linear_map.det_eq_det_to_matrix_of_finset b,
    refine continuous.matrix_det _,
    exact ((linear_map.to_matrix b b).to_linear_map.comp
        (continuous_linear_map.coe_lm 𝕜)).continuous_of_finite_dimensional },
  { unfold linear_map.det,
    simpa only [h, monoid_hom.one_apply, dif_neg, not_false_iff] using continuous_const }
end

namespace linear_map

variables [finite_dimensional 𝕜 E]

/-- The continuous linear map induced by a linear map on a finite dimensional space -/
def to_continuous_linear_map : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F' :=
{ to_fun := λ f, ⟨f, f.continuous_of_finite_dimensional⟩,
  inv_fun := coe,
  map_add' := λ f g, rfl,
  map_smul' := λ c f, rfl,
  left_inv := λ f, rfl,
  right_inv := λ f, continuous_linear_map.coe_injective rfl }

@[simp] lemma coe_to_continuous_linear_map' (f : E →ₗ[𝕜] F') :
  ⇑f.to_continuous_linear_map = f := rfl

@[simp] lemma coe_to_continuous_linear_map (f : E →ₗ[𝕜] F') :
  (f.to_continuous_linear_map : E →ₗ[𝕜] F') = f := rfl

@[simp] lemma coe_to_continuous_linear_map_symm :
  ⇑(to_continuous_linear_map : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F').symm = coe := rfl

end linear_map

namespace linear_equiv

variables [finite_dimensional 𝕜 E]

/-- The continuous linear equivalence induced by a linear equivalence on a finite dimensional
space. -/
def to_continuous_linear_equiv (e : E ≃ₗ[𝕜] F) : E ≃L[𝕜] F :=
{ continuous_to_fun := e.to_linear_map.continuous_of_finite_dimensional,
  continuous_inv_fun := begin
    haveI : finite_dimensional 𝕜 F := e.finite_dimensional,
    exact e.symm.to_linear_map.continuous_of_finite_dimensional
  end,
  ..e }

@[simp] lemma coe_to_continuous_linear_equiv (e : E ≃ₗ[𝕜] F) :
  (e.to_continuous_linear_equiv : E →ₗ[𝕜] F) = e := rfl

@[simp] lemma coe_to_continuous_linear_equiv' (e : E ≃ₗ[𝕜] F) :
  (e.to_continuous_linear_equiv : E → F) = e := rfl

@[simp] lemma coe_to_continuous_linear_equiv_symm (e : E ≃ₗ[𝕜] F) :
  (e.to_continuous_linear_equiv.symm : F →ₗ[𝕜] E) = e.symm := rfl

@[simp] lemma coe_to_continuous_linear_equiv_symm' (e : E ≃ₗ[𝕜] F) :
  (e.to_continuous_linear_equiv.symm : F → E) = e.symm := rfl

@[simp] lemma to_linear_equiv_to_continuous_linear_equiv (e : E ≃ₗ[𝕜] F) :
  e.to_continuous_linear_equiv.to_linear_equiv = e :=
by { ext x, refl }

@[simp] lemma to_linear_equiv_to_continuous_linear_equiv_symm (e : E ≃ₗ[𝕜] F) :
  e.to_continuous_linear_equiv.symm.to_linear_equiv = e.symm :=
by { ext x, refl }

end linear_equiv

namespace continuous_linear_map

variable [finite_dimensional 𝕜 E]

/-- Builds a continuous linear equivalence from a continuous linear map on a finite-dimensional
vector space whose determinant is nonzero. -/
def to_continuous_linear_equiv_of_det_ne_zero
  (f : E →L[𝕜] E) (hf : f.det ≠ 0) : E ≃L[𝕜] E :=
((f : E →ₗ[𝕜] E).equiv_of_det_ne_zero hf).to_continuous_linear_equiv

@[simp] lemma coe_to_continuous_linear_equiv_of_det_ne_zero (f : E →L[𝕜] E) (hf : f.det ≠ 0) :
  (f.to_continuous_linear_equiv_of_det_ne_zero hf : E →L[𝕜] E) = f :=
by { ext x, refl }

@[simp] lemma to_continuous_linear_equiv_of_det_ne_zero_apply
  (f : E →L[𝕜] E) (hf : f.det ≠ 0) (x : E) :
  f.to_continuous_linear_equiv_of_det_ne_zero hf x = f x :=
rfl

end continuous_linear_map

/-- Any `K`-Lipschitz map from a subset `s` of a metric space `α` to a finite-dimensional real
vector space `E'` can be extended to a Lipschitz map on the whole space `α`, with a slightly worse
constant `C * K` where `C` only depends on `E'`. We record a working value for this constant `C`
as `lipschitz_extension_constant E'`. -/
@[irreducible] def lipschitz_extension_constant
  (E' : Type*) [normed_group E'] [normed_space ℝ E'] [finite_dimensional ℝ E'] : ℝ≥0 :=
let A := (basis.of_vector_space ℝ E').equiv_fun.to_continuous_linear_equiv in
  max (∥A.symm.to_continuous_linear_map∥₊ * ∥A.to_continuous_linear_map∥₊) 1

lemma lipschitz_extension_constant_pos
  (E' : Type*) [normed_group E'] [normed_space ℝ E'] [finite_dimensional ℝ E'] :
  0 < lipschitz_extension_constant E' :=
by { rw lipschitz_extension_constant, exact zero_lt_one.trans_le (le_max_right _ _) }

/-- Any `K`-Lipschitz map from a subset `s` of a metric space `α` to a finite-dimensional real
vector space `E'` can be extended to a Lipschitz map on the whole space `α`, with a slightly worse
constant `lipschitz_extension_constant E' * K`. -/
theorem lipschitz_on_with.extend_finite_dimension
  {α : Type*} [pseudo_metric_space α]
  {E' : Type*} [normed_group E'] [normed_space ℝ E'] [finite_dimensional ℝ E']
  {s : set α} {f : α → E'} {K : ℝ≥0} (hf : lipschitz_on_with K f s) :
  ∃ (g : α → E'), lipschitz_with (lipschitz_extension_constant E' * K) g ∧ eq_on f g s :=
begin
  /- This result is already known for spaces `ι → ℝ`. We use a continuous linear equiv between
  `E'` and such a space to transfer the result to `E'`. -/
  let ι : Type* := basis.of_vector_space_index ℝ E',
  let A := (basis.of_vector_space ℝ E').equiv_fun.to_continuous_linear_equiv,
  have LA : lipschitz_with (∥A.to_continuous_linear_map∥₊) A, by apply A.lipschitz,
  have L : lipschitz_on_with (∥A.to_continuous_linear_map∥₊ * K) (A ∘ f) s :=
    LA.comp_lipschitz_on_with hf,
  obtain ⟨g, hg, gs⟩ : ∃ g : α → (ι → ℝ), lipschitz_with (∥A.to_continuous_linear_map∥₊ * K) g ∧
    eq_on (A ∘ f) g s := L.extend_pi,
  refine ⟨A.symm ∘ g, _, _⟩,
  { have LAsymm : lipschitz_with (∥A.symm.to_continuous_linear_map∥₊) A.symm,
      by apply A.symm.lipschitz,
    apply (LAsymm.comp hg).weaken,
    rw [lipschitz_extension_constant, ← mul_assoc],
    refine mul_le_mul' (le_max_left _ _) le_rfl },
  { assume x hx,
    have : A (f x) = g x := gs hx,
    simp only [(∘), ← this, A.symm_apply_apply] }
end

lemma linear_map.exists_antilipschitz_with [finite_dimensional 𝕜 E] (f : E →ₗ[𝕜] F)
  (hf : f.ker = ⊥) : ∃ K > 0, antilipschitz_with K f :=
begin
  cases subsingleton_or_nontrivial E; resetI,
  { exact ⟨1, zero_lt_one, antilipschitz_with.of_subsingleton⟩ },
  { rw linear_map.ker_eq_bot at hf,
    let e : E ≃L[𝕜] f.range := (linear_equiv.of_injective f hf).to_continuous_linear_equiv,
    exact ⟨_, e.nnnorm_symm_pos, e.antilipschitz⟩ }
end

protected lemma linear_independent.eventually {ι} [fintype ι] {f : ι → E}
  (hf : linear_independent 𝕜 f) : ∀ᶠ g in 𝓝 f, linear_independent 𝕜 g :=
begin
  simp only [fintype.linear_independent_iff'] at hf ⊢,
  rcases linear_map.exists_antilipschitz_with _ hf with ⟨K, K0, hK⟩,
  have : tendsto (λ g : ι → E, ∑ i, ∥g i - f i∥) (𝓝 f) (𝓝 $ ∑ i, ∥f i - f i∥),
    from tendsto_finset_sum _ (λ i hi, tendsto.norm $
      ((continuous_apply i).tendsto _).sub tendsto_const_nhds),
  simp only [sub_self, norm_zero, finset.sum_const_zero] at this,
  refine (this.eventually (gt_mem_nhds $ inv_pos.2 K0)).mono (λ g hg, _),
  replace hg : ∑ i, ∥g i - f i∥₊ < K⁻¹, by { rw ← nnreal.coe_lt_coe, push_cast, exact hg },
  rw linear_map.ker_eq_bot,
  refine (hK.add_sub_lipschitz_with (lipschitz_with.of_dist_le_mul $ λ v u, _) hg).injective,
  simp only [dist_eq_norm, linear_map.lsum_apply, pi.sub_apply, linear_map.sum_apply,
    linear_map.comp_apply, linear_map.proj_apply, linear_map.smul_right_apply, linear_map.id_apply,
    ← finset.sum_sub_distrib, ← smul_sub, ← sub_smul, nnreal.coe_sum, coe_nnnorm, finset.sum_mul],
  refine norm_sum_le_of_le _ (λ i _, _),
  rw [norm_smul, mul_comm],
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (v - u) i) (norm_nonneg _)
end

lemma is_open_set_of_linear_independent {ι : Type*} [fintype ι] :
  is_open {f : ι → E | linear_independent 𝕜 f} :=
is_open_iff_mem_nhds.2 $ λ f, linear_independent.eventually

lemma is_open_set_of_nat_le_rank (n : ℕ) : is_open {f : E →L[𝕜] F | ↑n ≤ rank (f : E →ₗ[𝕜] F)} :=
begin
  simp only [le_rank_iff_exists_linear_independent_finset, set_of_exists, ← exists_prop],
  refine is_open_bUnion (λ t ht, _),
  have : continuous (λ f : E →L[𝕜] F, (λ x : (t : set E), f x)),
    from continuous_pi (λ x, (continuous_linear_map.apply 𝕜 F (x : E)).continuous),
  exact is_open_set_of_linear_independent.preimage this
end

/-- Two finite-dimensional normed spaces are continuously linearly equivalent if they have the same
(finite) dimension. -/
theorem finite_dimensional.nonempty_continuous_linear_equiv_of_finrank_eq
  [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F] (cond : finrank 𝕜 E = finrank 𝕜 F) :
  nonempty (E ≃L[𝕜] F) :=
(nonempty_linear_equiv_of_finrank_eq cond).map linear_equiv.to_continuous_linear_equiv

/-- Two finite-dimensional normed spaces are continuously linearly equivalent if and only if they
have the same (finite) dimension. -/
theorem finite_dimensional.nonempty_continuous_linear_equiv_iff_finrank_eq
  [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F] :
   nonempty (E ≃L[𝕜] F) ↔ finrank 𝕜 E = finrank 𝕜 F :=
⟨ λ ⟨h⟩, h.to_linear_equiv.finrank_eq,
  λ h, finite_dimensional.nonempty_continuous_linear_equiv_of_finrank_eq h ⟩

/-- A continuous linear equivalence between two finite-dimensional normed spaces of the same
(finite) dimension. -/
def continuous_linear_equiv.of_finrank_eq [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F]
  (cond : finrank 𝕜 E = finrank 𝕜 F) :
  E ≃L[𝕜] F :=
(linear_equiv.of_finrank_eq E F cond).to_continuous_linear_equiv

variables {ι : Type*} [fintype ι]

/-- Construct a continuous linear map given the value at a finite basis. -/
def basis.constrL (v : basis ι 𝕜 E) (f : ι → F) :
  E →L[𝕜] F :=
by haveI : finite_dimensional 𝕜 E := finite_dimensional.of_fintype_basis v;
  exact (v.constr 𝕜 f).to_continuous_linear_map

@[simp, norm_cast] lemma basis.coe_constrL (v : basis ι 𝕜 E) (f : ι → F) :
  (v.constrL f : E →ₗ[𝕜] F) = v.constr 𝕜 f := rfl

/-- The continuous linear equivalence between a vector space over `𝕜` with a finite basis and
functions from its basis indexing type to `𝕜`. -/
def basis.equiv_funL (v : basis ι 𝕜 E) : E ≃L[𝕜] (ι → 𝕜) :=
{ continuous_to_fun := begin
    haveI : finite_dimensional 𝕜 E := finite_dimensional.of_fintype_basis v,
    exact v.equiv_fun.to_linear_map.continuous_of_finite_dimensional,
  end,
  continuous_inv_fun := begin
    change continuous v.equiv_fun.symm.to_fun,
    exact v.equiv_fun.symm.to_linear_map.continuous_of_finite_dimensional,
  end,
  ..v.equiv_fun }

@[simp] lemma basis.constrL_apply (v : basis ι 𝕜 E) (f : ι → F) (e : E) :
  (v.constrL f) e = ∑ i, (v.equiv_fun e i) • f i :=
v.constr_apply_fintype 𝕜 _ _

@[simp] lemma basis.constrL_basis (v : basis ι 𝕜 E) (f : ι → F) (i : ι) :
  (v.constrL f) (v i) = f i :=
v.constr_basis 𝕜 _ _

lemma basis.op_nnnorm_le {ι : Type*} [fintype ι] (v : basis ι 𝕜 E) {u : E →L[𝕜] F} (M : ℝ≥0)
  (hu : ∀ i, ∥u (v i)∥₊ ≤ M) :
  ∥u∥₊ ≤ fintype.card ι • ∥v.equiv_funL.to_continuous_linear_map∥₊ * M :=
u.op_nnnorm_le_bound _ $ λ e, begin
  set φ := v.equiv_funL.to_continuous_linear_map,
  calc
  ∥u e∥₊ = ∥u (∑ i, v.equiv_fun e i • v i)∥₊ :   by rw [v.sum_equiv_fun]
    ... = ∥∑ i, (v.equiv_fun e i) • (u $ v i)∥₊ : by simp [u.map_sum, linear_map.map_smul]
    ... ≤ ∑ i, ∥(v.equiv_fun e i) • (u $ v i)∥₊ : nnnorm_sum_le _ _
    ... = ∑ i, ∥v.equiv_fun e i∥₊ * ∥u (v i)∥₊ :   by simp only [nnnorm_smul]
    ... ≤ ∑ i, ∥v.equiv_fun e i∥₊ * M : finset.sum_le_sum (λ i hi,
                                                    mul_le_mul_of_nonneg_left (hu i) (zero_le _))
    ... = (∑ i, ∥v.equiv_fun e i∥₊) * M : finset.sum_mul.symm
    ... ≤ fintype.card ι • (∥φ∥₊ * ∥e∥₊) * M :
          (suffices _, from mul_le_mul_of_nonneg_right this (zero_le M),
          calc  ∑ i, ∥v.equiv_fun e i∥₊
              ≤ fintype.card ι • ∥φ e∥₊ : pi.sum_nnnorm_apply_le_nnnorm _
          ... ≤ fintype.card ι • (∥φ∥₊ * ∥e∥₊) : nsmul_le_nsmul_of_le_right (φ.le_op_nnnorm e) _)
    ... = fintype.card ι • ∥φ∥₊ * M * ∥e∥₊ : by simp only [smul_mul_assoc, mul_right_comm],
end

lemma basis.op_norm_le {ι : Type*} [fintype ι] (v : basis ι 𝕜 E) {u : E →L[𝕜] F} {M : ℝ}
  (hM : 0 ≤ M) (hu : ∀ i, ∥u (v i)∥ ≤ M) :
  ∥u∥ ≤ fintype.card ι • ∥v.equiv_funL.to_continuous_linear_map∥ * M :=
by simpa using nnreal.coe_le_coe.mpr (v.op_nnnorm_le ⟨M, hM⟩ hu)

/-- A weaker version of `basis.op_nnnorm_le` that abstracts away the value of `C`. -/
lemma basis.exists_op_nnnorm_le {ι : Type*} [fintype ι] (v : basis ι 𝕜 E) :
  ∃ C > (0 : ℝ≥0), ∀ {u : E →L[𝕜] F} (M : ℝ≥0), (∀ i, ∥u (v i)∥₊ ≤ M) → ∥u∥₊ ≤ C*M :=
⟨ max (fintype.card ι • ∥v.equiv_funL.to_continuous_linear_map∥₊) 1,
  zero_lt_one.trans_le (le_max_right _ _),
  λ u M hu, (v.op_nnnorm_le M hu).trans $ mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le M)⟩

/-- A weaker version of `basis.op_norm_le` that abstracts away the value of `C`. -/
lemma basis.exists_op_norm_le {ι : Type*} [fintype ι] (v : basis ι 𝕜 E) :
  ∃ C > (0 : ℝ), ∀ {u : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ∥u (v i)∥ ≤ M) → ∥u∥ ≤ C*M :=
let ⟨C, hC, h⟩ := v.exists_op_nnnorm_le in ⟨C, hC, λ u, subtype.forall'.mpr h⟩

instance [finite_dimensional 𝕜 E] [second_countable_topology F] :
  second_countable_topology (E →L[𝕜] F) :=
begin
  set d := finite_dimensional.finrank 𝕜 E,
  suffices :
    ∀ ε > (0 : ℝ), ∃ n : (E →L[𝕜] F) → fin d → ℕ, ∀ (f g : E →L[𝕜] F), n f = n g → dist f g ≤ ε,
  from metric.second_countable_of_countable_discretization
    (λ ε ε_pos, ⟨fin d → ℕ, by apply_instance, this ε ε_pos⟩),
  intros ε ε_pos,
  obtain ⟨u : ℕ → F, hu : dense_range u⟩ := exists_dense_seq F,
  let v := finite_dimensional.fin_basis 𝕜 E,
  obtain ⟨C : ℝ, C_pos : 0 < C,
          hC : ∀ {φ : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ∥φ (v i)∥ ≤ M) → ∥φ∥ ≤ C * M⟩ :=
    v.exists_op_norm_le,
  have h_2C : 0 < 2*C := mul_pos zero_lt_two C_pos,
  have hε2C : 0 < ε/(2*C) := div_pos ε_pos h_2C,
  have : ∀ φ : E →L[𝕜] F, ∃ n : fin d → ℕ, ∥φ - (v.constrL $ u ∘ n)∥ ≤ ε/2,
  { intros φ,
    have : ∀ i, ∃ n, ∥φ (v i) - u n∥ ≤ ε/(2*C),
    { simp only [norm_sub_rev],
      intro i,
      have : φ (v i) ∈ closure (range u) := hu _,
      obtain ⟨n, hn⟩ : ∃ n, ∥u n - φ (v i)∥ < ε / (2 * C),
      { rw mem_closure_iff_nhds_basis metric.nhds_basis_ball at this,
        specialize this (ε/(2*C)) hε2C,
        simpa [dist_eq_norm] },
      exact ⟨n, le_of_lt hn⟩ },
    choose n hn using this,
    use n,
    replace hn : ∀ i : fin d, ∥(φ - (v.constrL $ u ∘ n)) (v i)∥ ≤ ε / (2 * C), by simp [hn],
    have : C * (ε / (2 * C)) = ε/2,
    { rw [eq_div_iff (two_ne_zero : (2 : ℝ) ≠ 0), mul_comm, ← mul_assoc,
          mul_div_cancel' _ (ne_of_gt h_2C)] },
    specialize hC (le_of_lt hε2C) hn,
    rwa this at hC },
  choose n hn using this,
  set Φ := λ φ : E →L[𝕜] F, (v.constrL $ u ∘ (n φ)),
  change ∀ z, dist z (Φ z) ≤ ε/2 at hn,
  use n,
  intros x y hxy,
  calc dist x y ≤ dist x (Φ x) + dist (Φ x) y : dist_triangle _ _ _
  ... = dist x (Φ x) + dist y (Φ y) : by simp [Φ, hxy, dist_comm]
  ... ≤ ε : by linarith [hn x, hn y]
end

/-- Any finite-dimensional vector space over a complete field is complete.
We do not register this as an instance to avoid an instance loop when trying to prove the
completeness of `𝕜`, and the search for `𝕜` as an unknown metavariable. Declare the instance
explicitly when needed. -/
variables (𝕜 E)
lemma finite_dimensional.complete [finite_dimensional 𝕜 E] : complete_space E :=
begin
  set e := continuous_linear_equiv.of_finrank_eq (@finrank_fin_fun 𝕜 _ (finrank 𝕜 E)).symm,
  have : uniform_embedding e.to_linear_equiv.to_equiv.symm := e.symm.uniform_embedding,
  exact (complete_space_congr this).1 (by apply_instance)
end

variables {𝕜 E}
/-- A finite-dimensional subspace is complete. -/
lemma submodule.complete_of_finite_dimensional (s : submodule 𝕜 E) [finite_dimensional 𝕜 s] :
  is_complete (s : set E) :=
complete_space_coe_iff_is_complete.1 (finite_dimensional.complete 𝕜 s)

/-- A finite-dimensional subspace is closed. -/
lemma submodule.closed_of_finite_dimensional (s : submodule 𝕜 E) [finite_dimensional 𝕜 s] :
  is_closed (s : set E) :=
s.complete_of_finite_dimensional.is_closed

lemma affine_subspace.closed_of_finite_dimensional {P : Type*} [metric_space P]
  [normed_add_torsor E P] (s : affine_subspace 𝕜 P) [finite_dimensional 𝕜 s.direction] :
  is_closed (s : set P) :=
s.is_closed_direction_iff.mp s.direction.closed_of_finite_dimensional

section riesz

/-- In an infinite dimensional space, given a finite number of points, one may find a point
with norm at most `R` which is at distance at least `1` of all these points. -/
theorem exists_norm_le_le_norm_sub_of_finset {c : 𝕜} (hc : 1 < ∥c∥) {R : ℝ} (hR : ∥c∥ < R)
  (h : ¬ (finite_dimensional 𝕜 E)) (s : finset E) :
  ∃ (x : E), ∥x∥ ≤ R ∧ ∀ y ∈ s, 1 ≤ ∥y - x∥ :=
begin
  let F := submodule.span 𝕜 (s : set E),
  haveI : finite_dimensional 𝕜 F := module.finite_def.2
    ((submodule.fg_top _).2 (submodule.fg_def.2 ⟨s, finset.finite_to_set _, rfl⟩)),
  have Fclosed : is_closed (F : set E) := submodule.closed_of_finite_dimensional _,
  have : ∃ x, x ∉ F,
  { contrapose! h,
    have : (⊤ : submodule 𝕜 E) = F, by { ext x, simp [h] },
    have : finite_dimensional 𝕜 (⊤ : submodule 𝕜 E), by rwa this,
    refine module.finite_def.2 ((submodule.fg_top _).1 (module.finite_def.1 this)) },
  obtain ⟨x, xR, hx⟩ : ∃ (x : E), ∥x∥ ≤ R ∧ ∀ (y : E), y ∈ F → 1 ≤ ∥x - y∥ :=
    riesz_lemma_of_norm_lt hc hR Fclosed this,
  have hx' : ∀ (y : E), y ∈ F → 1 ≤ ∥y - x∥,
  { assume y hy, rw ← norm_neg, simpa using hx y hy },
  exact ⟨x, xR, λ y hy, hx' _ (submodule.subset_span hy)⟩,
end

/-- In an infinite-dimensional normed space, there exists a sequence of points which are all
bounded by `R` and at distance at least `1`. For a version not assuming `c` and `R`, see
`exists_seq_norm_le_one_le_norm_sub`. -/
theorem exists_seq_norm_le_one_le_norm_sub' {c : 𝕜} (hc : 1 < ∥c∥) {R : ℝ} (hR : ∥c∥ < R)
  (h : ¬ (finite_dimensional 𝕜 E)) :
  ∃ f : ℕ → E, (∀ n, ∥f n∥ ≤ R) ∧ (∀ m n, m ≠ n → 1 ≤ ∥f m - f n∥) :=
begin
  haveI : is_symm E (λ (x y : E), 1 ≤ ∥x - y∥),
  { constructor,
    assume x y hxy,
    rw ← norm_neg,
    simpa },
  apply exists_seq_of_forall_finset_exists' (λ (x : E), ∥x∥ ≤ R) (λ (x : E) (y : E), 1 ≤ ∥x - y∥),
  assume s hs,
  exact exists_norm_le_le_norm_sub_of_finset hc hR h s,
end

theorem exists_seq_norm_le_one_le_norm_sub (h : ¬ (finite_dimensional 𝕜 E)) :
  ∃ (R : ℝ) (f : ℕ → E), (1 < R) ∧ (∀ n, ∥f n∥ ≤ R) ∧ (∀ m n, m ≠ n → 1 ≤ ∥f m - f n∥) :=
begin
  obtain ⟨c, hc⟩ : ∃ (c : 𝕜), 1 < ∥c∥ := normed_field.exists_one_lt_norm 𝕜,
  have A : ∥c∥ < ∥c∥ + 1, by linarith,
  rcases exists_seq_norm_le_one_le_norm_sub' hc A h with ⟨f, hf⟩,
  exact ⟨∥c∥ + 1, f, hc.trans A, hf.1, hf.2⟩
end

variable (𝕜)

/-- **Riesz's theorem**: if a closed ball with center zero of positive radius is compact in a vector
space, then the space is finite-dimensional. -/
theorem finite_dimensional_of_is_compact_closed_ball₀ {r : ℝ} (rpos : 0 < r)
  (h : is_compact (metric.closed_ball (0 : E) r)) : finite_dimensional 𝕜 E :=
begin
  by_contra hfin,
  obtain ⟨R, f, Rgt, fle, lef⟩ :
    ∃ (R : ℝ) (f : ℕ → E), (1 < R) ∧ (∀ n, ∥f n∥ ≤ R) ∧ (∀ m n, m ≠ n → 1 ≤ ∥f m - f n∥) :=
      exists_seq_norm_le_one_le_norm_sub hfin,
  have rRpos : 0 < r / R := div_pos rpos (zero_lt_one.trans Rgt),
  obtain ⟨c, hc⟩ : ∃ (c : 𝕜), 0 < ∥c∥ ∧ ∥c∥ < (r / R) := normed_field.exists_norm_lt _ rRpos,
  let g := λ (n : ℕ), c • f n,
  have A : ∀ n, g n ∈ metric.closed_ball (0 : E) r,
  { assume n,
    simp only [norm_smul, dist_zero_right, metric.mem_closed_ball],
    calc ∥c∥ * ∥f n∥ ≤ (r / R) * R : mul_le_mul hc.2.le (fle n) (norm_nonneg _) rRpos.le
    ... = r : by field_simp [(zero_lt_one.trans Rgt).ne'] },
  obtain ⟨x, hx, φ, φmono, φlim⟩ : ∃ (x : E) (H : x ∈ metric.closed_ball (0 : E) r) (φ : ℕ → ℕ),
    strict_mono φ ∧ tendsto (g ∘ φ) at_top (𝓝 x) := h.tendsto_subseq A,
  have B : cauchy_seq (g ∘ φ) := φlim.cauchy_seq,
  obtain ⟨N, hN⟩ : ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → dist ((g ∘ φ) n) ((g ∘ φ) N) < ∥c∥ :=
    metric.cauchy_seq_iff'.1 B (∥c∥) hc.1,
  apply lt_irrefl (∥c∥),
  calc ∥c∥ ≤ dist (g (φ (N+1))) (g (φ N)) : begin
    conv_lhs { rw [← mul_one (∥c∥)] },
    simp only [g, dist_eq_norm, ←smul_sub, norm_smul, -mul_one],
    apply mul_le_mul_of_nonneg_left (lef _ _ (ne_of_gt _)) (norm_nonneg _),
    exact φmono (nat.lt_succ_self N)
  end
  ... < ∥c∥ : hN (N+1) (nat.le_succ N)
end

/-- **Riesz's theorem**: if a closed ball of positive radius is compact in a vector space, then the
space is finite-dimensional. -/
theorem finite_dimensional_of_is_compact_closed_ball {r : ℝ} (rpos : 0 < r) {c : E}
  (h : is_compact (metric.closed_ball c r)) : finite_dimensional 𝕜 E :=
begin
  apply finite_dimensional_of_is_compact_closed_ball₀ 𝕜 rpos,
  have : continuous (λ x, -c + x), from continuous_const.add continuous_id,
  simpa using h.image this,
end

end riesz

/-- An injective linear map with finite-dimensional domain is a closed embedding. -/
lemma linear_equiv.closed_embedding_of_injective {f : E →ₗ[𝕜] F} (hf : f.ker = ⊥)
  [finite_dimensional 𝕜 E] :
  closed_embedding ⇑f :=
let g := linear_equiv.of_injective f (linear_map.ker_eq_bot.mp hf) in
{ closed_range := begin
    haveI := f.finite_dimensional_range,
    simpa [f.range_coe] using f.range.closed_of_finite_dimensional
  end,
  .. embedding_subtype_coe.comp g.to_continuous_linear_equiv.to_homeomorph.embedding }

lemma continuous_linear_map.exists_right_inverse_of_surjective [finite_dimensional 𝕜 F]
  (f : E →L[𝕜] F) (hf : f.range = ⊤) :
  ∃ g : F →L[𝕜] E, f.comp g = continuous_linear_map.id 𝕜 F :=
let ⟨g, hg⟩ := (f : E →ₗ[𝕜] F).exists_right_inverse_of_surjective hf in
⟨g.to_continuous_linear_map, continuous_linear_map.ext $ linear_map.ext_iff.1 hg⟩

lemma closed_embedding_smul_left {c : E} (hc : c ≠ 0) : closed_embedding (λ x : 𝕜, x • c) :=
linear_equiv.closed_embedding_of_injective (linear_map.ker_to_span_singleton 𝕜 E hc)

/- `smul` is a closed map in the first argument. -/
lemma is_closed_map_smul_left (c : E) : is_closed_map (λ x : 𝕜, x • c) :=
begin
  by_cases hc : c = 0,
  { simp_rw [hc, smul_zero], exact is_closed_map_const },
  { exact (closed_embedding_smul_left hc).is_closed_map }
end

open continuous_linear_map
/-- Continuous linear equivalence between continuous linear functions `𝕜ⁿ → E` and `Eⁿ`.
The spaces `𝕜ⁿ` and `Eⁿ` are represented as `ι → 𝕜` and `ι → E`, respectively,
where `ι` is a finite type. -/
def continuous_linear_equiv.pi_ring (ι : Type*) [fintype ι] [decidable_eq ι] :
  ((ι → 𝕜) →L[𝕜] E) ≃L[𝕜] (ι → E) :=
{ continuous_to_fun :=
  begin
    refine continuous_pi (λ i, _),
    exact (continuous_linear_map.apply 𝕜 E (pi.single i 1)).continuous,
  end,
  continuous_inv_fun :=
  begin
    simp_rw [linear_equiv.inv_fun_eq_symm, linear_equiv.trans_symm, linear_equiv.symm_symm],
    change continuous (linear_map.to_continuous_linear_map.to_linear_map.comp
                      (linear_equiv.pi_ring 𝕜 E ι 𝕜).symm.to_linear_map),
    apply linear_map.continuous_of_bound _ (fintype.card ι : ℝ) (λ g, _),
    rw ← nsmul_eq_mul,
    apply op_norm_le_bound _ (nsmul_nonneg (norm_nonneg g) (fintype.card ι)) (λ t, _),
    simp_rw [linear_map.coe_comp, linear_equiv.coe_to_linear_map, function.comp_app,
      linear_map.coe_to_continuous_linear_map', linear_equiv.pi_ring_symm_apply],
    apply le_trans (norm_sum_le _ _),
    rw smul_mul_assoc,
    refine finset.sum_le_card_nsmul _ _ _ (λ i hi, _),
    rw [norm_smul, mul_comm],
    exact mul_le_mul (norm_le_pi_norm g i) (norm_le_pi_norm t i) (norm_nonneg _) (norm_nonneg g),
  end,
  .. linear_map.to_continuous_linear_map.symm.trans (linear_equiv.pi_ring 𝕜 E ι 𝕜) }

/-- A family of continuous linear maps is continuous on `s` if all its applications are. -/
lemma continuous_on_clm_apply {X : Type*} [topological_space X]
  [finite_dimensional 𝕜 E] {f : X → E →L[𝕜] F} {s : set X} :
  continuous_on f s ↔ ∀ y, continuous_on (λ x, f x y) s :=
begin
  refine ⟨λ h y, (continuous_linear_map.apply 𝕜 F y).continuous.comp_continuous_on h, λ h, _⟩,
  let d := finrank 𝕜 E,
  have hd : d = finrank 𝕜 (fin d → 𝕜) := (finrank_fin_fun 𝕜).symm,
  let e₁ : E ≃L[𝕜] fin d → 𝕜 := continuous_linear_equiv.of_finrank_eq hd,
  let e₂ : (E →L[𝕜] F) ≃L[𝕜] fin d → F :=
    (e₁.arrow_congr (1 : F ≃L[𝕜] F)).trans (continuous_linear_equiv.pi_ring (fin d)),
  rw [← function.comp.left_id f, ← e₂.symm_comp_self],
  exact e₂.symm.continuous.comp_continuous_on (continuous_on_pi.mpr (λ i, h _))
end

lemma continuous_clm_apply {X : Type*} [topological_space X] [finite_dimensional 𝕜 E]
  {f : X → E →L[𝕜] F} :
  continuous f ↔ ∀ y, continuous (λ x, f x y) :=
by simp_rw [continuous_iff_continuous_on_univ, continuous_on_clm_apply]

end complete_field

section proper_field
variables (𝕜 : Type u) [nondiscrete_normed_field 𝕜]
(E : Type v) [normed_group E] [normed_space 𝕜 E] [proper_space 𝕜]

/-- Any finite-dimensional vector space over a proper field is proper.
We do not register this as an instance to avoid an instance loop when trying to prove the
properness of `𝕜`, and the search for `𝕜` as an unknown metavariable. Declare the instance
explicitly when needed. -/
lemma finite_dimensional.proper [finite_dimensional 𝕜 E] : proper_space E :=
begin
  set e := continuous_linear_equiv.of_finrank_eq (@finrank_fin_fun 𝕜 _ (finrank 𝕜 E)).symm,
  exact e.symm.antilipschitz.proper_space e.symm.continuous e.symm.surjective
end

end proper_field

/- Over the real numbers, we can register the previous statement as an instance as it will not
cause problems in instance resolution since the properness of `ℝ` is already known. -/
@[priority 900]
instance finite_dimensional.proper_real
  (E : Type u) [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E] : proper_space E :=
finite_dimensional.proper ℝ E

/-- If `E` is a finite dimensional normed real vector space, `x : E`, and `s` is a neighborhood of
`x` that is not equal to the whole space, then there exists a point `y ∈ frontier s` at distance
`metric.inf_dist x sᶜ` from `x`. See also
`is_compact.exists_mem_frontier_inf_dist_compl_eq_dist`. -/
lemma exists_mem_frontier_inf_dist_compl_eq_dist {E : Type*} [normed_group E]
  [normed_space ℝ E] [finite_dimensional ℝ E] {x : E} {s : set E} (hx : x ∈ s) (hs : s ≠ univ) :
  ∃ y ∈ frontier s, metric.inf_dist x sᶜ = dist x y :=
begin
  rcases metric.exists_mem_closure_inf_dist_eq_dist (nonempty_compl.2 hs) x with ⟨y, hys, hyd⟩,
  rw closure_compl at hys,
  refine ⟨y, ⟨metric.closed_ball_inf_dist_compl_subset_closure hx $
    metric.mem_closed_ball.2 $ ge_of_eq _, hys⟩, hyd⟩,
  rwa dist_comm
end

/-- If `K` is a compact set in a nontrivial real normed space and `x ∈ K`, then there exists a point
`y` of the boundary of `K` at distance `metric.inf_dist x Kᶜ` from `x`. See also
`exists_mem_frontier_inf_dist_compl_eq_dist`. -/
lemma is_compact.exists_mem_frontier_inf_dist_compl_eq_dist {E : Type*} [normed_group E]
  [normed_space ℝ E] [nontrivial E] {x : E} {K : set E} (hK : is_compact K) (hx : x ∈ K) :
  ∃ y ∈ frontier K, metric.inf_dist x Kᶜ = dist x y :=
begin
  obtain (hx'|hx') : x ∈ interior K ∪ frontier K,
  { rw ← closure_eq_interior_union_frontier, exact subset_closure hx },
  { rw [mem_interior_iff_mem_nhds, metric.nhds_basis_closed_ball.mem_iff] at hx',
    rcases hx' with ⟨r, hr₀, hrK⟩,
    haveI : finite_dimensional ℝ E,
      from finite_dimensional_of_is_compact_closed_ball ℝ hr₀
        (compact_of_is_closed_subset hK metric.is_closed_ball hrK),
    exact exists_mem_frontier_inf_dist_compl_eq_dist hx hK.ne_univ },
  { refine ⟨x, hx', _⟩,
    rw frontier_eq_closure_inter_closure at hx',
    rw [metric.inf_dist_zero_of_mem_closure hx'.2, dist_self] },
end

/-- In a finite dimensional vector space over `ℝ`, the series `∑ x, ∥f x∥` is unconditionally
summable if and only if the series `∑ x, f x` is unconditionally summable. One implication holds in
any complete normed space, while the other holds only in finite dimensional spaces. -/
lemma summable_norm_iff {α E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {f : α → E} : summable (λ x, ∥f x∥) ↔ summable f :=
begin
  refine ⟨summable_of_summable_norm, λ hf, _⟩,
  -- First we use a finite basis to reduce the problem to the case `E = fin N → ℝ`
  suffices : ∀ {N : ℕ} {g : α → fin N → ℝ}, summable g → summable (λ x, ∥g x∥),
  { obtain v := fin_basis ℝ E,
    set e := v.equiv_funL,
    have : summable (λ x, ∥e (f x)∥) := this (e.summable.2 hf),
    refine summable_of_norm_bounded _ (this.mul_left
      ↑(∥(e.symm : (fin (finrank ℝ E) → ℝ) →L[ℝ] E)∥₊)) (λ i, _),
    simpa using (e.symm : (fin (finrank ℝ E) → ℝ) →L[ℝ] E).le_op_norm (e $ f i) },
  unfreezingI { clear_dependent E },
  -- Now we deal with `g : α → fin N → ℝ`
  intros N g hg,
  have : ∀ i, summable (λ x, ∥g x i∥) := λ i, (pi.summable.1 hg i).abs,
  refine summable_of_norm_bounded _ (summable_sum (λ i (hi : i ∈ finset.univ), this i)) (λ x, _),
  rw [norm_norm, pi_norm_le_iff],
  { refine λ i, finset.single_le_sum (λ i hi, _) (finset.mem_univ i),
    exact norm_nonneg (g x i) },
  { exact finset.sum_nonneg (λ _ _, norm_nonneg _) }
end

lemma summable_of_is_O' {ι E F : Type*} [normed_group E] [complete_space E] [normed_group F]
  [normed_space ℝ F] [finite_dimensional ℝ F] {f : ι → E} {g : ι → F}
  (hg : summable g) (h : is_O f g cofinite) : summable f :=
summable_of_is_O (summable_norm_iff.mpr hg) h.norm_right

lemma summable_of_is_O_nat' {E F : Type*} [normed_group E] [complete_space E] [normed_group F]
  [normed_space ℝ F] [finite_dimensional ℝ F] {f : ℕ → E} {g : ℕ → F}
  (hg : summable g) (h : is_O f g at_top) : summable f :=
summable_of_is_O_nat (summable_norm_iff.mpr hg) h.norm_right

lemma summable_of_is_equivalent {ι E : Type*} [normed_group E] [normed_space ℝ E]
  [finite_dimensional ℝ E] {f : ι → E} {g : ι → E}
  (hg : summable g) (h : f ~[cofinite] g) : summable f :=
hg.trans_sub (summable_of_is_O' hg h.is_o.is_O)

lemma summable_of_is_equivalent_nat {E : Type*} [normed_group E] [normed_space ℝ E]
  [finite_dimensional ℝ E] {f : ℕ → E} {g : ℕ → E}
  (hg : summable g) (h : f ~[at_top] g) : summable f :=
hg.trans_sub (summable_of_is_O_nat' hg h.is_o.is_O)

lemma is_equivalent.summable_iff {ι E : Type*} [normed_group E] [normed_space ℝ E]
  [finite_dimensional ℝ E] {f : ι → E} {g : ι → E}
  (h : f ~[cofinite] g) : summable f ↔ summable g :=
⟨λ hf, summable_of_is_equivalent hf h.symm, λ hg, summable_of_is_equivalent hg h⟩

lemma is_equivalent.summable_iff_nat {E : Type*} [normed_group E] [normed_space ℝ E]
  [finite_dimensional ℝ E] {f : ℕ → E} {g : ℕ → E}
  (h : f ~[at_top] g) : summable f ↔ summable g :=
⟨λ hf, summable_of_is_equivalent_nat hf h.symm, λ hg, summable_of_is_equivalent_nat hg h⟩
