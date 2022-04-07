/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Anatole Dedecker
-/
import analysis.normed.normed_field

/-!
# TODO
-/

universes u v w x

noncomputable theory

open set finite_dimensional topological_space filter
open_locale classical big_operators filter topological_space nnreal uniformity

section move_me

lemma equiv.uniform_embedding {α β : Type*} [uniform_space α] [uniform_space β] (f : α ≃ β)
  (h₁ : uniform_continuous f) (h₂ : uniform_continuous f.symm) : uniform_embedding f :=
{ comap_uniformity :=
  begin
    refine le_antisymm _ _,
    { change comap (f.prod_congr f) _ ≤ _,
      rw ← map_equiv_symm (f.prod_congr f),
      exact h₂ },
    { rw ← map_le_iff_le_comap,
      exact h₁ }
  end,
  inj := f.injective }

variables {𝕜 𝕜₂ E F : Type*} [semiring 𝕜] [semiring 𝕜₂]
  [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜₂ F]
  [uniform_space E] [uniform_space F] [uniform_add_group E] [uniform_add_group F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜}

lemma continuous_linear_map.uniform_continuous (f : E →SL[σ₁₂] F) : uniform_continuous f :=
(f : E →+ F).uniform_continuous_of_continuous_at_zero f.continuous.continuous_at

lemma continuous_linear_equiv.uniform_embedding
  [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂] (e : E ≃SL[σ₁₂] F) :
  uniform_embedding e :=
e.to_linear_equiv.to_equiv.uniform_embedding
  e.to_continuous_linear_map.uniform_continuous
  e.symm.to_continuous_linear_map.uniform_continuous

lemma linear_equiv.uniform_embedding [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]
  (e : E ≃ₛₗ[σ₁₂] F) (h₁ : continuous e)
  (h₂ : continuous e.symm) : uniform_embedding e :=
continuous_linear_equiv.uniform_embedding
({ continuous_to_fun := h₁,
  continuous_inv_fun := h₂,
  .. e } : E ≃SL[σ₁₂] F)

end move_me

/-- A linear map on `ι → 𝕜` (where `ι` is a fintype) is continuous -/
lemma linear_map.continuous_on_pi {ι : Type w} [fintype ι] {𝕜 : Type u} [field 𝕜]
  [topological_space 𝕜] {E : Type v}  [add_comm_group E] [module 𝕜 E] [topological_space E]
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
begin
  haveI : is_noetherian 𝕜 (E →ₗ[𝕜] F) := is_noetherian.iff_fg.mpr (by apply_instance),
  let I : (E →L[𝕜] F) →ₗ[𝕜] (E →ₗ[𝕜] F) := continuous_linear_map.coe_lm 𝕜,
  exact module.finite.of_injective I continuous_linear_map.coe_injective
end

section complete_field

variables {𝕜 : Type u} [nondiscrete_normed_field 𝕜]
{E : Type v} [add_comm_group E] [module 𝕜 E] [topological_space E]
[topological_add_group E] [has_continuous_smul 𝕜 E]
{F : Type w} [add_comm_group F] [module 𝕜 F] [topological_space F]
[topological_add_group F] [has_continuous_smul 𝕜 F]
{F' : Type x} [add_comm_group F'] [module 𝕜 F'] [topological_space F']
[topological_add_group F'] [has_continuous_smul 𝕜 F']
[complete_space 𝕜]

lemma linear_map.continuous_of_is_closed_ker (l : E →ₗ[𝕜] 𝕜) (hl : is_closed (l.ker : set E)) :
  continuous l :=
sorry

/-- In finite dimension over a complete field, the canonical identification (in terms of a basis)
with `𝕜^n` together with its sup norm is continuous. This is the nontrivial part in the fact that
all norms are equivalent in finite dimension.

This statement is superceded by the fact that every linear map on a finite-dimensional space is
continuous, in `linear_map.continuous_of_finite_dimensional`. -/
lemma continuous_equiv_fun_basis [ht2 : t2_space E] {ι : Type v} [fintype ι] (ξ : basis ι 𝕜 E) :
  continuous ξ.equiv_fun :=
begin
  letI : uniform_space E := topological_add_group.to_uniform_space E,
  letI : uniform_add_group E := topological_add_group_is_uniform,
  letI : separated_space E := separated_iff_t2.mpr ht2,
  unfreezingI { induction hn : fintype.card ι with n IH generalizing ι E },
  { rw fintype.card_eq_zero_iff at hn,
    exact continuous_of_const (λ x y, funext hn.elim) },
  { haveI : finite_dimensional 𝕜 E := of_fintype_basis ξ,
    -- first step: thanks to the inductive assumption, any n-dimensional subspace is equivalent
    -- to a standard space of dimension n, hence it is complete and therefore closed.
    have H₁ : ∀s : submodule 𝕜 E, finrank 𝕜 s = n → is_closed (s : set E),
    { assume s s_dim,
      letI : uniform_add_group s := sorry,
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
          rwa [H, zero_add] at Z },
        { left,
          have : finrank 𝕜 f.range = 1,
            from le_antisymm (finrank_self 𝕜 ▸ f.range.finrank_le) (zero_lt_iff.mpr H),
          rw [this, add_comm, nat.add_one] at Z,
          exact nat.succ.inj Z } },
      have : is_closed (f.ker : set E),
      { cases this,
        { exact H₁ _ this },
        { have : f.ker = ⊤,
            by { apply eq_top_of_finrank_eq, rw [finrank_eq_card_basis ξ, hn, this] },
          rw [this]
          exact is_closed_univ } },
      exact linear_map.continuous_of_is_closed_ker f this },
    rw continuous_pi_iff,
    intros i,
    change continuous (ξ.coord i),
    exact H₂ (ξ.coord i) },
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

theorem affine_map.continuous_of_finite_dimensional {PE PF : Type*}
  [metric_space PE] [normed_add_torsor E PE] [metric_space PF] [normed_add_torsor F PF]
  [finite_dimensional 𝕜 E] (f : PE →ᵃ[𝕜] PF) : continuous f :=
affine_map.continuous_linear_iff.1 f.linear.continuous_of_finite_dimensional

lemma continuous_linear_map.continuous_det :
  continuous (λ (f : E →L[𝕜] E), f.det) :=
begin
  change continuous (λ (f : E →L[𝕜] E), (f : E →ₗ[𝕜] E).det),
  classical,
  by_cases h : ∃ (s : finset E), nonempty (basis ↥s 𝕜 E),
  { rcases h with ⟨s, ⟨b⟩⟩,
    haveI : finite_dimensional 𝕜 E := finite_dimensional.of_finset_basis b,
    letI : normed_group (matrix s s 𝕜) := matrix.normed_group,
    letI : normed_space 𝕜 (matrix s s 𝕜) := matrix.normed_space,
    simp_rw linear_map.det_eq_det_to_matrix_of_finset b,
    have A : continuous (λ (f : E →L[𝕜] E), linear_map.to_matrix b b f),
    { change continuous ((linear_map.to_matrix b b).to_linear_map.comp
        (continuous_linear_map.coe_lm 𝕜)),
      exact linear_map.continuous_of_finite_dimensional _ },
    convert A.matrix_det,
    ext f,
    congr },
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

end complete_field
