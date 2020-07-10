/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.normed_space.operator_norm
import linear_algebra.finite_dimensional
import tactic.omega

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

## Implementation notes

The fact that all norms are equivalent is not written explicitly, as it would mean having two norms
on a single space, which is not the way type classes work. However, if one has a
finite-dimensional vector space `E` with a norm, and a copy `E'` of this type with another norm,
then the identities from `E` to `E'` and from `E'`to `E` are continuous thanks to
`linear_map.continuous_of_finite_dimensional`. This gives the desired norm equivalence.
-/

universes u v w x

open set finite_dimensional
open_locale classical big_operators

/-- A linear map on `ι → 𝕜` (where `ι` is a fintype) is continuous -/
lemma linear_map.continuous_on_pi {ι : Type w} [fintype ι] {𝕜 : Type u} [normed_field 𝕜]
  {E : Type v}  [add_comm_group E] [vector_space 𝕜 E] [topological_space E]
  [topological_add_group E] [topological_vector_space 𝕜 E] (f : (ι → 𝕜) →ₗ[𝕜] E) : continuous f :=
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

section complete_field

variables {𝕜 : Type u} [nondiscrete_normed_field 𝕜]
{E : Type v} [normed_group E] [normed_space 𝕜 E]
{F : Type w} [normed_group F] [normed_space 𝕜 F]
{F' : Type x} [add_comm_group F'] [vector_space 𝕜 F'] [topological_space F']
[topological_add_group F'] [topological_vector_space 𝕜 F']
[complete_space 𝕜]


/-- In finite dimension over a complete field, the canonical identification (in terms of a basis)
with `𝕜^n` together with its sup norm is continuous. This is the nontrivial part in the fact that
all norms are equivalent in finite dimension.

This statement is superceded by the fact that every linear map on a finite-dimensional space is
continuous, in `linear_map.continuous_of_finite_dimensional`. -/
lemma continuous_equiv_fun_basis {ι : Type v} [fintype ι] (ξ : ι → E) (hξ : is_basis 𝕜 ξ) :
  continuous (equiv_fun_basis hξ) :=
begin
  unfreezingI { induction hn : fintype.card ι with n IH generalizing ι E },
  { apply linear_map.continuous_of_bound _ 0 (λx, _),
    have : equiv_fun_basis hξ x = 0,
      by { ext i, exact (fintype.card_eq_zero_iff.1 hn i).elim },
    change ∥equiv_fun_basis hξ x∥ ≤ 0 * ∥x∥,
    rw this,
    simp [norm_nonneg] },
  { haveI : finite_dimensional 𝕜 E := of_finite_basis hξ,
    -- first step: thanks to the inductive assumption, any n-dimensional subspace is equivalent
    -- to a standard space of dimension n, hence it is complete and therefore closed.
    have H₁ : ∀s : submodule 𝕜 E, findim 𝕜 s = n → is_closed (s : set E),
    { assume s s_dim,
      rcases exists_is_basis_finite 𝕜 s with ⟨b, b_basis, b_finite⟩,
      letI : fintype b := finite.fintype b_finite,
      have U : uniform_embedding (equiv_fun_basis b_basis).symm.to_equiv,
      { have : fintype.card b = n,
          by { rw ← s_dim, exact (findim_eq_card_basis b_basis).symm },
        have : continuous (equiv_fun_basis b_basis) := IH (subtype.val : b → s) b_basis this,
        exact (equiv_fun_basis b_basis).symm.uniform_embedding (linear_map.continuous_on_pi _) this },
      have : is_complete (s : set E),
        from complete_space_coe_iff_is_complete.1 ((complete_space_congr U).1 (by apply_instance)),
      exact this.is_closed },
    -- second step: any linear form is continuous, as its kernel is closed by the first step
    have H₂ : ∀f : E →ₗ[𝕜] 𝕜, continuous f,
    { assume f,
      have : findim 𝕜 f.ker = n ∨ findim 𝕜 f.ker = n.succ,
      { have Z := f.findim_range_add_findim_ker,
        rw [findim_eq_card_basis hξ, hn] at Z,
        have : findim 𝕜 f.range = 0 ∨ findim 𝕜 f.range = 1,
        { have I : ∀(k : ℕ), k ≤ 1 ↔ k = 0 ∨ k = 1, by omega manual,
          have : findim 𝕜 f.range ≤ findim 𝕜 𝕜 := submodule.findim_le _,
          rwa [findim_of_field, I] at this },
        cases this,
        { rw this at Z,
          right,
          simpa using Z },
        { left,
          rw [this, add_comm, nat.add_one] at Z,
          exact nat.succ.inj Z } },
      have : is_closed (f.ker : set E),
      { cases this,
        { exact H₁ _ this },
        { have : f.ker = ⊤,
            by { apply eq_top_of_findim_eq, rw [findim_eq_card_basis hξ, hn, this] },
          simp [this] } },
      exact linear_map.continuous_iff_is_closed_ker.2 this },
    -- third step: applying the continuity to the linear form corresponding to a coefficient in the
    -- basis decomposition, deduce that all such coefficients are controlled in terms of the norm
    have : ∀i:ι, ∃C, 0 ≤ C ∧ ∀(x:E), ∥equiv_fun_basis hξ x i∥ ≤ C * ∥x∥,
    { assume i,
      let f : E →ₗ[𝕜] 𝕜 := (linear_map.proj i).comp (equiv_fun_basis hξ),
      let f' : E →L[𝕜] 𝕜 := { cont := H₂ f, ..f },
      exact ⟨∥f'∥, norm_nonneg _, λx, continuous_linear_map.le_op_norm f' x⟩ },
    -- fourth step: combine the bound on each coefficient to get a global bound and the continuity
    choose C0 hC0 using this,
    let C := ∑ i, C0 i,
    have C_nonneg : 0 ≤ C := finset.sum_nonneg (λi hi, (hC0 i).1),
    have C0_le : ∀i, C0 i ≤ C :=
      λi, finset.single_le_sum (λj hj, (hC0 j).1) (finset.mem_univ _),
    apply linear_map.continuous_of_bound _ C (λx, _),
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
  rcases exists_is_basis_finite 𝕜 E with ⟨b, b_basis, b_finite⟩,
  letI : fintype b := finite.fintype b_finite,
  have A : continuous (equiv_fun_basis b_basis) :=
    continuous_equiv_fun_basis _ b_basis,
  have B : continuous (f.comp ((equiv_fun_basis b_basis).symm : (b → 𝕜) →ₗ[𝕜] E)) :=
    linear_map.continuous_on_pi _,
  have : continuous ((f.comp ((equiv_fun_basis b_basis).symm : (b → 𝕜) →ₗ[𝕜] E))
                      ∘ (equiv_fun_basis b_basis)) := B.comp A,
  convert this,
  ext x,
  dsimp,
  rw linear_equiv.symm_apply_apply
end

/-- The continuous linear map induced by a linear map on a finite dimensional space -/
def linear_map.to_continuous_linear_map [finite_dimensional 𝕜 E] (f : E →ₗ[𝕜] F') : E →L[𝕜] F' :=
{ cont := f.continuous_of_finite_dimensional, ..f }

/-- The continuous linear equivalence induced by a linear equivalence on a finite dimensional space. -/
def linear_equiv.to_continuous_linear_equiv [finite_dimensional 𝕜 E] (e : E ≃ₗ[𝕜] F) : E ≃L[𝕜] F :=
{ continuous_to_fun := e.to_linear_map.continuous_of_finite_dimensional,
  continuous_inv_fun := begin
    haveI : finite_dimensional 𝕜 F := e.finite_dimensional,
    exact e.symm.to_linear_map.continuous_of_finite_dimensional
  end,
  ..e }

/-- Any finite-dimensional vector space over a complete field is complete.
We do not register this as an instance to avoid an instance loop when trying to prove the
completeness of `𝕜`, and the search for `𝕜` as an unknown metavariable. Declare the instance
explicitly when needed. -/
variables (𝕜 E)
lemma finite_dimensional.complete [finite_dimensional 𝕜 E] : complete_space E :=
begin
  rcases exists_is_basis_finite 𝕜 E with ⟨b, b_basis, b_finite⟩,
  letI : fintype b := finite.fintype b_finite,
  have : uniform_embedding (equiv_fun_basis b_basis).symm :=
    linear_equiv.uniform_embedding _ (linear_map.continuous_of_finite_dimensional _)
    (linear_map.continuous_of_finite_dimensional _),
  change uniform_embedding (equiv_fun_basis b_basis).symm.to_equiv at this,
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

lemma continuous_linear_map.exists_right_inverse_of_surjective [finite_dimensional 𝕜 F]
  (f : E →L[𝕜] F) (hf : f.range = ⊤) :
  ∃ g : F →L[𝕜] E, f.comp g = continuous_linear_map.id 𝕜 F :=
let ⟨g, hg⟩ := (f : E →ₗ[𝕜] F).exists_right_inverse_of_surjective hf in
⟨g.to_continuous_linear_map, continuous_linear_map.ext $ linear_map.ext_iff.1 hg⟩

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
  rcases exists_is_basis_finite 𝕜 E with ⟨b, b_basis, b_finite⟩,
  letI : fintype b := finite.fintype b_finite,
  let e := equiv_fun_basis b_basis,
  let f : E →L[𝕜] (b → 𝕜) :=
    { cont := linear_map.continuous_of_finite_dimensional _, ..e.to_linear_map },
  refine metric.proper_image_of_proper e.symm
    (linear_map.continuous_of_finite_dimensional _) _ (∥f∥)  (λx y, _),
  { exact equiv.range_eq_univ e.symm.to_equiv },
  { have A : e (e.symm x) = x := linear_equiv.apply_symm_apply _ _,
    have B : e (e.symm y) = y := linear_equiv.apply_symm_apply _ _,
    conv_lhs { rw [← A, ← B] },
    change dist (f (e.symm x)) (f (e.symm y)) ≤ ∥f∥ * dist (e.symm x) (e.symm y),
    unfreezingI { exact f.lipschitz.dist_le_mul _ _ } }
end

end proper_field

/- Over the real numbers, we can register the previous statement as an instance as it will not
cause problems in instance resolution since the properness of `ℝ` is already known. -/
instance finite_dimensional.proper_real
  (E : Type u) [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E] : proper_space E :=
finite_dimensional.proper ℝ E

attribute [instance, priority 900] finite_dimensional.proper_real
