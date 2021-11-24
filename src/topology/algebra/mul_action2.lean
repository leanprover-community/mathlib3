/-
Copyright (c) 2021 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import topology.homeomorph
import group_theory.group_action.basic
/-!
# Continuous monoid action

In this file we define class `has_continuous_smul₂`. We say `has_continuous_smul₂ Γ T` if `Γ` acts
on `T` and for each `γ`, the map `x ↦ γ • x` is continuous.

## Main definitions

* `has_continuous_smul₂ Γ T` : typeclass saying that the map `x ↦ γ • x` is continuous on `T`;
* `properly_discontinuous_smul`: says that the scalar multiplication `(•) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ:Γ` move `K` to have nontrivial intersection with `L`.
* `homeomorph.smul`: scalar multiplication by an element of a group `Γ` acting on `T`
  is a homeomorphism of `T`.

## Main results

* `is_open_map_quotient_mk_mul` : The quotient map by a group action is open.
* `is_t2_of_properly_discontinuous_smul_of_t2` : The quotient by a discontinuous group action of
a locally compact t2 space is t2.

## Tags

Hausdorff, discrete group, properly discontinuous, quotient space

-/

local attribute [instance] mul_action.orbit_rel

/-- Class `has_continuous_smul₂ Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of multiplicative
actions, including (semi)modules and algebras.
-/
class has_continuous_smul₂ (Γ : Type*) (T : Type*) [topological_space T] [has_scalar Γ T]
 : Prop :=
(continuous_smul₂ : ∀ γ : Γ, continuous (λ x : T, γ • x))

/-- Class `has_continuous_vadd₂ Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of additive actions,
including (semi)modules and algebras.
-/
class has_continuous_vadd₂ (Γ : Type*) (T : Type*) [topological_space T]
  [has_vadd Γ T] : Prop :=
(continuous_vadd₂ : ∀ γ : Γ, continuous (λ x : T, γ +ᵥ x))

attribute [to_additive has_continuous_vadd₂] has_continuous_smul₂

export has_continuous_smul₂ (continuous_smul₂)

export has_continuous_vadd₂ (continuous_vadd₂)

/-- Class `properly_discontinuous_smul Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ:Γ` move `K` to have nontrivial intersection with `L`.
-/
class properly_discontinuous_smul (Γ : Type*) (T : Type*) [topological_space T]
  [has_scalar Γ T] : Prop :=
(finite_disjoint_inter_image : ∀ {K L : set T}, is_compact K → is_compact L →
  set.finite {γ : Γ | (((•) γ) '' K) ∩ L ≠ ∅ })

/-- Class `properly_discontinuous_vadd Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ:Γ` move `K` to have nontrivial intersection with `L`.
-/
class properly_discontinuous_vadd (Γ : Type*) (T : Type*) [topological_space T]
  [has_vadd Γ T] : Prop :=
(finite_disjoint_inter_image : ∀ {K L : set T}, is_compact K → is_compact L →
  set.finite {γ : Γ | (((+ᵥ) γ) '' K) ∩ L ≠ ∅ })

attribute [to_additive] properly_discontinuous_smul

variables {Γ : Type*} [group Γ] {T : Type*} [topological_space T] [mul_action Γ T]

/-- A finite group action is always properly discontinuous
-/
@[to_additive] instance fintype.properly_discontinuous_smul [fintype Γ] :
  properly_discontinuous_smul Γ T :=
{ finite_disjoint_inter_image := λ _ _ _ _, set.finite.of_fintype _}

export properly_discontinuous_smul (finite_disjoint_inter_image)

export properly_discontinuous_vadd (finite_disjoint_inter_image)

/-- Scalar multiplication by an element of a group `Γ` acting on `T` is a homeomorphism from `T`
to itself. -/
def homeomorph.smul {T : Type*} [topological_space T] {Γ : Type*} [group Γ]
  [mul_action Γ T] [has_continuous_smul₂ Γ T] (γ : Γ) :
  T ≃ₜ T :=
{ to_equiv := mul_action.to_perm_hom Γ T γ,
  continuous_to_fun  := continuous_smul₂ γ,
  continuous_inv_fun := continuous_smul₂ γ⁻¹ }

/-- Affine-addition of an element of an additive group `Γ` acting on `T` is a homeomorphism
from `T` to itself. -/
def homeomorph.vadd {T : Type*} [topological_space T] {Γ : Type*} [add_group Γ]
  [add_action Γ T] [has_continuous_vadd₂ Γ T] (γ : Γ) :
  T ≃ₜ T :=
{ to_equiv := add_action.to_perm_hom T Γ γ,
  continuous_to_fun  := continuous_vadd₂ γ,
  continuous_inv_fun := continuous_vadd₂ (-γ) }

attribute [to_additive homeomorph.vadd] homeomorph.smul

/-- The quotient map by a group action is open.
-/
@[to_additive] lemma is_open_map_quotient_mk_mul [has_continuous_smul₂ Γ T] :
  is_open_map (quotient.mk : T → quotient (mul_action.orbit_rel Γ T)) :=
begin
  intros U hU,
  rw is_open_coinduced,
  let f : T → quotient (mul_action.orbit_rel Γ T) := quotient.mk,
  rw quotient_preimage_image_eq_union_mul U,
  apply is_open_Union,
  intros γ,
  exact (homeomorph.smul γ).is_open_map U hU,
end

/-- The quotient by a discontinuous group action of a locally compact t2 space is t2.
-/
@[to_additive] instance is_t2_of_properly_discontinuous_smul_of_t2 [t2_space T]
  [locally_compact_space T] [has_continuous_smul₂ Γ T] [properly_discontinuous_smul Γ T] :
  t2_space (quotient (mul_action.orbit_rel Γ T)) :=
{ t2 := begin
  let f : T → quotient (mul_action.orbit_rel Γ T) := quotient.mk,
  intros x y hxy,
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ = x := quotient.exists_rep x,
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, f y₀ = y := quotient.exists_rep y,
  have hγx₀y₀ : ∀ γ : Γ, γ • x₀ ≠ y₀,
  { intros γ,
    contrapose! hxy,
    calc x = f(x₀) : hx₀.symm
       ... = f(γ • x₀) : quotient.sound ⟨γ⁻¹, inv_smul_smul γ x₀⟩
       ... = f(y₀) : congr_arg f hxy
       ... = y : hy₀, },
  have hx₀y₀ : x₀ ≠ y₀ := by simpa using (hγx₀y₀ 1),
  obtain ⟨u₀, v₀, open_u₀, open_v₀, x₀_in_u₀, y₀_in_v₀, hu₀v₀⟩ := t2_separation hx₀y₀,
  obtain ⟨K₀, K₀_is_cpt, x₀_in_K₀, K₀_in_u₀⟩ := exists_compact_subset open_u₀ x₀_in_u₀,
  obtain ⟨L₀, L₀_is_cpt, y₀_in_L₀, L₀_in_v₀⟩ := exists_compact_subset open_v₀ y₀_in_v₀,
  let bad_Γ_set := {γ : Γ | (((•) γ) '' K₀) ∩ L₀ ≠ ∅ },
  have bad_Γ_finite : bad_Γ_set.finite := finite_disjoint_inter_image K₀_is_cpt L₀_is_cpt,
  choose uγ vγ is_open_uγ is_open_vγ γx₀_in_uγ y₀_in_vγ uγ_vγ_disjoint using
    λ γ, t2_separation (hγx₀y₀ γ),
  let U₀₀ := ⋂ γ ∈ bad_Γ_set, ((•) γ) ⁻¹' (uγ γ),
  have all_open : ∀ γ, γ ∈ bad_Γ_set → is_open (((•) γ) ⁻¹' (uγ γ)) :=
    λ γ hγ, is_open.preimage (continuous_smul₂ γ) (is_open_uγ γ),
  have U₀₀_is_open : is_open U₀₀ := is_open_bInter bad_Γ_finite all_open,
  let U₀ := U₀₀ ∩ (interior K₀),
  have U₀_is_open : is_open U₀ := is_open.inter U₀₀_is_open is_open_interior,
  let V₀₀ := ⋂ γ ∈ bad_Γ_set, (vγ γ),
  have V₀₀_is_open : is_open V₀₀ := is_open_bInter bad_Γ_finite (λ γ _, is_open_vγ γ),
  let V₀ := V₀₀ ∩ (interior L₀),
  have V₀_is_open : is_open V₀ := is_open.inter V₀₀_is_open is_open_interior,
  let V := f '' V₀,
  let U := f '' U₀,
  have f_is_open_map : is_open_map f := is_open_map_quotient_mk_mul,
  have V_open : is_open V := f_is_open_map _ V₀_is_open,
  have U_open : is_open U := f_is_open_map _ U₀_is_open,
  have x_in_U : x ∈ U,
  { refine ⟨x₀, _, hx₀⟩,
    rw set.mem_inter_iff,
    split,
    { apply set.mem_bInter,
      intros γ hγ,
      exact γx₀_in_uγ γ, },
    exact x₀_in_K₀, },
  have y_in_V : y ∈ V,
  { refine ⟨y₀, _, hy₀⟩,
    rw set.mem_inter_iff,
    split,
    { apply set.mem_bInter,
      intros γ hγ,
      exact y₀_in_vγ γ, },
    exact y₀_in_L₀, },
  have UV_disjoint : U ∩ V = ∅,
  { rw set.eq_empty_iff_forall_not_mem,
    intros z,
    rintros ⟨⟨x₁, x₁_in_U₀, f_x₁_z⟩, ⟨y₁, y₁_in_V₀, f_y₁_z⟩⟩,
    obtain ⟨γ₁, hγ₁⟩ := quotient.exact (f_x₁_z.trans f_y₁_z.symm),
    have hγ₁' : y₁ = γ₁⁻¹ • x₁ := by simp [← hγ₁],
    by_cases hγ₁_bad : γ₁⁻¹ ∈ bad_Γ_set,
    { have y₁_in_vγ₁ : y₁ ∈ vγ γ₁⁻¹,
      { have := set.Inter_subset _ γ₁⁻¹ (y₁_in_V₀.1),
        have := set.Inter_subset _ hγ₁_bad this,
        exact this, },
      have y₁_in_uγ₁ : y₁ ∈ uγ γ₁⁻¹,
      { rw hγ₁',
        have := set.Inter_subset _ γ₁⁻¹ (x₁_in_U₀.1),
        have := set.Inter_subset _ hγ₁_bad this,
        exact this, },
      have : y₁ ∈ uγ γ₁⁻¹ ∩ vγ γ₁⁻¹ := ⟨y₁_in_uγ₁, y₁_in_vγ₁⟩,
      rw (uγ_vγ_disjoint γ₁⁻¹) at this,
      exact this, },
    { have y₁_in_L₀ : y₁ ∈ L₀ := interior_subset y₁_in_V₀.2,
      have x₁_in_K₀ : x₁ ∈ K₀ := interior_subset x₁_in_U₀.2,
      have y₁_in_γ₁K₀ : y₁ ∈ (λ x, γ₁⁻¹ • x) '' K₀,
      { rw hγ₁',
        exact ⟨x₁, ⟨x₁_in_K₀, rfl⟩⟩, },
      have γ₁K₀L₀_disjoint : (λ x, γ₁⁻¹ • x) '' K₀ ∩ L₀ = ∅ := by simpa [bad_Γ_set] using hγ₁_bad,
      have : y₁ ∈ (λ x, γ₁⁻¹ • x) '' K₀ ∩ L₀ := ⟨y₁_in_γ₁K₀, y₁_in_L₀⟩,
      rw (γ₁K₀L₀_disjoint) at this,
      exact this, }, },
  exact ⟨U, V, U_open, V_open, x_in_U, y_in_V, UV_disjoint⟩,
end}
