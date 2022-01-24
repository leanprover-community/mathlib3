/-
Copyright (c) 2021 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import topology.homeomorph
import group_theory.group_action.basic
/-!
# Monoid actions continuous in the second variable

In this file we define class `has_continuous_smul₂`. We say `has_continuous_smul₂ Γ T` if `Γ` acts
on `T` and for each `γ`, the map `x ↦ γ • x` is continuous. (This differs from
`has_continuous_smul`, which requires simultaneous continuity in both variables.)

## Main definitions

* `has_continuous_smul₂ Γ T` : typeclass saying that the map `x ↦ γ • x` is continuous on `T`;
* `properly_discontinuous_smul`: says that the scalar multiplication `(•) : Γ → T → T`
  is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely
  many `γ:Γ` move `K` to have nontrivial intersection with `L`.
* `homeomorph.smul`: scalar multiplication by an element of a group `Γ` acting on `T`
  is a homeomorphism of `T`.

## Main results

* `is_open_map_quotient_mk_mul` : The quotient map by a group action is open.
* `t2_space_of_properly_discontinuous_smul_of_t2_space` : The quotient by a discontinuous group
  action of a locally compact t2 space is t2.

## Tags

Hausdorff, discrete group, properly discontinuous, quotient space

-/

open_locale topological_space

open filter set

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
@[priority 100, to_additive] instance fintype.properly_discontinuous_smul [fintype Γ] :
  properly_discontinuous_smul Γ T :=
{ finite_disjoint_inter_image := λ _ _ _ _, set.finite.of_fintype _}

export properly_discontinuous_smul (finite_disjoint_inter_image)

export properly_discontinuous_vadd (finite_disjoint_inter_image)

/-- The homeomorphism given by scalar multiplication by a given element of a group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
def homeomorph.smul {T : Type*} [topological_space T] {Γ : Type*} [group Γ]
  [mul_action Γ T] [has_continuous_smul₂ Γ T] (γ : Γ) :
  T ≃ₜ T :=
{ to_equiv := mul_action.to_perm_hom Γ T γ,
  continuous_to_fun  := continuous_smul₂ γ,
  continuous_inv_fun := continuous_smul₂ γ⁻¹ }

/-- The homeomorphism given by affine-addition by an element of an additive group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
def homeomorph.vadd {T : Type*} [topological_space T] {Γ : Type*} [add_group Γ]
  [add_action Γ T] [has_continuous_vadd₂ Γ T] (γ : Γ) :
  T ≃ₜ T :=
{ to_equiv := add_action.to_perm_hom T Γ γ,
  continuous_to_fun  := continuous_vadd₂ γ,
  continuous_inv_fun := continuous_vadd₂ (-γ) }

attribute [to_additive homeomorph.vadd] homeomorph.smul

/-- The quotient map by a group action is open. -/
@[to_additive]
lemma is_open_map_quotient_mk_mul [has_continuous_smul₂ Γ T] :
  is_open_map (quotient.mk : T → quotient (mul_action.orbit_rel Γ T)) :=
begin
  intros U hU,
  rw [is_open_coinduced, mul_action.quotient_preimage_image_eq_union_mul U],
  exact is_open_Union (λ γ, (homeomorph.smul γ).is_open_map U hU)
end

/-- The quotient by a discontinuous group action of a locally compact t2 space is t2. -/
@[priority 100, to_additive] instance t2_space_of_properly_discontinuous_smul_of_t2_space [t2_space T]
  [locally_compact_space T] [has_continuous_smul₂ Γ T] [properly_discontinuous_smul Γ T] :
  t2_space (quotient (mul_action.orbit_rel Γ T)) :=
begin
  set Q := quotient (mul_action.orbit_rel Γ T),
  rw t2_space_iff_nhds,
  let f : T → Q := quotient.mk,
  have f_op : is_open_map f := is_open_map_quotient_mk_mul,
  rintros ⟨x₀⟩ ⟨y₀⟩ (hxy : f x₀ ≠ f y₀),
  show ∃ (U ∈ 𝓝 (f x₀)) (V ∈ 𝓝 (f y₀)), U ∩ V = ∅,
  have hx₀y₀ : x₀ ≠ y₀ := ne_of_apply_ne _ hxy,
  have hγx₀y₀ : ∀ γ : Γ, γ • x₀ ≠ y₀ := not_exists.mp (mt quotient.sound hxy.symm : _),
  obtain ⟨K₀, L₀, K₀_in, L₀_in, hK₀, hL₀, hK₀L₀⟩ := t2_separation_compact_nhds hx₀y₀,
  let bad_Γ_set := {γ : Γ | (((•) γ) '' K₀) ∩ L₀ ≠ ∅ },
  have bad_Γ_finite : bad_Γ_set.finite := finite_disjoint_inter_image hK₀ hL₀,
  choose u v hu hv u_v_disjoint using λ γ, t2_separation_nhds (hγx₀y₀ γ),
  let U₀₀ := ⋂ γ ∈ bad_Γ_set, ((•) γ) ⁻¹' (u γ),
  let U₀ := U₀₀ ∩ K₀,
  let V₀₀ := ⋂ γ ∈ bad_Γ_set, v γ,
  let V₀ := V₀₀ ∩ L₀,
  have U_nhds : f '' U₀ ∈ 𝓝 (f x₀),
  { apply f_op.image_mem_nhds (inter_mem ((bInter_mem bad_Γ_finite).mpr $ λ γ hγ, _) K₀_in),
    exact (has_continuous_smul₂.continuous_smul₂ γ).continuous_at (hu γ) },
  have V_nhds : f '' V₀ ∈ 𝓝 (f y₀),
    from f_op.image_mem_nhds (inter_mem ((bInter_mem bad_Γ_finite).mpr $ λ γ hγ, hv γ) L₀_in),
  refine ⟨f '' U₀, U_nhds, f '' V₀, V_nhds, _⟩,
  rw mul_action.image_inter_image_iff,
  rintros x ⟨x_in_U₀₀, x_in_K₀⟩ γ,
  by_cases H : γ ∈ bad_Γ_set,
  { rintros ⟨h, -⟩,
    exact eq_empty_iff_forall_not_mem.mp (u_v_disjoint γ) (γ • x)
      ⟨(mem_bInter_iff.mp x_in_U₀₀ γ H : _), mem_bInter_iff.mp h γ H⟩ },
  { rintros ⟨-, h'⟩,
    simp only [image_smul, not_not, mem_set_of_eq, ne.def] at H,
    exact eq_empty_iff_forall_not_mem.mp H (γ • x) ⟨mem_image_of_mem _ x_in_K₀, h'⟩ },
end
