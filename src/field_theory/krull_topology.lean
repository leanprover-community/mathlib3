/-
Copyright (c) 2022 Sebastian Monnet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Monnet
-/

import field_theory.galois
import topology.algebra.filter_basis
import topology.algebra.open_subgroup
import tactic.by_contra
import topology.category.Profinite.default

/-!
# Krull topology

We define the Krull topology on `L ≃ₐ[K] L` for an arbitrary field extension `L/K`. In order to do
this, we first define a `group_filter_basis` on `L ≃ₐ[K] L`, whose sets are `E.fixing_subgroup` for
all intermediate fields `E` with `E/K` finite dimensional.

## Main Definitions

- `finite_exts K L`. Given a field extension `L/K`, this is the set of intermediate fields that are
  finite-dimensional over `K`.

- `fixed_by_finite K L`. Given a field extension `L/K`, `fixed_by_finite K L` is the set of
  subsets `Gal(L/E)` of `Gal(L/K)`, where `E/K` is finite

- `gal_basis K L`. Given a field extension `L/K`, this is the filter basis on `L ≃ₐ[K] L` whose
  sets are `Gal(L/E)` for intermediate fields `E` with `E/K` finite.

- `gal_group_basis K L`. This is the same as `gal_basis K L`, but with the added structure
  that it is a group filter basis on `L ≃ₐ[K] L`, rather than just a filter basis.

- `krull_topology K L`. Given a field extension `L/K`, this is the topology on `L ≃ₐ[K] L`, induced
  by the group filter basis `gal_group_basis K L`.

## Main Results

- `krull_topology_t2 K L`. For an integral field extension `L/K`, the topology `krull_topology K L`
  is Hausdorff.

- `krull_topology_totally_disconnected K L`. For an integral field extension `L/K`, the topology
  `krull_topology K L` is totally disconnected.

## Notations

- In docstrings, we will write `Gal(L/E)` to denote the fixing subgroup of an intermediate field
  `E`. That is, `Gal(L/E)` is the subgroup of `L ≃ₐ[K] L` consisting of automorphisms that fix
  every element of `E`. In particular, we distinguish between `L ≃ₐ[E] L` and `Gal(L/E)`, since the
  former is defined to be a subgroup of `L ≃ₐ[K] L`, while the latter is a group in its own right.

## Implementation Notes

- `krull_topology K L` is defined as an instance for type class inference.
-/

open set ultrafilter
open_locale classical

/-- Mapping intermediate fields along algebra equivalences preserves the partial order -/
lemma intermediate_field.map_mono {K L M : Type*} [field K] [field L] [field M]
  [algebra K L] [algebra K M] {E1 E2 : intermediate_field K L}
  (e : L ≃ₐ[K] M) (h12 : E1 ≤ E2) : E1.map e.to_alg_hom ≤ E2.map e.to_alg_hom :=
set.image_subset e h12

/-- Mapping intermediate fields along the identity does not change them -/
lemma intermediate_field.map_id {K L : Type*} [field K] [field L] [algebra K L]
  (E : intermediate_field K L) :
  E.map (alg_hom.id K L) = E :=
set_like.coe_injective $ set.image_id _

/-- Mapping a finite dimensional intermediate field along an algebra equivalence gives
a finite-dimensional intermediate field. -/
instance im_finite_dimensional {K L : Type*} [field K] [field L] [algebra K L]
  {E : intermediate_field K L} (σ : L ≃ₐ[K] L) [finite_dimensional K E]:
  finite_dimensional K (E.map σ.to_alg_hom) :=
linear_equiv.finite_dimensional (intermediate_field.intermediate_field_map σ E).to_linear_equiv

/-- Given a field extension `L/K`, `finite_exts K L` is the set of
intermediate field extensions `L/E/K` such that `E/K` is finite -/
def finite_exts (K : Type*) [field K] (L : Type*) [field L] [algebra K L] :
  set (intermediate_field K L) :=
{E | finite_dimensional K E}

/-- Given a field extension `L/K`, `fixed_by_finite K L` is the set of
subsets `Gal(L/E)` of `L ≃ₐ[K] L`, where `E/K` is finite -/
def fixed_by_finite (K L : Type*) [field K] [field L] [algebra K L]: set (subgroup (L ≃ₐ[K] L)) :=
intermediate_field.fixing_subgroup '' (finite_exts K L)

/-- For an field extension `L/K`, the intermediate field `K` is finite-dimensional over `K` -/
lemma intermediate_field.finite_dimensional_bot (K L : Type*) [field K]
  [field L] [algebra K L] : finite_dimensional K (⊥ : intermediate_field K L) :=
finite_dimensional_of_dim_eq_one intermediate_field.dim_bot

/-- This lemma says that `Gal(L/K) = L ≃ₐ[K] L` -/
lemma intermediate_field.fixing_subgroup.bot {K L : Type*} [field K]
  [field L] [algebra K L] :
  intermediate_field.fixing_subgroup (⊥ : intermediate_field K L) = ⊤ :=
begin
  ext f,
  refine ⟨λ _, subgroup.mem_top _, λ _, _⟩,
  rintro ⟨x, hx : x ∈ (⊥ : intermediate_field K L)⟩,
  rw intermediate_field.mem_bot at hx,
  rcases hx with ⟨y, rfl⟩,
  exact f.commutes y,
end

/-- If `L/K` is a field extension, then we have `Gal(L/K) ∈ fixed_by_finite K L` -/
lemma top_fixed_by_finite {K L : Type*} [field K] [field L] [algebra K L] :
  ⊤ ∈ fixed_by_finite K L :=
⟨⊥, intermediate_field.finite_dimensional_bot K L, intermediate_field.fixing_subgroup.bot⟩

/-- If `E1` and `E2` are finite-dimensional intermediate fields, then so is their compositum.
This rephrases a result already in mathlib so that it is compatible with our type classes -/
lemma finite_dimensional_sup {K L: Type*} [field K] [field L] [algebra K L]
  (E1 E2 : intermediate_field K L) (h1 : finite_dimensional K E1)
  (h2 : finite_dimensional K E2) : finite_dimensional K ↥(E1 ⊔ E2) :=
by exactI intermediate_field.finite_dimensional_sup E1 E2

/-- An element of `L ≃ₐ[K] L` is in `Gal(L/E)` if and only if it fixes every element of `E`-/
lemma intermediate_field.mem_fixing_subgroup_iff {K L : Type*} [field K] [field L] [algebra K L]
  (E : intermediate_field K L) (σ : (L ≃ₐ[K] L)) :
  σ ∈ E.fixing_subgroup ↔∀ (x : L), x ∈ E → σ x = x :=
⟨λ hσ x hx, hσ ⟨x, hx⟩, λ h ⟨x, hx⟩, h x hx⟩

/-- The map `E ↦ Gal(L/E)` is inclusion-reversing -/
lemma intermediate_field.fixing_subgroup.antimono {K L : Type*} [field K] [field L] [algebra K L]
  {E1 E2 : intermediate_field K L} (h12 : E1 ≤ E2) : E2.fixing_subgroup ≤ E1.fixing_subgroup :=
begin
  rintro σ hσ ⟨x, hx⟩,
  exact hσ ⟨x, h12 hx⟩,
end

/-- Given a field extension `L/K`, `gal_basis K L` is the filter basis on `L ≃ₐ[K] L` whose sets
are `Gal(L/E)` for intermediate fields `E` with `E/K` finite dimensional -/
def gal_basis (K L : Type*) [field K] [field L] [algebra K L] : filter_basis (L ≃ₐ[K] L) :=
{ sets := subgroup.carrier '' (fixed_by_finite K L),
  nonempty := ⟨⊤, ⊤, top_fixed_by_finite, rfl⟩,
  inter_sets :=
  begin
    rintros X Y ⟨H1, ⟨E1, h_E1, rfl⟩, rfl⟩ ⟨H2, ⟨E2, h_E2, rfl⟩, rfl⟩,
    use (intermediate_field.fixing_subgroup (E1 ⊔ E2)).carrier,
    refine ⟨⟨_, ⟨_, finite_dimensional_sup E1 E2 h_E1 h_E2, rfl⟩, rfl⟩, _⟩,
    rw set.subset_inter_iff,
    exact ⟨intermediate_field.fixing_subgroup.antimono le_sup_left,
      intermediate_field.fixing_subgroup.antimono le_sup_right⟩,
  end }

/-- A subset of `L ≃ₐ[K] L` is a member of `gal_basis K L` if and only if it is the underlying set
of `Gal(L/E)` for some finite subextension `E/K`-/
lemma mem_gal_basis_iff (K L : Type*) [field K] [field L] [algebra K L]
  (U : set (L ≃ₐ[K] L)) : U ∈ gal_basis K L ↔ U ∈ subgroup.carrier '' (fixed_by_finite K L) :=
iff.rfl

/-- For a field extension `L/K`, `gal_group_basis K L` is the group filter basis on `L ≃ₐ[K] L`
whose sets are `Gal(L/E)` for finite subextensions `E/K` -/
def gal_group_basis (K L : Type*) [field K] [field L] [algebra K L] :
  group_filter_basis (L ≃ₐ[K] L) :=
{ to_filter_basis := gal_basis K L,
  one' := λ U ⟨H, hH, h2⟩, h2 ▸ H.one_mem,
  mul' := λ U hU, ⟨U, hU, begin
    rcases hU with ⟨H, hH, rfl⟩,
    rintros x ⟨a, b, haH, hbH, rfl⟩,
    exact H.mul_mem haH hbH,
  end⟩,
  inv' := λ U hU, ⟨U, hU, begin
    rcases hU with ⟨H, hH, rfl⟩,
    exact H.inv_mem',
  end⟩,
  conj' :=
  begin
    rintros σ U ⟨H, ⟨E, hE, rfl⟩, rfl⟩,
    let F : intermediate_field K L := E.map (σ.symm.to_alg_hom),
    refine ⟨F.fixing_subgroup.carrier, ⟨⟨F.fixing_subgroup, ⟨F,
      _, rfl⟩, rfl⟩, λ g hg, _⟩⟩,
    { apply im_finite_dimensional σ.symm,
      exact hE },
    change σ * g * σ⁻¹ ∈ E.fixing_subgroup,
    rw intermediate_field.mem_fixing_subgroup_iff,
    intros x hx,
    change σ(g(σ⁻¹ x)) = x,
    have h_in_F : σ⁻¹ x ∈ F := ⟨x, hx, by {dsimp, rw ← alg_equiv.inv_fun_eq_symm, refl }⟩,
    have h_g_fix : g (σ⁻¹ x) = (σ⁻¹ x),
    { rw [subgroup.mem_carrier, intermediate_field.mem_fixing_subgroup_iff F g] at hg,
      exact hg (σ⁻¹ x) h_in_F },
    rw h_g_fix,
    change σ(σ⁻¹ x) = x,
    exact alg_equiv.apply_symm_apply σ x,
  end }

/-- For a field extension `L/K`, `krull_topology K L` is the topological space structure on
`L ≃ₐ[K] L` induced by the group filter basis `gal_group_basis K L` -/
instance krull_topology (K L : Type*) [field K] [field L] [algebra K L] :
  topological_space (L ≃ₐ[K] L) :=
group_filter_basis.topology (gal_group_basis K L)

/-- For a field extension `L/K`, the Krull topology on `L ≃ₐ[K] L` makes it a topological group. -/
instance (K L : Type*) [field K] [field L] [algebra K L] :
  topological_group (L ≃ₐ[K] L) :=
group_filter_basis.is_topological_group (gal_group_basis K L)

section krull_t2

open_locale topological_space filter

/-- Let `L/E/K` be a tower of fields with `E/K` finite. Then `Gal(L/E)` is an open subgroup of
  `L ≃ₐ[K] L`. -/
lemma intermediate_field.fixing_subgroup_is_open {K L : Type*} [field K] [field L] [algebra K L]
  (E : intermediate_field K L) [finite_dimensional K E] :
  is_open (E.fixing_subgroup : set (L ≃ₐ[K] L)) :=
begin
  have h_basis : E.fixing_subgroup.carrier ∈ (gal_group_basis K L) :=
   ⟨E.fixing_subgroup, ⟨E, _inst_4, rfl⟩, rfl⟩,
  have h_nhd := group_filter_basis.mem_nhds_one (gal_group_basis K L) h_basis,
  rw mem_nhds_iff at h_nhd,
  rcases h_nhd with ⟨U, hU_le, hU_open, h1U⟩,
  exact subgroup.is_open_of_one_mem_interior ⟨U, ⟨hU_open, hU_le⟩, h1U⟩,
end

/-- Given a tower of fields `L/E/K`, with `E/K` finite, the subgroup `Gal(L/E) ≤ L ≃ₐ[K] L` is
  closed. -/
lemma intermediate_field.fixing_subgroup_is_closed {K L : Type*} [field K] [field L] [algebra K L]
  (E : intermediate_field K L) [finite_dimensional K E] :
  is_closed (E.fixing_subgroup : set (L ≃ₐ[K] L)) :=
open_subgroup.is_closed ⟨E.fixing_subgroup, E.fixing_subgroup_is_open⟩

/-- If `L/K` is an algebraic extension, then the Krull topology on `L ≃ₐ[K] L` is Hausdorff. -/
lemma krull_topology_t2 {K L : Type*} [field K] [field L] [algebra K L]
  (h_int : algebra.is_integral K L) : t2_space (L ≃ₐ[K] L) :=
{ t2 := λ f g hfg,
  begin
    let φ := f⁻¹ * g,
    cases (fun_like.exists_ne hfg) with x hx,
    have hφx : φ x ≠ x,
    { apply ne_of_apply_ne f,
      change f (f.symm (g x)) ≠ f x,
      rw [alg_equiv.apply_symm_apply f (g x), ne_comm],
      exact hx },
    let E : intermediate_field K L := intermediate_field.adjoin K {x},
    let h_findim : finite_dimensional K E :=
      intermediate_field.adjoin.finite_dimensional (h_int x),
    let H := E.fixing_subgroup,
    have h_basis : (H : set (L ≃ₐ[K] L)) ∈ gal_group_basis K L := ⟨H, ⟨E, ⟨h_findim, rfl⟩⟩, rfl⟩,
    have h_nhd := group_filter_basis.mem_nhds_one (gal_group_basis K L) h_basis,
    rw mem_nhds_iff at h_nhd,
    rcases h_nhd with ⟨W, hWH, hW_open, hW_1⟩,
    refine ⟨left_coset f W, left_coset g W,
      ⟨hW_open.left_coset f, hW_open.left_coset g, ⟨1, hW_1, mul_one _⟩, ⟨1, hW_1, mul_one _⟩, _⟩⟩,
    rintro σ ⟨⟨w1, hw1, h⟩, w2, hw2, hgw2⟩,
    rw ← hgw2 at h,
    rw [eq_inv_mul_iff_mul_eq.symm, ← mul_assoc, mul_inv_eq_iff_eq_mul.symm] at h,
    have h_in_H : w1 * w2⁻¹ ∈ H := H.mul_mem (hWH hw1) (H.inv_mem (hWH hw2)),
    rw h at h_in_H,
    change φ ∈ E.fixing_subgroup at h_in_H,
    rw intermediate_field.mem_fixing_subgroup_iff at h_in_H,
    specialize h_in_H x,
    have hxE : x ∈ E,
    { apply intermediate_field.subset_adjoin,
      apply set.mem_singleton },
    exact hφx (h_in_H hxE),
  end }

end krull_t2

section totally_disconnected

/-- If `L/K` is an algebraic field extension, then the Krull topology on `L ≃ₐ[K] L` is
  totally disconnected. -/
lemma krull_topology_totally_disconnected {K L : Type*} [field K] [field L] [algebra K L]
  (h_int : algebra.is_integral K L) : is_totally_disconnected (set.univ : set (L ≃ₐ[K] L)) :=
begin
  apply is_totally_disconnected_of_clopen_set,
  intros σ τ h_diff,
  have hστ : σ⁻¹ * τ ≠ 1,
  { rwa [ne.def, inv_mul_eq_one] },
  rcases (fun_like.exists_ne hστ) with ⟨x, hx : (σ⁻¹ * τ) x ≠ x⟩,
  let E := intermediate_field.adjoin K ({x} : set L),
  haveI := intermediate_field.adjoin.finite_dimensional (h_int x),
  refine ⟨left_coset σ E.fixing_subgroup,
    ⟨E.fixing_subgroup_is_open.left_coset σ, E.fixing_subgroup_is_closed.left_coset σ⟩,
    ⟨1, E.fixing_subgroup.one_mem', by simp⟩, _⟩,
  simp only [mem_left_coset_iff, set_like.mem_coe, intermediate_field.mem_fixing_subgroup_iff,
    not_forall],
  exact ⟨x, intermediate_field.mem_adjoin_simple_self K x, hx⟩,
end

end totally_disconnected

section compact

variables {K L : Type*} [field K] [field L] [algebra K L] {E F : intermediate_field K L}

/-- Let `E` be an intermediate field of `L/K` with `E/K` finite, and let `f` be an ultrafilter
on `L ≃ₐ[K] L`. Then the restriction map `(L ≃ₐ[K] L) → (E →ₐ[K] L)` pushes `f` forward to an
ultrafilter on `E →ₐ[K] L`. Since `E →ₐ[K] L` is a finite set, this ultrafilter is principal. The
element of `E →ₐ[K] L` generating this principal ultrafilter is `f.alg_hom h_findim`, where
`h_findim : finite_dimensional K E`. -/
protected noncomputable def ultrafilter.generator_of_pushforward
  (f : ultrafilter (L →ₐ[K] L)) {E : Type*} [field E] [algebra K E] [algebra E L]
  [is_scalar_tower K E L] [finite_dimensional K E]: E →ₐ[K] L :=
classical.some $ ultrafilter.eq_pure_of_fintype $
  f.map $ λ σ, σ.comp $ is_scalar_tower.to_alg_hom K E L

/-- Let `f` be an ultrafilter on `L ≃ₐ[K] L`. For an intermediate field `E` of `L/K`, there is a
  natural restriction map `(L ≃ₐ[K] L) → (E →ₐ[K] L)`. Moreover, this restriction map gives
  a pushforward of `f` to an ultrafilter on `E →ₐ[K] L`. If `E/K` is finite, then this pushforward
  is generated by `ultrafilter.alg_hom h_findim f`.  -/
lemma ultrafilter.generator_of_pushforward_spec (f : ultrafilter (L →ₐ[K] L)) {E : Type*} [field E]
  [algebra K E] [algebra E L] [is_scalar_tower K E L] [finite_dimensional K E]:
  f.map (λ σ : L →ₐ[K] L, σ.comp $ is_scalar_tower.to_alg_hom K E L) =
  pure (f.generator_of_pushforward) :=
coe_injective $ classical.some_spec $ ultrafilter.eq_pure_of_fintype _


lemma ultrafilter.generator_of_pushforward_comp_inclusion (f : ultrafilter (L →ₐ[K] L))
  (hE : finite_dimensional K E) (hF : finite_dimensional K F) (hEF : E ≤ F) :
  (f.generator_of_pushforward : F →ₐ[K] L).comp (subalgebra.inclusion hEF) =
  (f.generator_of_pushforward : E →ₐ[K] L) :=
begin
  refine ultrafilter.pure_injective _,
  transitivity map (λ ϕ : ↥F →ₐ[K] L, ϕ.comp $ subalgebra.inclusion hEF)
  (pure $ f.generator_of_pushforward),
  { refl },
  rw [←f.generator_of_pushforward_spec, ←f.generator_of_pushforward_spec],
  refl,
end

/-- For each `x : L`, the intermediate field `K(x)` is finite dimensional over `K`, so
`f.alg_hom` gives a map `ϕₓ : K(x) → L`. We define
`f.glued_generators_of_pushforwards_function h_int` to be the function taking `x`
to `ϕₓ(x)` for all `x : L`. -/
protected noncomputable def ultrafilter.glued_generators_of_pushforwards_function
  (h_int : algebra.is_integral K L) (f : ultrafilter (L →ₐ[K] L)) (x : L) : L :=
let foo : finite_dimensional K (intermediate_field.adjoin K {x}) :=
  intermediate_field.adjoin.finite_dimensional (h_int x) in
by exactI (f.generator_of_pushforward : (intermediate_field.adjoin K {x}) →ₐ[K] L)
  ⟨x, intermediate_field.mem_adjoin_simple_self K x⟩

lemma ultrafilter.glued_generators_of_pushforwards_function_spec (h_int : algebra.is_integral K L)
  (f : ultrafilter (L →ₐ[K] L)) (hE : finite_dimensional K E) {x : L} (hx : x ∈ E) :
  f.glued_generators_of_pushforwards_function h_int x =
  (f.generator_of_pushforward : (E →ₐ[K] L)) ⟨x, hx⟩ :=
begin
  haveI h_findim : finite_dimensional K ((intermediate_field.adjoin K {x}) : intermediate_field K
  L) := intermediate_field.adjoin.finite_dimensional (h_int x),
  have h : f.glued_generators_of_pushforwards_function h_int x = (f.generator_of_pushforward :
  (intermediate_field.adjoin K {x}) →ₐ[K] L) ⟨x, intermediate_field.mem_adjoin_simple_self K x⟩ :=
  rfl,
  rw [h, ←f.generator_of_pushforward_comp_inclusion],
  refl,
  simp [hx],
end

lemma ultrafilter.glued_generators_of_pushforwards_function_spec' (h_int : algebra.is_integral K L)
  (f : ultrafilter (L →ₐ[K] L)) (hE : finite_dimensional K E) (x : E) :
  f.glued_generators_of_pushforwards_function h_int x =
  (f.generator_of_pushforward : (E →ₐ[K] L)) x :=
by rw [f.glued_generators_of_pushforwards_function_spec h_int hE x.prop, subtype.coe_eta]

/-- The function `f.glued_generators_of_pushforwards_function h_int` is actually a `K`-algebra
homomorphism,
  and here we define the corresponding term of `L →ₐ[K] L`.-/
noncomputable def ultrafilter.glued_generators_of_pushforwards_alg_hom
  (f : ultrafilter (L →ₐ[K] L)) (h_int : algebra.is_integral K L) :
  L →ₐ[K] L :=
{ to_fun := ultrafilter.glued_generators_of_pushforwards_function h_int f,
  map_zero' := (f.glued_generators_of_pushforwards_function_spec' _
    (intermediate_field.finite_dimensional_bot K L) (0 : (⊥ : intermediate_field K L))).trans
    (map_zero _),
  map_one' := (f.glued_generators_of_pushforwards_function_spec' _
    (intermediate_field.finite_dimensional_bot K L) (1 : (⊥ : intermediate_field K L))).trans
    (map_one _),
  map_mul' := λ x y,
  begin
    let E := intermediate_field.adjoin K ({x, y} : set L),
    have h_sub := intermediate_field.gc.le_u_l {x, y},
    have hx := h_sub (mem_insert x _),
    have hy := h_sub (mem_insert_of_mem _ $ mem_singleton _),
    haveI hE : finite_dimensional K E := intermediate_field.adjoin.finite_dimensional_of_finite_set
    ((finite_singleton _).insert _) (λ a _, h_int a),
    rw [f.glued_generators_of_pushforwards_function_spec h_int hE hx,
      f.glued_generators_of_pushforwards_function_spec h_int hE hy,
      f.glued_generators_of_pushforwards_function_spec h_int hE (E.mul_mem hx hy)],
    exact map_mul ((f.generator_of_pushforward : ((E : intermediate_field K L) →ₐ[K] L))) ⟨x, hx⟩
    ⟨y, hy⟩,
  end,
  map_add' := λ x y,
  begin
    let E := intermediate_field.adjoin K ({x, y} : set L),
    have h_sub := intermediate_field.gc.le_u_l {x, y},
    have hx := h_sub (mem_insert x _),
    have hy := h_sub (mem_insert_of_mem _ $ mem_singleton _),
    haveI hE : finite_dimensional K E := intermediate_field.adjoin.finite_dimensional_of_finite_set
    ((finite_singleton _).insert _) (λ a _, h_int a),
    rw [f.glued_generators_of_pushforwards_function_spec h_int hE hx,
      f.glued_generators_of_pushforwards_function_spec h_int hE hy,
      f.glued_generators_of_pushforwards_function_spec h_int hE (E.add_mem hx hy)],
    exact map_add (f.generator_of_pushforward : (E : intermediate_field K L) →ₐ[K] L) ⟨x, hx⟩
    ⟨y, hy⟩,
  end,
  commutes' := λ r,
  begin
    rw [f.glued_generators_of_pushforwards_function_spec h_int
      (intermediate_field.finite_dimensional_bot K L)
      (intermediate_field.algebra_map_mem _ r)],
    haveI : finite_dimensional K (⊥ : intermediate_field K L) :=
    intermediate_field.finite_dimensional_bot K L,
    exact (f.generator_of_pushforward : (⊥ : intermediate_field K L) →ₐ[K] L).commutes r,
  end }

lemma ultrafilter.glued_generators_of_pushforwards_alg_hom_injective
  (h_int : algebra.is_integral K L)
  (f : ultrafilter (L →ₐ[K] L)) : function.injective
  (ultrafilter.glued_generators_of_pushforwards_alg_hom f h_int) :=
(ultrafilter.glued_generators_of_pushforwards_alg_hom f h_int).to_ring_hom.injective

lemma eq_of_map_le {f : L →ₐ[K] L} (h_findim : finite_dimensional K E) (h_map_le : E.map f ≤ E) :
  E.map f = E :=
begin
  haveI hE_submod_fin : finite_dimensional K E.to_subalgebra.to_submodule := h_findim,
  have h_finrank_eq : finite_dimensional.finrank K E = finite_dimensional.finrank K (E.map f),
  { exact (E.to_subalgebra.to_submodule.equiv_map_of_injective
      f.to_linear_map f.to_ring_hom.injective).finrank_eq },
  exact intermediate_field.to_subalgebra_eq_iff.mp (subalgebra.to_submodule_injective
    (finite_dimensional.eq_of_le_of_finrank_eq h_map_le h_finrank_eq.symm)),
end

lemma ultrafilter.glued_generators_of_pushforwards_alg_hom_surjective (h_int :
  algebra.is_integral K L) (f : ultrafilter (L →ₐ[K] L)) :
  function.surjective (ultrafilter.glued_generators_of_pushforwards_alg_hom f h_int) :=
begin
  intro y,
  let p := minpoly K y,
  let S := p.root_set L,
  let σ := ultrafilter.glued_generators_of_pushforwards_alg_hom f h_int,
  have hp : p ≠ 0 := (minpoly.monic (h_int y)).ne_zero,
  have hσSS : σ '' S ⊆ S,
  { rintros x ⟨a, ha, rfl⟩,
    rw polynomial.mem_root_set hp at ha,
    rw [polynomial.mem_root_set hp, polynomial.aeval_alg_hom_apply, ha, σ.map_zero] },
  have h3 : σ '' S = S :=
  eq_of_subset_of_card_le hσSS (ge_of_eq (card_image_of_injective S σ.to_ring_hom.injective)),
  have hy : y ∈ σ '' S,
  { rw [h3, polynomial.mem_root_set hp, minpoly.aeval] },
  rcases hy with ⟨a, ha, hay⟩,
  exact ⟨a, hay⟩,
end

lemma ultrafilter.glued_generators_of_pushforwards_alg_hom_bijection
  (h_int : algebra.is_integral K L) (f : ultrafilter (L →ₐ[K] L)) : function.bijective
  (ultrafilter.glued_generators_of_pushforwards_alg_hom f h_int) :=
⟨ultrafilter.glued_generators_of_pushforwards_alg_hom_injective h_int f,
  ultrafilter.glued_generators_of_pushforwards_alg_hom_surjective h_int f⟩

/-- Since `ultrafilter.glued_generators_of_pushforwards_alg_hom h_int f` is a bijective `K`-algebra
  homomorphism `L →ₐ[K] L`,it is a `K`-algebra equivalence. Here we define the corresponding term
  of `L ≃ₐ[K] L`. -/
noncomputable def ultrafilter.glued_generators_of_pushforwards_alg_equiv (h_int :
  algebra.is_integral K L) (f : ultrafilter (L →ₐ[K] L)) : (L ≃ₐ[K] L) :=
alg_equiv.of_bijective (ultrafilter.glued_generators_of_pushforwards_alg_hom f h_int)
  (ultrafilter.glued_generators_of_pushforwards_alg_hom_bijection h_int f)

/-- Let `L/K` be a normal algebraic field extension, let `f` be an ultrafilter on
  `L ≃ₐ[K] L`, and let `E/K` be a finite subextension. Then
  `ultrafilter.glued_generators_of_pushforwards_alg_equiv h_int f`
  is a term of `L ≃ₐ[K] L`, and `alg_hom_of_finite_dimensional_of_ultrafilter h_findim f` is a term
  `E →ₐ[K] L`. This Lemma tells us that the underlying maps of these two terms agree on `E`.
    -/
lemma equiv_restricts_to_alg_hom_of_finite_dimensional (h_int : algebra.is_integral K L)
  (f : ultrafilter (L →ₐ[K] L)) {E : intermediate_field K L} [finite_dimensional K E] :
  ((ultrafilter.glued_generators_of_pushforwards_alg_equiv h_int f).to_alg_hom.comp E.val) =
  (f.generator_of_pushforward : E →ₐ[K] L) :=
alg_hom.ext (ultrafilter.glued_generators_of_pushforwards_function_spec' h_int f _)

open_locale topological_space

lemma ultrafilter_converges_to_glued_equiv (h_int : algebra.is_integral K L)
  (f : ultrafilter (L ≃ₐ[K] L)) : (f : filter (L ≃ₐ[K] L)) ≤
  𝓝 (ultrafilter.glued_generators_of_pushforwards_alg_equiv h_int
  (f.map (λ (σ : L ≃ₐ[K] L), σ.to_alg_hom))) :=
begin
  let σ := ultrafilter.glued_generators_of_pushforwards_alg_equiv h_int (f.map (λ (e : L ≃ₐ[K] L),
  e.to_alg_hom)),
  rw [←map_mul_left_nhds_one, group_filter_basis.nhds_one_eq],
  apply filter.le_map,
  rintros S ⟨-, ⟨-, ⟨E, hE, rfl⟩, rfl⟩, hS⟩,
  refine filter.mem_of_superset _ (set.image_subset _ hS),
  let p : (L ≃ₐ[K] L) → (E →ₐ[K] L) := (λ σ : L →ₐ[K] L, σ.comp E.val) ∘ alg_equiv.to_alg_hom,
  have h_preim : p⁻¹' {p σ} = has_mul.mul σ '' E.fixing_subgroup.carrier,
  { refine set.ext (λ g, (fun_like.ext_iff.trans _).trans (mem_left_coset_iff σ).symm),
    exact forall_congr (λ x, σ.to_equiv.symm_apply_eq.symm) },
  rw [←h_preim, mem_coe, ←mem_map, ←map_map],
  have asdf : (E.val : E →ₐ[K] L) = is_scalar_tower.to_alg_hom K E L := rfl,
  rw asdf,
  rw (f.map (λ σ : L ≃ₐ[K] L, σ.to_alg_hom)).generator_of_pushforward_spec,
  rw [mem_pure, mem_singleton_iff, ←equiv_restricts_to_alg_hom_of_finite_dimensional],
  exact hE,
end

lemma krull_topology_compact (h_int : algebra.is_integral K L) :
  is_compact (set.univ : set (L ≃ₐ[K] L)) :=
is_compact_iff_ultrafilter_le_nhds.2 (λ f _,
  ⟨ultrafilter.glued_generators_of_pushforwards_alg_equiv h_int (f.map alg_equiv.to_alg_hom),
  set.mem_univ _, ultrafilter_converges_to_glued_equiv h_int f⟩)

end compact

variables {K L : Type*} [field K] [field L] [algebra K L]

/-- The Krull topology on `L ≃ₐ[K] L` is compact and Hausdorff whenever `L/K` is an
  algebraic extension -/
def krull_topology_comphaus (h_int : algebra.is_integral K L) : CompHaus :=
{ to_Top := Top.of (L ≃ₐ[K] L),
  is_compact := { compact_univ := krull_topology_compact h_int },
  is_hausdorff := krull_topology_t2 h_int }

/-- The Krull topology on `L ≃ₐ[K] L` is totally disconnected whenever `L/K` is a normal
  extension -/
lemma krull_topology_totally_disconnected_space (h_int : algebra.is_integral K L) :
  totally_disconnected_space (L ≃ₐ[K] L) :=
{ is_totally_disconnected_univ := krull_topology_totally_disconnected h_int }

/-- The Krull topology on `L ≃ₐ[K] L` is profinite whenever `L/K` is an algebraic extension -/
def krull_topology_profinite (h_int : algebra.is_integral K L) : Profinite :=
{ to_CompHaus := krull_topology_comphaus h_int,
  is_totally_disconnected := krull_topology_totally_disconnected_space h_int }
