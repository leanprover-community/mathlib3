/-
Copyright (c) 2022 Sebastian Monnet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Monnet
-/

import field_theory.galois
import topology.algebra.filter_basis
import topology.algebra.open_subgroup
import tactic.by_contra

/-!
# Krull topology

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
finite_dimensional_of_rank_eq_one intermediate_field.rank_bot

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
    exact λ _, H.inv_mem',
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
    change σ (g (σ⁻¹ x)) = x,
    have h_in_F : σ⁻¹ x ∈ F := ⟨x, hx, by {dsimp, rw ← alg_equiv.inv_fun_eq_symm, refl }⟩,
    have h_g_fix : g (σ⁻¹ x) = σ⁻¹ x,
    { rw [subgroup.mem_carrier, intermediate_field.mem_fixing_subgroup_iff F g] at hg,
      exact hg (σ⁻¹ x) h_in_F },
    rw h_g_fix,
    change σ (σ⁻¹ x) = x,
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

open_locale topology filter

/-- Let `L/E/K` be a tower of fields with `E/K` finite. Then `Gal(L/E)` is an open subgroup of
  `L ≃ₐ[K] L`. -/
lemma intermediate_field.fixing_subgroup_is_open {K L : Type*} [field K] [field L] [algebra K L]
  (E : intermediate_field K L) [finite_dimensional K E] :
  is_open (E.fixing_subgroup : set (L ≃ₐ[K] L)) :=
begin
  have h_basis : E.fixing_subgroup.carrier ∈ (gal_group_basis K L) :=
   ⟨E.fixing_subgroup, ⟨E, ‹_›, rfl⟩, rfl⟩,
  have h_nhd := group_filter_basis.mem_nhds_one (gal_group_basis K L) h_basis,
  exact subgroup.is_open_of_mem_nhds _ h_nhd
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
    rw set.disjoint_left,
    rintro σ ⟨w1, hw1, h⟩ ⟨w2, hw2, rfl⟩,
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
    ⟨1, E.fixing_subgroup.one_mem', mul_one σ⟩, _⟩,
  simp only [mem_left_coset_iff, set_like.mem_coe, intermediate_field.mem_fixing_subgroup_iff,
    not_forall],
  exact ⟨x, intermediate_field.mem_adjoin_simple_self K x, hx⟩,
end

end totally_disconnected
