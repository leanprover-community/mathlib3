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
lemma mem_fixing_subgroup_iff {K L : Type*} [field K] [field L] [algebra K L]
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
    rw mem_fixing_subgroup_iff,
    intros x hx,
    change σ(g(σ⁻¹ x)) = x,
    have h_in_F : σ⁻¹ x ∈ F := ⟨x, hx, by {dsimp, rw ← alg_equiv.inv_fun_eq_symm, refl }⟩,
    have h_g_fix : g (σ⁻¹ x) = (σ⁻¹ x),
    { rw [subgroup.mem_carrier, mem_fixing_subgroup_iff F g] at hg,
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
    by_contra h_nonempty,
    change left_coset f W ∩ left_coset g W ≠ ∅ at h_nonempty,
    rw set.ne_empty_iff_nonempty at h_nonempty,
    rcases h_nonempty with ⟨σ, ⟨⟨w1, hw1, hfw1⟩, ⟨w2, hw2, hgw2⟩⟩⟩,
    rw ← hgw2 at hfw1,
    rename hfw1 h,
    rw [eq_inv_mul_iff_mul_eq.symm, ← mul_assoc, mul_inv_eq_iff_eq_mul.symm] at h,
    have h_in_H : w1 * w2⁻¹ ∈ H := H.mul_mem (hWH hw1) (H.inv_mem (hWH hw2)),
    rw h at h_in_H,
    change φ ∈ E.fixing_subgroup at h_in_H,
    rw mem_fixing_subgroup_iff at h_in_H,
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
  simp only [mem_left_coset_iff, set_like.mem_coe, mem_fixing_subgroup_iff, not_forall],
  exact ⟨x, intermediate_field.mem_adjoin_simple_self K x, hx⟩,
end

end totally_disconnected


section finite_stuff

variables {K E L : Type*} [field K] [field E] [algebra K E] [field L] [algebra K L]
  [finite_dimensional K E]

noncomputable instance foo {E : Type*} {X : set E} (hX : X.finite) {L : Type*}
  (F : E → multiset L) : fintype (Π x : X, {l : L // l ∈ F x}) :=
by { classical, letI : fintype X := set.finite.fintype hX, exact pi.fintype}

variable (K)

/-- Function taking `e ∈ E` to the multiset of roots of its minimal polynomial in `L` -/
noncomputable def aux_fun1 : E → multiset L :=
λ e, ((minpoly K e).map (algebra_map K L)).roots

lemma minpoly.ne_zero' (e : E) : minpoly K e ≠ 0 :=
minpoly.ne_zero $ is_integral_of_noetherian (is_noetherian.iff_fg.2 infer_instance) _

variable (E)

def basis_set: set E :=
set.range (finite_dimensional.fin_basis K E : _ → E)

variable (L)

/-- Function from Hom_K(E,L) to pi type Π (x : basis), roots of min poly of x -/
def aux_fun2 (φ : E →ₐ[K] L) (x : basis_set K E) :
  {l : L // l ∈ (aux_fun1 K x.1 : multiset L)} :=
⟨φ x, begin
  unfold aux_fun1,
  rw [polynomial.mem_roots_map (minpoly.ne_zero' K x.val),
    ← polynomial.alg_hom_eval₂_algebra_map, ← φ.map_zero],
  exact congr_arg φ (minpoly.aeval K (x : E)),
end⟩

lemma aux_inj : function.injective (aux_fun2 K E L) :=
begin
  intros f g h,
  suffices : (f : E →ₗ[K] L) = g,
  { rw linear_map.ext_iff at this,
    ext x, exact this x },
  rw function.funext_iff at h,
  apply linear_map.ext_on (finite_dimensional.fin_basis K E).span_eq,
  rintro e he,
  have := (h ⟨e, he⟩),
  apply_fun subtype.val at this,
  exact this,
end

/-- Given field extensions `E/K` and `L/K`, with `E/K` finite, there are finitely many `K`-algebra
  homomorphisms `E →ₐ[K] L`. -/
noncomputable def alg_homs_finite : fintype (E →ₐ[K] L) :=
let n := finite_dimensional.finrank K E in
begin
  let B : basis (fin n) K E := finite_dimensional.fin_basis K E,
  let X := set.range (B : fin n → E),
  have hX : X.finite := set.finite_range ⇑B,
  refine @fintype.of_injective _ _
    (foo hX (λ e, ((minpoly K e).map (algebra_map K L)).roots)) _ (aux_inj K E L),
end

end finite_stuff

open set

lemma ultrafilter.eq_principal_of_fintype (X : Type*) [fintype X]
  (f : ultrafilter X) : ∃ x : X, (f : filter X) = pure x :=
let ⟨x, hx1, (hx2 : (f : filter X) = pure x)⟩ :=
  ultrafilter.eq_principal_of_finite_mem (finite_univ : (univ : set X).finite)
  (filter.univ_mem) in
⟨x, hx2⟩

universe u

/-- Let `E` be an intermediate field of `L/K` with `E/K` finite, and let `f` be an ultrafilter
  on `L ≃ₐ[K] L`. Then the restriction map `(L ≃ₐ[K] L) → (E →ₐ[K] L)` gives pushes `f` forward
  to an ultrafilter on `E →ₐ[K] L`. Since `E →ₐ[K] L` is a finite set, this ultrafilter is
  principal. The element of `E →ₐ[K] L` generating this principal ultrafilter is
  `alg_hom_of_finite_dimensional_of_ultrafilter h_findim f`, where
  `h_findim : finite_dimensional K E`. -/
noncomputable def alg_hom_of_finite_dimensional_of_ultrafilter
  {K : Type*} {L : Type u} [field K] [field L] [algebra K L]
  {E : intermediate_field K L} (h_findim : finite_dimensional K E)
  (f : ultrafilter (L ≃ₐ[K] L)) : E →ₐ[K] L := classical.some (@ultrafilter.eq_principal_of_fintype
  (E →ₐ[K] L) (alg_homs_finite K E L) (f.map (λ σ, σ.to_alg_hom.comp (intermediate_field.val E))))

/-- Let `f` be an ultrafilter on `L ≃ₐ[K] L`. For an intermediate field `E` of `L/K`, there is a
  natural restriction map `res : (L ≃ₐ[K] L) → (E →ₐ[K] L)`. Moreover, this restriction map gives
  a pushforward of `f` to an ultrafilter on `E →ₐ[K] L`. If `E/K` is finite, then this pushforward
  is generated by `alg_hom_of_finite_dimensional_of_ultrafilter_spec h_findim f`.  -/
lemma alg_hom_of_finite_dimensional_of_ultrafilter_spec {K L : Type*} [field K] [field L]
  [algebra K L] {E : intermediate_field K L} (h_findim : finite_dimensional K E)
  (f : ultrafilter (L ≃ₐ[K] L)) : (f.map (λ σ : L ≃ₐ[K] L, σ.to_alg_hom.comp
  (intermediate_field.val E)) : filter (E →ₐ[K] L)) =
  pure (alg_hom_of_finite_dimensional_of_ultrafilter h_findim f) := classical.some_spec
  (@ultrafilter.eq_principal_of_fintype (E →ₐ[K] L) (alg_homs_finite K E L)
  (f.map (λ σ, σ.to_alg_hom.comp (intermediate_field.val E))))

lemma ultrafilter.map_map {X Y Z: Type*} (m : X → Y) (n : Y → Z) (f : ultrafilter X) :
(f.map m).map n = f.map(n ∘ m) :=
begin
  ext,
  split,
  { intro hs,
    rw [ultrafilter.mem_map, set.preimage_comp, ← ultrafilter.mem_map, ← ultrafilter.mem_map],
    exact hs },
  { intro hs,
    rw [ultrafilter.mem_map, ultrafilter.mem_map, ← set.preimage_comp, ← ultrafilter.mem_map],
    exact hs },
end

lemma ultrafilter.map_pure {X Y : Type*} (x : X) (m : X → Y):
(pure x : ultrafilter X).map m = pure (m x) := rfl

lemma alg_hom_of_finite_dimensional_of_ultrafilter_functor {K L : Type*} [field K] [field L]
  [algebra K L] {E : intermediate_field K L} (hE : finite_dimensional K E)
  (f : ultrafilter (L ≃ₐ[K] L)) {F : intermediate_field K L} (hF : finite_dimensional K F)
  (hEF : E ≤ F) : alg_hom_of_finite_dimensional_of_ultrafilter hE f =
  (alg_hom_of_finite_dimensional_of_ultrafilter hF f).comp (subalgebra.inclusion hEF) :=
  begin
    set p_E :=  (λ σ : L ≃ₐ[K] L, σ.to_alg_hom.comp (intermediate_field.val E)) with p_E_def,
    set p_F :=  (λ σ : L ≃ₐ[K] L, σ.to_alg_hom.comp (intermediate_field.val F)) with p_F_def,
    set σ_E := alg_hom_of_finite_dimensional_of_ultrafilter hE f with σ_E_def,
    set σ_F := alg_hom_of_finite_dimensional_of_ultrafilter hF f with σ_F_def,
    have hσ_E := alg_hom_of_finite_dimensional_of_ultrafilter_spec hE f,
    rw [← p_E_def, ← σ_E_def] at hσ_E,
    have hσ_F := alg_hom_of_finite_dimensional_of_ultrafilter_spec hF f,
    rw [← p_F_def, ← σ_F_def] at hσ_F,
    set res : (F →ₐ[K] L) → (E →ₐ[K] L) := (λ ϕ, ϕ.comp (subalgebra.inclusion hEF))
    with res_def,
    have h_pF_pE_res : res ∘ p_F = p_E := rfl,
    have h_maps_commute : ((f.map p_F).map res : filter (E →ₐ[K] L)) = f.map p_E,
    { rw [ultrafilter.map_map, h_pF_pE_res] },
    have hEf  := alg_hom_of_finite_dimensional_of_ultrafilter_spec hE f,
    rw [← σ_E_def, ← p_E_def] at hEf,
    have hFf := alg_hom_of_finite_dimensional_of_ultrafilter_spec hF f,
    rw [← σ_F_def, ← p_F_def] at hFf,
    have hFf' : (ultrafilter.map p_F f) = (pure σ_F : ultrafilter (F →ₐ[K] L)),
    { exact ultrafilter.coe_inj.mp hFf },
    rw [hEf, hFf', ultrafilter.map_pure] at h_maps_commute,
    have h := filter.pure_injective h_maps_commute,
    rw res_def at h,
    dsimp at h,
    exact h.symm,
  end

/-- For each `x : L`, the intermediate field `K(x)` is finite dimensional over `K`, so
  `alg_hom_of_finite_dimensional_of_ultrafilter` gives a map `ϕₓ : K(x) → L`. We define
  `function_of_ultrafilter h_int f` to be the function taking `x` to `ϕₓ(x)` for all `x : L`. -/
noncomputable def function_of_ultrafilter {K L : Type*} [field K] [field L] [algebra K L]
(h_int : algebra.is_integral K L) (f : ultrafilter (L ≃ₐ[K] L)) :
(L → L) :=
λ x, (alg_hom_of_finite_dimensional_of_ultrafilter
(intermediate_field.adjoin.finite_dimensional (h_int x)) f)
(⟨x, intermediate_field.mem_adjoin_simple_self K x⟩)

lemma function_of_ultrafilter_spec {K L : Type*} [field K] [field L] [algebra K L]
(h_int : algebra.is_integral K L) (f : ultrafilter (L ≃ₐ[K] L)) {E : intermediate_field K L}
(hE : finite_dimensional K E) (x : E) :
(function_of_ultrafilter h_int f) x = (alg_hom_of_finite_dimensional_of_ultrafilter hE f) x :=
begin
   have h_le : intermediate_field.adjoin K {(x : L)} ≤ E,
   { apply intermediate_field.gc.l_le,
     simp only [set_like.coe_mem, set_like.mem_coe, set.singleton_subset_iff, set.le_eq_subset] },
   have h_Kx : finite_dimensional K (intermediate_field.adjoin K {(x : L)}) :=
   intermediate_field.adjoin.finite_dimensional (h_int x),
   let h_functor := alg_hom_of_finite_dimensional_of_ultrafilter_functor h_Kx f hE h_le,
   have h : (function_of_ultrafilter h_int f) x =
   (alg_hom_of_finite_dimensional_of_ultrafilter h_Kx f) ⟨x,
   intermediate_field.mem_adjoin_simple_self K x⟩ := rfl,
   rw [h, h_functor],
   let x_in_Kx : intermediate_field.adjoin K {(x : L)} := ⟨(x : L),
   intermediate_field.mem_adjoin_simple_self K (x : L)⟩,
   have h_inclusion_mk : (subalgebra.inclusion h_le) ⟨x, intermediate_field.mem_adjoin_simple_self K
   (x : L)⟩ = ⟨x, h_le (intermediate_field.mem_adjoin_simple_self K (x : L))⟩ := rfl,
   simp [h_inclusion_mk],
end

lemma adj_finset_finite_dimensional {K L : Type*} [field K] [field L] [algebra K L]
(S : finset L)
(h_int : ∀ (x : L), x ∈ S → is_integral K x) :
finite_dimensional K (intermediate_field.adjoin K (coe S : set L)) :=
begin
  refine intermediate_field.induction_on_adjoin_finset (S) (λ (E : intermediate_field K L),
  finite_dimensional K E) _ _,
  { have temp : (⊥ : intermediate_field K L) = (⊥ : intermediate_field K L) := rfl,
    rw ← intermediate_field.finrank_eq_one_iff at temp,
    refine finite_dimensional.finite_dimensional_of_finrank _,
    rw temp,
    exact zero_lt_one },
  { intros E x hx,
    specialize h_int x hx,
    introI h,
    haveI h2 : finite_dimensional ↥E (↥E)⟮x⟯,
    { apply intermediate_field.adjoin.finite_dimensional,
      exact is_integral_of_is_scalar_tower x h_int },
    change finite_dimensional K ↥(↥E)⟮x⟯,
    exact finite_dimensional.trans K ↥E ↥(↥E)⟮x⟯ },
end

/-- The function `function_of_ultrafilter h_int f` is actually a `K`-algebra homomorphism,
  and here we define the corresponding term of `L →ₐ[K] L`.-/
noncomputable def alg_hom_of_ultrafilter {K L : Type*} [field K] [field L] [algebra K L]
(h_int : algebra.is_integral K L) (f : ultrafilter (L ≃ₐ[K] L)) :
(L →ₐ[K] L) :=
{ to_fun := function_of_ultrafilter h_int f,
  map_one' :=
  begin
    have h_findim_bot : finite_dimensional K (⊥ : intermediate_field K L) :=
    intermediate_field.finite_dimensional_bot K L,
    have h_one_bot : (1 : L) ∈ (⊥: intermediate_field K L) := (⊥ : intermediate_field K L).one_mem,
    have h := function_of_ultrafilter_spec h_int f h_findim_bot (1 : (⊥ : intermediate_field K L)),
    simp at h,
    exact h,
  end,
  map_mul' :=
  begin
    intros x y,
    let E := intermediate_field.adjoin K ({x, y} : set L),
    have h_sub : {x, y} ⊆ E.carrier := intermediate_field.gc.le_u_l {x, y},
    have hxE : x ∈ E := h_sub (mem_insert x {y}),
    have hyE : y ∈ E,
    { apply h_sub,
      simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
    have hxyE : x * y ∈ E := E.mul_mem' hxE hyE,
    haveI : decidable_eq L := classical.dec_eq L,
    let S := ({x, y} : finset L),
    have h_S_int : ∀ (x : L), x ∈ S → is_integral K x :=
    λ a ha, h_int a,
    have hE := adj_finset_finite_dimensional S h_S_int,
    have h_S_coes : (S : set L) = {x, y},
    { simp only [finset.coe_insert, finset.coe_singleton, eq_self_iff_true] },
    rw h_S_coes at hE,
    change finite_dimensional K E at hE,
    have h : function_of_ultrafilter h_int f x = function_of_ultrafilter h_int f (⟨x, hxE⟩ : E) :=
    rfl,
    change function_of_ultrafilter h_int f (⟨x * y, hxyE⟩ : E) =
    function_of_ultrafilter h_int f (⟨x, hxE⟩ : E) *
    function_of_ultrafilter h_int f (⟨y, hyE⟩ : E),
    rw [function_of_ultrafilter_spec h_int f hE ⟨x, hxE⟩,
    function_of_ultrafilter_spec h_int f hE ⟨y, hyE⟩,
    function_of_ultrafilter_spec h_int f hE ⟨x * y, hxyE⟩],
    have h2 : (alg_hom_of_finite_dimensional_of_ultrafilter hE f) ⟨x, hxE⟩ *
  (alg_hom_of_finite_dimensional_of_ultrafilter hE f) ⟨y, hyE⟩ =
  (alg_hom_of_finite_dimensional_of_ultrafilter hE f) (⟨x, hxE⟩ * ⟨y, hyE⟩),
    { simp only [mul_eq_mul_left_iff, true_or, eq_self_iff_true, map_mul] },
    rw h2,
    refl,
  end,
  map_zero' :=
  begin
    have h_findim_bot : finite_dimensional K (⊥ : intermediate_field K L) :=
    intermediate_field.finite_dimensional_bot K L,
    have h_zero_bot : (0 : L) ∈ (⊥: intermediate_field K L) :=
    (⊥ : intermediate_field K L).zero_mem,
    have h := function_of_ultrafilter_spec h_int f h_findim_bot (0 : (⊥ : intermediate_field K L)),
    simp at h,
    exact h,
  end,
  map_add' :=
  begin
    intros x y,
    let E := intermediate_field.adjoin K ({x, y} : set L),
    have h_sub : {x, y} ⊆ E.carrier := intermediate_field.gc.le_u_l {x, y},
    have hxE : x ∈ E := h_sub (mem_insert x {y}),
    have hyE : y ∈ E,
    { apply h_sub,
      simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
    have hxyE : x + y ∈ E := E.add_mem' hxE hyE,
    haveI : decidable_eq L := classical.dec_eq L,
    let S := ({x, y} : finset L),
    have h_S_int : ∀ (x : L), x ∈ S → is_integral K x :=
    λ a ha, h_int a,
    have hE := adj_finset_finite_dimensional S h_S_int,
    have h_S_coes : (S : set L) = {x, y},
    { simp only [finset.coe_insert, finset.coe_singleton, eq_self_iff_true] },
    rw h_S_coes at hE,
    change finite_dimensional K E at hE,
    have h : function_of_ultrafilter h_int f x = function_of_ultrafilter h_int f (⟨x, hxE⟩ : E) :=
    rfl,
    change function_of_ultrafilter h_int f (⟨x + y, hxyE⟩ : E) =
    function_of_ultrafilter h_int f (⟨x, hxE⟩ : E) +
    function_of_ultrafilter h_int f (⟨y, hyE⟩ : E),
    rw [function_of_ultrafilter_spec h_int f hE ⟨x, hxE⟩,
    function_of_ultrafilter_spec h_int f hE ⟨y, hyE⟩,
    function_of_ultrafilter_spec h_int f hE ⟨x + y, hxyE⟩],
    have h2 : (alg_hom_of_finite_dimensional_of_ultrafilter hE f) ⟨x, hxE⟩ +
  (alg_hom_of_finite_dimensional_of_ultrafilter hE f) ⟨y, hyE⟩ =
  (alg_hom_of_finite_dimensional_of_ultrafilter hE f) (⟨x, hxE⟩ + ⟨y, hyE⟩),
    { simp },
    rw h2,
    refl,
  end,
  commutes' :=
  begin
    intro r,
    let r' := (algebra_map K L) r,
    have h_findim_bot : finite_dimensional K (⊥ : intermediate_field K L) :=
    intermediate_field.finite_dimensional_bot K L,
    have h : r' ∈ (⊥ : intermediate_field K L) := (⊥ : intermediate_field K L).algebra_map_mem r,
    change function_of_ultrafilter h_int f (⟨r', h⟩ : (⊥ : intermediate_field K L)) =
    (⟨r', h⟩ : (⊥ : intermediate_field K L)),
    rw function_of_ultrafilter_spec h_int f h_findim_bot (⟨r', h⟩ : (⊥ : intermediate_field K L)),
    have h2 : (⟨r', h⟩ : (⊥ : intermediate_field K L)) = (algebra_map K (⊥ : intermediate_field K L)
    r) := rfl,
    rw h2,
    simp,
    refl,
  end }

lemma alg_hom_of_ultrafilter_injective {K L : Type*} [field K] [field L] [algebra K L]
(h_int : algebra.is_integral K L) (f : ultrafilter (L ≃ₐ[K] L)) :
function.injective (alg_hom_of_ultrafilter h_int f) :=
begin
  intros x y hxy,
  haveI : decidable_eq L := classical.dec_eq L,
  let E := intermediate_field.adjoin K ({x, y} : set L),
  let S := ({x, y} : finset L),
  have h_S_int : ∀ (x : L), x ∈ S → is_integral K x :=
  λ a ha, h_int a,
  have hE := adj_finset_finite_dimensional S h_S_int,
  have h_S_coes : (S : set L) = {x, y},
  { simp only [finset.coe_insert, finset.coe_singleton, eq_self_iff_true] },
  rw h_S_coes at hE,
  change finite_dimensional K E at hE,
  have h_sub : {x, y} ⊆ E.carrier := intermediate_field.gc.le_u_l {x, y},
  have hxE : x ∈ E := h_sub (mem_insert x {y}),
  have hyE : y ∈ E,
  { apply h_sub,
    simp only [set.mem_insert_iff, set.mem_singleton, or_true] },
  change (alg_hom_of_ultrafilter h_int f) (⟨x, hxE⟩ : E) =
  (alg_hom_of_ultrafilter h_int f) (⟨y, hyE⟩ : E) at hxy,
  change (function_of_ultrafilter h_int f) (⟨x, hxE⟩ : E) =
  (function_of_ultrafilter h_int f) (⟨y, hyE⟩ : E) at hxy,
  rw [function_of_ultrafilter_spec h_int f hE (⟨x, hxE⟩ : E),
  function_of_ultrafilter_spec h_int f hE (⟨y, hyE⟩ : E)] at hxy,
  have h : (⟨x, hxE⟩ : E) = (⟨y, hyE⟩ : E),
  { exact ring_hom.injective (alg_hom_of_finite_dimensional_of_ultrafilter hE f).to_ring_hom hxy },
  simp at h,
  exact h,
end

lemma eq_of_map_le {K L : Type*} [field K] [field L] [algebra K L] {E : intermediate_field K L}
{f : L →ₐ[K] L} (h_findim : finite_dimensional K E) (h_map_le : E.map f ≤ E) :
E.map f = E :=
begin
  have hf_inj : function.injective f := ring_hom.injective f.to_ring_hom,
  haveI hE_submod_fin : finite_dimensional K E.to_subalgebra.to_submodule,
  { exact h_findim },
  have h_finrank_eq : finite_dimensional.finrank K (E.map f) =
  finite_dimensional.finrank K E,
  { exact (linear_equiv.finrank_eq (submodule.equiv_map_of_injective (f.to_linear_map)
    hf_inj E.to_subalgebra.to_submodule)).symm },
  have h_submod_le : (E.map f).to_subalgebra.to_submodule ≤ E.to_subalgebra.to_submodule :=
  h_map_le,
  exact intermediate_field.to_subalgebra_eq_iff.mp (subalgebra.to_submodule_injective
  (finite_dimensional.eq_of_le_of_finrank_eq h_map_le h_finrank_eq)),
end

lemma alg_hom_of_ultrafilter_surjective {K L : Type*} [field K] [field L] [algebra K L]
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L)
(minpoly K x)) (f : ultrafilter (L ≃ₐ[K] L)) :
function.surjective (alg_hom_of_ultrafilter h_int f) :=
begin
  intro y,
  specialize h_splits y,
  let p := minpoly K y,
  haveI : decidable_eq L := classical.dec_eq L,
  let S := (p.map (algebra_map K L)).roots.to_finset,
  let E := intermediate_field.adjoin K (S : set L),
  have hE_findim : finite_dimensional K E := adj_finset_finite_dimensional S (λ x hx, h_int x),
  let σ := alg_hom_of_ultrafilter h_int f,
  have hσSS : σ '' S ⊆ S,
  { rintros x ⟨a, ha, hax⟩,
    rw ← hax,
    simp,
    rw polynomial.mem_roots,
    { rw [polynomial.is_root.def, ← polynomial.eval₂_eq_eval_map,
    ← polynomial.alg_hom_eval₂_algebra_map],
      have hσ0 : σ 0 = 0 := by simp,
      rw ← hσ0,
      apply congr_arg σ,
      simp at ha,
      rw polynomial.mem_roots at ha,
      { rw [polynomial.is_root.def, ← polynomial.eval₂_eq_eval_map] at ha,
        exact ha },
      { exact polynomial.map_monic_ne_zero (minpoly.monic (h_int y)) } },
    exact polynomial.map_monic_ne_zero (minpoly.monic (h_int y)) },
  have hSE : (S : set L) ⊆ E := intermediate_field.gc.le_u_l (S : set L),
  have hσSE : σ '' S ⊆ E := set.subset.trans hσSS hSE,
  have h1 : E.map σ = intermediate_field.adjoin K (σ '' S) := intermediate_field.adjoin_map K S σ,
  have h2 : intermediate_field.adjoin K (σ '' S) ≤ E,
  { apply intermediate_field.gc.l_le,
    exact hσSE },
  change ∃ (a : L), σ a = y,
  rw ← h1 at h2,
  have h3 := eq_of_map_le hE_findim h2,
  have hyE : y ∈ E,
  { have hyS : y ∈ S,
    { simp,
      rw polynomial.mem_roots,
      { rw [polynomial.is_root.def,
         ← polynomial.eval₂_eq_eval_map,
         ← polynomial.aeval_def],
        exact minpoly.aeval K y },
      { exact polynomial.map_monic_ne_zero (minpoly.monic (h_int y)) } },
    exact hSE hyS },
  rw ← h3 at hyE,
  rcases hyE with ⟨a, ha, hay⟩,
  exact ⟨a, hay⟩,
end

lemma alg_hom_of_ultrafilter_bijection {K L : Type*} [field K] [field L] [algebra K L]
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L)
(minpoly K x)) (f : ultrafilter (L ≃ₐ[K] L)) :
function.bijective (alg_hom_of_ultrafilter h_int f) :=
begin
  exact ⟨alg_hom_of_ultrafilter_injective h_int f,
  alg_hom_of_ultrafilter_surjective h_int h_splits f⟩,
end

/-- Since `alg_hom_of_ultrafilter h_int f` is a bijective `K`-algebra homomorphism `L →ₐ[K] L`,
  it is a `K`-algebra equivalence. Here we define the corresponding term of `L ≃ₐ[K] L`. -/
noncomputable def equiv_of_ultrafilter {K L : Type*} [field K] [field L] [algebra K L]
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L)
(minpoly K x)) (f : ultrafilter (L ≃ₐ[K] L)) :
(L ≃ₐ[K] L) :=
alg_equiv.of_bijective (alg_hom_of_ultrafilter h_int f) (alg_hom_of_ultrafilter_bijection h_int
h_splits f)

lemma equiv_of_ultrafilter_to_fun {K L : Type*} [field K] [field L] [algebra K L]
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L)
(minpoly K x)) (f : ultrafilter (L ≃ₐ[K] L)) :
(equiv_of_ultrafilter h_int h_splits f).to_fun = function_of_ultrafilter h_int f :=
rfl

lemma equiv_of_ultrafilter_to_alg_hom {K L : Type*} [field K] [field L] [algebra K L]
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L)
(minpoly K x)) (f : ultrafilter (L ≃ₐ[K] L)) :
(equiv_of_ultrafilter h_int h_splits f).to_alg_hom = alg_hom_of_ultrafilter h_int f :=
rfl

/-- Let `L/K` be a normal algebraic field extension, let `f` be an ultrafilter on
  `L ≃ₐ[K] L`, and let `E/K` be a finite subextension. Then `equiv_of_ultrafilter h_int h_splits f`
  is a term of `L ≃ₐ[K] L`, and `alg_hom_of_finite_dimensional_of_ultrafilter h_findim f` is a term
  `E →ₐ[K] L`. This Lemma tells us that the underlying maps of these two terms agree on `E`.
    -/
lemma equiv_restricts_to_alg_hom_of_finite_dimensional {K L : Type*} [field K] [field L]
[algebra K L]
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L)
(minpoly K x)) (f : ultrafilter (L ≃ₐ[K] L)) {E : intermediate_field K L}
(h_findim : finite_dimensional K E) :
((equiv_of_ultrafilter h_int h_splits f).to_alg_hom.comp E.val) =
alg_hom_of_finite_dimensional_of_ultrafilter h_findim f :=
begin
  ext,
  exact function_of_ultrafilter_spec h_int f h_findim x,
end

/-- The restriction map `L ≃ₐ[K] L → E →ₐ[K] L`. -/
def res {K L : Type*} [field K] [field L] [algebra K L] (E : intermediate_field K L):
(L ≃ₐ[K] L) → (E →ₐ[K] L) :=
λ f, f.to_alg_hom.comp E.val

lemma res_eq_map {K L : Type*} [field K] [field L] [algebra K L] {E : intermediate_field K L}
(σ : L ≃ₐ[K] L) (x : E) :
σ x = (res E σ) x :=
begin
  unfold res,
  simp,
end

lemma inv_mul_alg_equiv_of_elem {K L : Type*} [field K] [field L] [algebra K L]
(x : L) (f g : L ≃ₐ[K] L)  :
(f⁻¹ * g) x = x ↔ g x = f x :=
begin
   rw alg_equiv.mul_apply,
   split,
   { intro h,
    have h' := congr_arg f h,
    rw [← alg_equiv.mul_apply, mul_right_inv] at h',
    exact h' },
   { intro h,
    have h' := congr_arg f.symm h,
    rw alg_equiv.symm_apply_apply at h',
    exact h' },
end

lemma top_group_map_nhds_eq {G : Type*} [group G] [topological_space G]
[topological_group G] (g x : G) :
filter.map (λ y, g * y) (nhds x) = nhds (g * x) :=
begin
  ext,
  split,
  { intro h,
    rw [filter.mem_map, mem_nhds_iff] at h,
    rcases h with ⟨U, h_subset, h_open, hxU⟩,
    rw mem_nhds_iff,
    use left_coset g U,
    split,
    { rw ← set.image_subset_iff at h_subset,
      exact h_subset },
    refine ⟨_, ⟨x, ⟨hxU, rfl⟩⟩⟩,
    apply is_open_map_mul_left g,
    exact h_open },
  { intro h,
    rw mem_nhds_iff at h,
    rcases h with ⟨U, h_subset, h_open, hgxU⟩,
    rw [filter.mem_map, mem_nhds_iff],
    use left_coset g⁻¹ U,
    split,
    { rw ← set.image_subset_iff,
      have h : (λ (y : G), g * y) '' left_coset g⁻¹ U = U,
      { ext a,
        refine ⟨_, λ ha, ⟨g⁻¹ * a, ⟨a, ha, rfl⟩, by simp⟩⟩,
        rintro ⟨b, ⟨c, hcU, hcb⟩, hba⟩,
        change g⁻¹ * c = b at hcb,
        change g * b = a at hba,
        rw [← hcb, ← mul_assoc, mul_right_inv, one_mul] at hba,
        rw ← hba,
        exact hcU },
      rw h,
      exact h_subset },
    refine ⟨_, ⟨g * x, hgxU, by simp⟩⟩,
    apply is_open_map_mul_left g⁻¹,
    exact h_open },
end


lemma sigma_is_limit {K L : Type*} [field K] [field L] [algebra K L]
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L)
(minpoly K x))
(f : ultrafilter (L ≃ₐ[K] L))
(h_le_princ : ↑f ≤ filter.principal
 (set.univ : set (L ≃ₐ[K] L))) :
(f : filter (L ≃ₐ[K] L)) ≤ nhds (equiv_of_ultrafilter h_int h_splits f) :=
begin
  let σ := equiv_of_ultrafilter h_int h_splits f,
  intros A hA,
  have hA_coset : left_coset σ⁻¹ A ∈ nhds (1 : L ≃ₐ[K] L),
  { have h_sigma_1 : σ = σ * 1 := by simp,
    change A ∈ nhds σ at hA,
    rw [h_sigma_1, ← top_group_map_nhds_eq σ 1, filter.mem_map] at hA,
    have h : left_coset σ⁻¹ A = (λ y, σ * y)⁻¹' A,
    { ext,
      split,
      { rintro ⟨a, ha, hax⟩,
        simp [hax.symm, ha] },
      { intro hx,
        rw set.mem_preimage at hx,
        rw [mem_left_coset_iff, inv_inv],
        exact hx } },
    rw h,
    exact hA },
  have hA_coset_cont_H : ∃ (E : intermediate_field K L), finite_dimensional K E
  ∧ E.fixing_subgroup.carrier ⊆ left_coset σ⁻¹ A,
  { rw [group_filter_basis.nhds_one_eq, filter_basis.mem_filter_iff] at hA_coset,
    rcases hA_coset with ⟨H_set, hH, hA_coset⟩,
    change H_set ∈ gal_basis K L at hH,
    rw mem_gal_basis_iff at hH,
    rcases hH with ⟨H, ⟨E, hE, hHE⟩, hHH_set⟩,
    refine ⟨E, hE, _⟩,
    rw [hHE, hHH_set],
    exact hA_coset },
  rcases hA_coset_cont_H with ⟨E, h_findim, hEA⟩,
  have hEA' : left_coset σ E.fixing_subgroup ⊆ A,
  { rintros x ⟨y, hy, hyx⟩,
    change σ * y = x at hyx,
    specialize hEA hy,
    rcases hEA with ⟨a, ha, hay⟩,
    change σ⁻¹ * a = y at hay,
    rw inv_mul_eq_iff_eq_mul at hay,
    rw [← hyx, ← hay],
    exact ha },
  let p : (L ≃ₐ[K] L) → (E →ₐ[K] L) := λ σ, (σ.to_alg_hom.comp E.val),
  have h_principal : f.map p = pure (p σ),
  { have h : p σ = alg_hom_of_finite_dimensional_of_ultrafilter h_findim f :=
    equiv_restricts_to_alg_hom_of_finite_dimensional h_int h_splits f h_findim,
    rw h,
    have h2 : ↑(ultrafilter.map p f) = pure (alg_hom_of_finite_dimensional_of_ultrafilter h_findim
    f) :=
    alg_hom_of_finite_dimensional_of_ultrafilter_spec h_findim f,
    ext,
    split,
    { intro hs,
      rw [← ultrafilter.mem_coe, h2] at hs,
      exact hs },
    { intro hs,
      rw ultrafilter.mem_pure at hs,
      have h3 : s ∈ (pure (alg_hom_of_finite_dimensional_of_ultrafilter h_findim f) : filter
      (↥E →ₐ[K] L)),
      { rw filter.mem_pure,
        exact hs },
      rw ← h2 at h3,
      rw ultrafilter.mem_coe at h3,
      exact h3 } },
  have h_small_set : left_coset σ E.fixing_subgroup ∈ f,
  { have h : {p σ} ∈ (pure (p σ) : ultrafilter (E →ₐ[K] L)) := set.mem_singleton (p σ),
    rw [← h_principal, ultrafilter.mem_map] at h,
    have h_preim : p⁻¹' {p σ} = left_coset σ E.fixing_subgroup,
    { ext g,
      split,
      { intro hg,
        rw [set.mem_preimage, set.mem_singleton_iff] at hg,
        rw mem_left_coset_iff,
        intro x,
        have h_g_on_x : g x = (p g) x := res_eq_map g x,
        have h_σ_on_x : σ x = (p σ) x := res_eq_map σ x,
        change (σ⁻¹ * g) x = x,
        rw [inv_mul_alg_equiv_of_elem, h_g_on_x, h_σ_on_x, hg] },
      { intro hg,
        rw [set.mem_preimage, set.mem_singleton_iff],
        ext,
        have h_g_on_x : g x = (p g) x := res_eq_map g x,
        have h_σ_on_x : σ x = (p σ) x := res_eq_map σ x,
        rw [← h_g_on_x, ← h_σ_on_x, ← inv_mul_alg_equiv_of_elem],
        exact (mem_left_coset_iff σ).1 hg x } },
    rw h_preim at h,
    exact h },
  exact f.to_filter.sets_of_superset h_small_set hEA',
end


lemma krull_topology_compact {K L : Type*} [field K] [field L] [algebra K L]
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L)
(minpoly K x))  :
is_compact (set.univ : set (L ≃ₐ[K] L)) := is_compact_iff_ultrafilter_le_nhds.2
  (λ f hf,  ⟨equiv_of_ultrafilter h_int h_splits f,
  set.mem_univ (equiv_of_ultrafilter h_int h_splits f),
  sigma_is_limit h_int h_splits f hf⟩)

/-- Term of type `CompHaus`, showing that the Krull topology on `L ≃ₐ[K] L` is compact and
  Hausdorff -/
def krull_topology_comphaus {K L : Type*} [field K] [field L] [algebra K L]
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L)
(minpoly K x)):
CompHaus :=
{ to_Top := Top.of (L ≃ₐ[K] L),
  is_compact := { compact_univ := krull_topology_compact h_int h_splits },
  is_hausdorff := krull_topology_t2 h_int }

/-- Term of type `totally_disconnected_space (L ≃ₐ[K] L)`, showing that the Krull topology
  is totally disconnected. -/
def krull_topology_totally_disconnected_space {K L : Type*} [field K] [field L] [algebra K L]
(h_int : ∀ (x : L), is_integral K x) :
totally_disconnected_space (L ≃ₐ[K] L) :=
{ is_totally_disconnected_univ := krull_topology_totally_disconnected h_int}

/-- Term of type `Profinite`, showing that the Krull topology is profinite. -/
def krull_topology_profinite {K L : Type*} [field K] [field L] [algebra K L]
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L)
(minpoly K x)) :
Profinite :=
{ to_CompHaus := krull_topology_comphaus h_int h_splits,
  is_totally_disconnected := krull_topology_totally_disconnected_space h_int}
