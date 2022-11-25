/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import algebra.category.Module.projective
import algebraic_topology.extra_degeneracy
import category_theory.abelian.ext
import representation_theory.Rep

/-!
# The structure of the `k[G]`-module `k[Gⁿ]`

This file contains facts about an important `k[G]`-module structure on `k[Gⁿ]`, where `k` is a
commutative ring and `G` is a group. The module structure arises from the representation
`G →* End(k[Gⁿ])` induced by the diagonal action of `G` on `Gⁿ.`

In particular, we define an isomorphism of `k`-linear `G`-representations between `k[Gⁿ⁺¹]` and
`k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`).

This allows us to define a `k[G]`-basis on `k[Gⁿ⁺¹]`, by mapping the natural `k[G]`-basis of
`k[G] ⊗ₖ k[Gⁿ]` along the isomorphism.

We then define the standard resolution of `k` as a trivial representation, by
taking the alternating face map complex associated to an appropriate simplicial `k`-linear
`G`-representation. This simplicial object is the `linearization` of the simplicial `G`-set given
by the universal cover of the classifying space of `G`, `EG`. We prove this simplicial `G`-set `EG`
is isomorphic to the Čech nerve of the natural arrow of `G`-sets `G ⟶ {pt}`.

We then use this isomorphism to deduce that as a complex of `k`-modules, the standard resolution
of `k` as a trivial `G`-representation is homotopy equivalent to the complex with `k` at 0 and 0
elsewhere.

Putting this material together allows us to define `group_cohomology.ProjectiveResolution`, the
standard projective resolution of `k` as a trivial `k`-linear `G`-representation.

## Main definitions

 * `group_cohomology.resolution.to_tensor`
 * `group_cohomology.resolution.of_tensor`
 * `Rep.of_mul_action`
 * `group_cohomology.resolution.equiv_tensor`
 * `group_cohomology.resolution.of_mul_action_basis`
 * `classifying_space_universal_cover`
 * `group_cohomology.resolution.forget₂_to_Module_homotopy_equiv`
 * `group_cohomology.ProjectiveResolution`

## Implementation notes

We express `k[G]`-module structures on a module `k`-module `V` using the `representation`
definition. We avoid using instances `module (G →₀ k) V` so that we do not run into possible
scalar action diamonds.

We also use the category theory library to bundle the type `k[Gⁿ]` - or more generally `k[H]` when
`H` has `G`-action - and the representation together, as a term of type `Rep k G`, and call it
`Rep.of_mul_action k G H.` This enables us to express the fact that certain maps are
`G`-equivariant by constructing morphisms in the category `Rep k G`, i.e., representations of `G`
over `k`.
-/

noncomputable theory

universes u v w

variables {k G : Type u} [comm_ring k] {n : ℕ}

open_locale tensor_product
open category_theory

local notation `Gⁿ` := fin n → G
local notation `Gⁿ⁺¹` := fin (n + 1) → G

namespace group_cohomology.resolution

open finsupp (hiding lift) fin (partial_prod) representation

section basis
variables (k G n) [group G]

/-- The `k`-linear map from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` sending `(g₀, ..., gₙ)`
to `g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def to_tensor_aux :
  ((fin (n + 1) → G) →₀ k) →ₗ[k] (G →₀ k) ⊗[k] ((fin n → G) →₀ k) :=
finsupp.lift ((G →₀ k) ⊗[k] ((fin n → G) →₀ k)) k (fin (n + 1) → G)
  (λ x, single (x 0) 1 ⊗ₜ[k] single (λ i, (x i)⁻¹ * x i.succ) 1)

/-- The `k`-linear map from `k[G] ⊗ₖ k[Gⁿ]` to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)`. -/
def of_tensor_aux :
  (G →₀ k) ⊗[k] ((fin n → G) →₀ k) →ₗ[k] ((fin (n + 1) → G) →₀ k) :=
tensor_product.lift (finsupp.lift _ _ _ $ λ g, finsupp.lift _ _ _
  (λ f, single (g • partial_prod f) (1 : k)))

variables {k G n}

lemma to_tensor_aux_single (f : Gⁿ⁺¹) (m : k) :
  to_tensor_aux k G n (single f m) = single (f 0) m ⊗ₜ single (λ i, (f i)⁻¹ * f i.succ) 1 :=
begin
  simp only [to_tensor_aux, lift_apply, sum_single_index, tensor_product.smul_tmul'],
  { simp },
end

lemma to_tensor_aux_of_mul_action (g : G) (x : Gⁿ⁺¹) :
  to_tensor_aux k G n (of_mul_action k G Gⁿ⁺¹ g (single x 1)) =
  tensor_product.map (of_mul_action k G G g) 1 (to_tensor_aux k G n (single x 1)) :=
by simp [of_mul_action_def, to_tensor_aux_single, mul_assoc, inv_mul_cancel_left]

lemma of_tensor_aux_single (g : G) (m : k) (x : Gⁿ →₀ k) :
  of_tensor_aux k G n ((single g m) ⊗ₜ x) =
  finsupp.lift (Gⁿ⁺¹ →₀ k) k Gⁿ (λ f, single (g • partial_prod f) m) x :=
by simp [of_tensor_aux, sum_single_index, smul_sum, mul_comm m]

lemma of_tensor_aux_comm_of_mul_action (g h : G) (x : Gⁿ) :
  of_tensor_aux k G n (tensor_product.map (of_mul_action k G G g)
  (1 : module.End k (Gⁿ →₀ k)) (single h (1 : k) ⊗ₜ single x (1 : k))) =
  of_mul_action k G Gⁿ⁺¹ g (of_tensor_aux k G n (single h 1 ⊗ₜ single x 1)) :=
begin
  simp [of_mul_action_def, of_tensor_aux_single, mul_smul],
end

lemma to_tensor_aux_left_inv (x : Gⁿ⁺¹ →₀ k) :
  of_tensor_aux _ _ _ (to_tensor_aux _ _ _ x) = x :=
begin
  refine linear_map.ext_iff.1 (@finsupp.lhom_ext _ _ _ k _ _ _ _ _
    (linear_map.comp (of_tensor_aux _ _ _) (to_tensor_aux _ _ _)) linear_map.id (λ x y, _)) x,
  dsimp,
  rw [to_tensor_aux_single x y, of_tensor_aux_single, finsupp.lift_apply, finsupp.sum_single_index,
    one_smul, fin.partial_prod_left_inv],
  { rw zero_smul }
end

lemma to_tensor_aux_right_inv (x : (G →₀ k) ⊗[k] (Gⁿ →₀ k)) :
  to_tensor_aux _ _ _ (of_tensor_aux _ _ _ x) = x :=
begin
  refine tensor_product.induction_on x (by simp) (λ y z, _) (λ z w hz hw, by simp [hz, hw]),
  rw [←finsupp.sum_single y, finsupp.sum, tensor_product.sum_tmul],
  simp only [finset.smul_sum, linear_map.map_sum],
  refine finset.sum_congr rfl (λ f hf, _),
  simp only [of_tensor_aux_single, finsupp.lift_apply, finsupp.smul_single',
    linear_map.map_finsupp_sum, to_tensor_aux_single, fin.partial_prod_right_inv],
  dsimp,
  simp only [fin.partial_prod_zero, mul_one],
  conv_rhs {rw [←finsupp.sum_single z, finsupp.sum, tensor_product.tmul_sum]},
  exact finset.sum_congr rfl (λ g hg, show _ ⊗ₜ _ = _, by
    rw [←finsupp.smul_single', tensor_product.smul_tmul, finsupp.smul_single_one])
end

variables (k G n)

/-- A hom of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def to_tensor : Rep.of_mul_action k G (fin (n + 1) → G) ⟶ Rep.of
  ((representation.of_mul_action k G G).tprod (1 : G →* module.End k ((fin n → G) →₀ k))) :=
{ hom := to_tensor_aux k G n,
  comm' := λ g, by ext; exact to_tensor_aux_of_mul_action _ _ }

/-- A hom of `k`-linear representations of `G` from `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)`. -/
def of_tensor :
  Rep.of ((representation.of_mul_action k G G).tprod (1 : G →* module.End k ((fin n → G) →₀ k)))
    ⟶ Rep.of_mul_action k G (fin (n + 1) → G) :=
{ hom := of_tensor_aux k G n,
  comm' := λ g, by { ext, congr' 1, exact (of_tensor_aux_comm_of_mul_action _ _ _) }}

variables {k G n}

@[simp] lemma to_tensor_single (f : Gⁿ⁺¹) (m : k) :
  (to_tensor k G n).hom (single f m) = single (f 0) m ⊗ₜ single (λ i, (f i)⁻¹ * f i.succ) 1 :=
to_tensor_aux_single _ _

@[simp] lemma of_tensor_single (g : G) (m : k) (x : Gⁿ →₀ k) :
  (of_tensor k G n).hom ((single g m) ⊗ₜ x) =
  finsupp.lift (Rep.of_mul_action k G Gⁿ⁺¹) k Gⁿ (λ f, single (g • partial_prod f) m) x :=
of_tensor_aux_single _ _ _

lemma of_tensor_single' (g : G →₀ k) (x : Gⁿ) (m : k) :
  (of_tensor k G n).hom (g ⊗ₜ single x m) =
  finsupp.lift _ k G (λ a, single (a • partial_prod x) m) g :=
by simp [of_tensor, of_tensor_aux]

variables (k G n)

/-- An isomorphism of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on
which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def equiv_tensor : (Rep.of_mul_action k G (fin (n + 1) → G)) ≅ Rep.of
  ((representation.of_mul_action k G G).tprod (1 : representation k G ((fin n → G) →₀ k))) :=
Action.mk_iso (linear_equiv.to_Module_iso
{ inv_fun := of_tensor_aux k G n,
  left_inv := to_tensor_aux_left_inv,
  right_inv := λ x, by convert to_tensor_aux_right_inv x,
  ..to_tensor_aux k G n }) (to_tensor k G n).comm

@[simp] lemma equiv_tensor_def :
  (equiv_tensor k G n).hom = to_tensor k G n := rfl

@[simp] lemma equiv_tensor_inv_def :
  (equiv_tensor k G n).inv = of_tensor k G n := rfl

/-- The `k[G]`-linear isomorphism `k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹]`, where the `k[G]`-module structure on
the lefthand side is `tensor_product.left_module`, whilst that of the righthand side comes from
`representation.as_module`. Allows us to use `basis.algebra_tensor_product` to get a `k[G]`-basis
of the righthand side. -/
def of_mul_action_basis_aux : (monoid_algebra k G ⊗[k] ((fin n → G) →₀ k)) ≃ₗ[monoid_algebra k G]
  (of_mul_action k G (fin (n + 1) → G)).as_module :=
{ map_smul' := λ r x,
  begin
    rw [ring_hom.id_apply, linear_equiv.to_fun_eq_coe, ←linear_equiv.map_smul],
    congr' 1,
    refine x.induction_on _ (λ x y, _) (λ y z hy hz, _),
    { simp only [smul_zero] },
    { simp only [tensor_product.smul_tmul'],
      show (r * x) ⊗ₜ y = _,
      rw [←of_mul_action_self_smul_eq_mul, smul_tprod_one_as_module] },
    { rw [smul_add, hz, hy, smul_add], }
  end, .. ((Rep.equivalence_Module_monoid_algebra.1).map_iso
    (equiv_tensor k G n).symm).to_linear_equiv }

/-- A `k[G]`-basis of `k[Gⁿ⁺¹]`, coming from the `k[G]`-linear isomorphism
`k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹].` -/
def of_mul_action_basis  :
  basis (fin n → G) (monoid_algebra k G) (of_mul_action k G (fin (n + 1) → G)).as_module :=
@basis.map _ (monoid_algebra k G) (monoid_algebra k G ⊗[k] ((fin n → G) →₀ k))
  _ _ _ _ _ _ (@algebra.tensor_product.basis k _ (monoid_algebra k G) _ _ ((fin n → G) →₀ k) _ _
  (fin n → G) ⟨linear_equiv.refl k _⟩) (of_mul_action_basis_aux k G n)

lemma of_mul_action_free :
  module.free (monoid_algebra k G) (of_mul_action k G (fin (n + 1) → G)).as_module :=
module.free.of_basis (of_mul_action_basis k G n)

end basis
end group_cohomology.resolution
variables (G)

/-- The simplicial `G`-set sending `[n]` to `Gⁿ⁺¹` equipped with the diagonal action of `G`. -/
def classifying_space_universal_cover [monoid G] :
  simplicial_object (Action (Type u) $ Mon.of G) :=
{ obj := λ n, Action.of_mul_action G (fin (n.unop.len + 1) → G),
  map := λ m n f,
  { hom := λ x, x ∘ f.unop.to_order_hom,
    comm' := λ g, rfl },
  map_id' := λ n, rfl,
  map_comp' := λ i j k f g, rfl }

namespace classifying_space_universal_cover
open category_theory category_theory.limits
variables [monoid G]

/-- When the category is `G`-Set, `cech_nerve_terminal_from` of `G` with the left regular action is
isomorphic to `EG`, the universal cover of the classifying space of `G` as a simplicial `G`-set. -/
def cech_nerve_terminal_from_iso :
  cech_nerve_terminal_from (Action.of_mul_action G G) ≅ classifying_space_universal_cover G :=
nat_iso.of_components (λ n, limit.iso_limit_cone (Action.of_mul_action_limit_cone _ _)) $ λ m n f,
begin
  refine is_limit.hom_ext (Action.of_mul_action_limit_cone.{u 0} _ _).2 (λ j, _),
  dunfold cech_nerve_terminal_from pi.lift,
  dsimp,
  rw [category.assoc, limit.iso_limit_cone_hom_π, limit.lift_π, category.assoc],
  exact (limit.iso_limit_cone_hom_π _ _).symm,
end

/-- As a simplicial set, `cech_nerve_terminal_from` of a monoid `G` is isomorphic to the universal
cover of the classifying space of `G` as a simplicial set. -/
def cech_nerve_terminal_from_iso_comp_forget :
  cech_nerve_terminal_from G ≅ classifying_space_universal_cover G ⋙ forget _ :=
nat_iso.of_components (λ n, types.product_iso _) $ λ m n f, matrix.ext $ λ i j,
  types.limit.lift_π_apply _ _ _ _

variables (k G)
open algebraic_topology simplicial_object.augmented simplicial_object category_theory.arrow

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `fin 1 → G` to the terminal object in `Type u`. -/
def comp_forget_augmented : simplicial_object.augmented (Type u) :=
simplicial_object.augment (classifying_space_universal_cover G ⋙ forget _) (terminal _)
(terminal.from _) $ λ i g h, subsingleton.elim _ _

/-- The augmented Čech nerve of the map from `fin 1 → G` to the terminal object in `Type u` has an
extra degeneracy. -/
def extra_degeneracy_augmented_cech_nerve :
  extra_degeneracy (arrow.mk $ terminal.from G).augmented_cech_nerve :=
augmented_cech_nerve.extra_degeneracy (arrow.mk $ terminal.from G)
  ⟨λ x, (1 : G), @subsingleton.elim _ (@unique.subsingleton _ (limits.unique_to_terminal _)) _ _⟩

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `fin 1 → G` to the terminal object in `Type u`, has an extra degeneracy. -/
def extra_degeneracy_comp_forget_augmented :
  extra_degeneracy (comp_forget_augmented G) :=
begin
  refine extra_degeneracy.of_iso (_ : (arrow.mk $ terminal.from G).augmented_cech_nerve ≅ _)
    (extra_degeneracy_augmented_cech_nerve G),
  exact comma.iso_mk (cech_nerve_terminal_from.iso G ≪≫
    cech_nerve_terminal_from_iso_comp_forget G) (iso.refl _)
    (by ext : 2; apply is_terminal.hom_ext terminal_is_terminal),
end

/-- The free functor `Type u ⥤ Module.{u} k` applied to the universal cover of the classifying
space of `G` as a simplicial set, augmented by the map from `fin 1 → G` to the terminal object
in `Type u`. -/
def comp_forget_augmented.to_Module : simplicial_object.augmented (Module.{u} k) :=
((simplicial_object.augmented.whiskering _ _).obj (Module.free k)).obj (comp_forget_augmented G)

/-- If we augment the universal cover of the classifying space of `G` as a simplicial set by the
map from `fin 1 → G` to the terminal object in `Type u`, then apply the free functor
`Type u ⥤ Module.{u} k`, the resulting augmented simplicial `k`-module has an extra degeneracy. -/
def extra_degeneracy_comp_forget_augmented_to_Module :
  extra_degeneracy (comp_forget_augmented.to_Module k G) :=
extra_degeneracy.map (extra_degeneracy_comp_forget_augmented G) (Module.free k)

end classifying_space_universal_cover

variables (k)

/-- The standard resolution of `k` as a trivial representation, defined as the alternating
face map complex of a simplicial `k`-linear `G`-representation. -/
def group_cohomology.resolution [monoid G] :=
(algebraic_topology.alternating_face_map_complex (Rep k G)).obj
  (classifying_space_universal_cover G ⋙ (Rep.linearization k G).1.1)

namespace group_cohomology.resolution
open classifying_space_universal_cover algebraic_topology category_theory category_theory.limits

variables (k G) [monoid G]

/-- The `k`-linear map underlying the differential in the standard resolution of `k` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ)`. -/
def d (G : Type u) (n : ℕ) : ((fin (n + 1) → G) →₀ k) →ₗ[k] ((fin n → G) →₀ k) :=
finsupp.lift ((fin n → G) →₀ k) k (fin (n + 1) → G) (λ g, (@finset.univ (fin (n + 1)) _).sum
  (λ p, finsupp.single (g ∘ p.succ_above) ((-1 : k) ^ (p : ℕ))))

variables {k G}

@[simp] lemma d_of {G : Type u} {n : ℕ} (c : fin (n + 1) → G) :
  d k G n (finsupp.single c 1) = finset.univ.sum (λ p : fin (n + 1), finsupp.single
    (c ∘ p.succ_above) ((-1 : k) ^ (p : ℕ))) :=
by simp [d]

variables (k G)

/-- The `n`th object of the standard resolution of `k` is definitionally isomorphic to `k[Gⁿ⁺¹]`
equipped with the representation induced by the diagonal action of `G`. -/
def X_iso (n : ℕ) :
  (group_cohomology.resolution k G).X n ≅ Rep.of_mul_action k G (fin (n + 1) → G) := iso.refl _

lemma X_projective (G : Type u) [group G] (n : ℕ) :
  projective ((group_cohomology.resolution k G).X n) :=
Rep.equivalence_Module_monoid_algebra.to_adjunction.projective_of_map_projective _ $
  @Module.projective_of_free.{u} _ _ (Module.of (monoid_algebra k G)
  (representation.of_mul_action k G (fin (n + 1) → G)).as_module) _ (of_mul_action_basis k G n)

/-- Simpler expression for the differential in the standard resolution of `k` as a
`G`-representation. It sends `(g₀, ..., gₙ₊₁) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ₊₁)`. -/
theorem d_eq (n : ℕ) :
  ((group_cohomology.resolution k G).d (n + 1) n).hom = d k G (n + 1) :=
begin
  ext x y,
  dsimp [group_cohomology.resolution],
  simpa [←@int_cast_smul k, simplicial_object.δ],
end

section exactness

/-- The standard resolution of `k` as a trivial representation as a complex of `k`-modules. -/
def forget₂_to_Module := ((forget₂ (Rep k G) (Module.{u} k)).map_homological_complex _).obj
(group_cohomology.resolution k G)

/-- If we apply the free functor `Type u ⥤ Module.{u} k` to the universal cover of the classifying
space of `G` as a simplicial set, then take the alternating face map complex, the result is
isomorphic to the standard resolution of the trivial `G`-representation `k` as a complex of
`k`-modules. -/
def comp_forget_augmented_iso : (alternating_face_map_complex.obj
  (simplicial_object.augmented.drop.obj (comp_forget_augmented.to_Module k G))) ≅
  group_cohomology.resolution.forget₂_to_Module k G :=
eq_to_iso (functor.congr_obj (map_alternating_face_map_complex (forget₂ (Rep k G)
  (Module.{u} k))).symm (classifying_space_universal_cover G ⋙ (Rep.linearization k G).1.1))

/-- As a complex of `k`-modules, the standard resolution of the trivial `G`-representation `k` is
homotopy equivalent to the complex which is `k` at 0 and 0 elsewhere. -/
def forget₂_to_Module_homotopy_equiv : homotopy_equiv
  (group_cohomology.resolution.forget₂_to_Module k G)
  ((chain_complex.single₀ (Module k)).obj
  ((forget₂ (Rep k G) _).obj $ Rep.of representation.trivial)) :=
(homotopy_equiv.of_iso (comp_forget_augmented_iso k G).symm).trans $
  (simplicial_object.augmented.extra_degeneracy.homotopy_equiv
    (extra_degeneracy_comp_forget_augmented_to_Module k G)).trans
  (homotopy_equiv.of_iso $ (chain_complex.single₀ (Module.{u} k)).map_iso
    (@finsupp.linear_equiv.finsupp_unique k k _ _ _ (⊤_ (Type u))
      types.terminal_iso.to_equiv.unique).to_Module_iso)

/-- The hom of `k`-linear `G`-representations `k[G¹] → k` sending `∑ nᵢgᵢ ↦ ∑ nᵢ`. -/
def ε : Rep.of_mul_action k G (fin 1 → G) ⟶ Rep.of representation.trivial :=
{ hom := finsupp.total _ _ _ (λ f, (1 : k)),
  comm' := λ g,
  begin
    ext,
    show finsupp.total (fin 1 → G) k k (λ f, (1 : k))
      (finsupp.map_domain _ (finsupp.single _ _)) = finsupp.total _ _ _ _ (finsupp.single _ _),
    simp only [finsupp.map_domain_single, finsupp.total_single],
  end }

/-- The homotopy equivalence of complexes of `k`-modules between the standard resolution of `k` as
a trivial `G`-representation, and the complex which is `k` at 0 and 0 everywhere else, acts as
`∑ nᵢgᵢ ↦ ∑ nᵢ : k[G¹] → k` at 0. -/
lemma forget₂_to_Module_homotopy_equiv_f_0_eq :
  (forget₂_to_Module_homotopy_equiv k G).1.f 0 =
  (forget₂ (Rep k G) _).map (ε k G) :=
begin
  show (homotopy_equiv.hom _ ≫ (homotopy_equiv.hom _ ≫ homotopy_equiv.hom _)).f 0 = _,
  simp only [homological_complex.comp_f],
  convert category.id_comp _,
  { dunfold homotopy_equiv.of_iso comp_forget_augmented_iso map_alternating_face_map_complex,
    simp only [iso.symm_hom, eq_to_iso.inv, homological_complex.eq_to_hom_f, eq_to_hom_refl] },
  transitivity ((finsupp.total _ _ _ (λ f, (1 : k))).comp
    ((Module.free k).map (terminal.from _))),
  { dsimp,
    rw [@finsupp.lmap_domain_total (fin 1 → G) k k _ _ _ (⊤_ (Type u)) k _ _ (λ i, (1 : k))
      (λ i, (1 : k)) (terminal.from ((classifying_space_universal_cover G).obj
      (opposite.op (simplex_category.mk 0))).V) linear_map.id (λ i, rfl), linear_map.id_comp],
    refl },
  { congr,
    { ext,
      dsimp [homotopy_equiv.of_iso],
      rw [finsupp.total_single, one_smul, @unique.eq_default _
        types.terminal_iso.to_equiv.unique a, finsupp.single_eq_same] },
    { exact (@subsingleton.elim _ (@unique.subsingleton _ (limits.unique_to_terminal _)) _ _) }}
end

lemma d_comp_ε : (group_cohomology.resolution k G).d 1 0 ≫ ε k G = 0 :=
begin
  ext1,
  refine linear_map.ext (λ x, _),
  have : (forget₂_to_Module k G).d 1 0 ≫ (forget₂ (Rep k G) (Module.{u} k)).map (ε k G) = 0,
  by rw [←forget₂_to_Module_homotopy_equiv_f_0_eq,
    ←(forget₂_to_Module_homotopy_equiv k G).1.2 1 0 rfl]; exact comp_zero,
  exact linear_map.ext_iff.1 this _,
end

/-- The chain map from the standard resolution of `k` to `k[0]` given by `∑ nᵢgᵢ ↦ ∑ nᵢ` in
degree zero. -/
def ε_to_single₀ : group_cohomology.resolution k G ⟶ (chain_complex.single₀ _).obj
  (Rep.of representation.trivial) :=
((group_cohomology.resolution k G).to_single₀_equiv _).symm ⟨ε k G, d_comp_ε k G⟩

lemma ε_to_single₀_comp_eq : ((forget₂ _ (Module.{u} k)).map_homological_complex _).map
  (ε_to_single₀ k G) ≫ ((chain_complex.single₀_map_homological_complex _).hom.app _) =
  (forget₂_to_Module_homotopy_equiv k G).hom :=
begin
  refine chain_complex.to_single₀_ext _ _ _,
  dsimp,
  rw category.comp_id,
  exact (forget₂_to_Module_homotopy_equiv_f_0_eq k G).symm,
end

lemma quasi_iso_of_forget₂_ε_to_single₀ :
  quasi_iso (((forget₂ _ (Module.{u} k)).map_homological_complex _).map (ε_to_single₀ k G)) :=
begin
  have h : quasi_iso (forget₂_to_Module_homotopy_equiv k G).hom := homotopy_equiv.to_quasi_iso _,
  rw ← ε_to_single₀_comp_eq k G at h,
  haveI := h,
  exact quasi_iso_of_comp_right _ (((chain_complex.single₀_map_homological_complex _).hom.app _)),
end

instance : quasi_iso (ε_to_single₀ k G) :=
(forget₂ _ (Module.{u} k)).quasi_iso_of_map_quasi_iso _ (quasi_iso_of_forget₂_ε_to_single₀ k G)

end exactness
end group_cohomology.resolution
open group_cohomology.resolution

variables [group G]

/-- The standard projective resolution of `k` as a trivial `k`-linear `G`-representation. -/
def group_cohomology.ProjectiveResolution :
  ProjectiveResolution (Rep.of (@representation.trivial k G _ _)) :=
(ε_to_single₀ k G).to_single₀_ProjectiveResolution (X_projective k G)

instance : enough_projectives (Rep k G) :=
Rep.equivalence_Module_monoid_algebra.enough_projectives_iff.2
  (Module.Module_enough_projectives.{u})

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is a trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
standard resolution of `k` called `group_cohomology.resolution k G`. -/
def group_cohomology.Ext_iso (V : Rep k G) (n : ℕ) :
  ((Ext k (Rep k G) n).obj (opposite.op $ Rep.of representation.trivial)).obj V ≅
    (((((linear_yoneda k (Rep k G)).obj V).right_op.map_homological_complex _).obj
      (group_cohomology.resolution k G)).homology n).unop :=
by let := (((linear_yoneda k (Rep k G)).obj V).right_op.left_derived_obj_iso
  n (group_cohomology.ProjectiveResolution k G)).unop.symm; exact this
