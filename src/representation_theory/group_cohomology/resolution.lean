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

 * `group_cohomology.resolution.Action_diagonal_succ`
 * `group_cohomology.resolution.diagonal_succ`
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

open category_theory

local notation `Gⁿ` := fin n → G
local notation `Gⁿ⁺¹` := fin (n + 1) → G

namespace group_cohomology.resolution

open finsupp (hiding lift) fin (partial_prod)

section basis
variables (k G n) [group G]

section Action
open Action

/-- An isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left multiplication on `Gⁿ⁺¹` and
`G` but trivially on `Gⁿ`. The map sends `(g₀, ..., gₙ) ↦ (g₀, (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ))`,
and the inverse is `(g₀, (g₁, ..., gₙ)) ↦ (g₀, g₀g₁, g₀g₁g₂, ..., g₀g₁...gₙ).` -/
def Action_diagonal_succ (G : Type u) [group G] : Π (n : ℕ),
  diagonal G (n + 1) ≅ left_regular G ⊗ Action.mk (fin n → G) 1
| 0 := diagonal_one_iso_left_regular G ≪≫ (ρ_ _).symm ≪≫ tensor_iso (iso.refl _)
  (tensor_unit_iso (equiv.equiv_of_unique punit _).to_iso)
| (n+1) := diagonal_succ _ _ ≪≫ tensor_iso (iso.refl _) (Action_diagonal_succ n)
  ≪≫ left_regular_tensor_iso _ _ ≪≫ tensor_iso (iso.refl _) (mk_iso
  (equiv.pi_fin_succ_above_equiv (λ j, G) 0).symm.to_iso (λ g, rfl))

lemma Action_diagonal_succ_hom_apply {G : Type u} [group G] {n : ℕ} (f : fin (n + 1) → G) :
  (Action_diagonal_succ G n).hom.hom f = (f 0, λ i, (f i)⁻¹ * f i.succ) :=
begin
  induction n with n hn,
  { exact prod.ext rfl (funext $ λ x, fin.elim0 x) },
  { ext,
    { refl },
    { dunfold Action_diagonal_succ,
      simp only [iso.trans_hom, comp_hom, types_comp_apply, diagonal_succ_hom_hom,
        left_regular_tensor_iso_hom_hom, tensor_iso_hom, mk_iso_hom_hom, equiv.to_iso_hom,
        tensor_hom, equiv.pi_fin_succ_above_equiv_symm_apply, tensor_apply, types_id_apply,
        tensor_rho, monoid_hom.one_apply, End.one_def, hn (λ (j : fin (n + 1)), f j.succ),
        fin.coe_eq_cast_succ, fin.insert_nth_zero'],
      refine fin.cases (fin.cons_zero _ _) (λ i, _) x,
      { simp only [fin.cons_succ, mul_left_inj, inv_inj, fin.cast_succ_fin_succ], }}}
end

lemma Action_diagonal_succ_inv_apply {G : Type u} [group G] {n : ℕ} (g : G) (f : fin n → G) :
  (Action_diagonal_succ G n).inv.hom (g, f) = (g • fin.partial_prod f : fin (n + 1) → G) :=
begin
  revert g,
  induction n with n hn,
  { intros g,
    ext,
    simpa only [subsingleton.elim x 0, pi.smul_apply, fin.partial_prod_zero,
      smul_eq_mul, mul_one] },
  { intro g,
    ext,
    dunfold Action_diagonal_succ,
    simp only [iso.trans_inv, comp_hom, hn, diagonal_succ_inv_hom, types_comp_apply,
      tensor_iso_inv, iso.refl_inv, tensor_hom, id_hom, tensor_apply, types_id_apply,
      left_regular_tensor_iso_inv_hom, tensor_rho, left_regular_ρ_apply, pi.smul_apply,
      smul_eq_mul],
    refine fin.cases _ _ x,
    { simp only [fin.cons_zero, fin.partial_prod_zero, mul_one], },
    { intro i,
      simpa only [fin.cons_succ, pi.smul_apply, smul_eq_mul, fin.partial_prod_succ', mul_assoc], }}
end

end Action
section Rep
open Rep

/-- An isomorphism of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on
which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. The inverse sends `g₀ ⊗ (g₁, ..., gₙ)` to
`(g₀, g₀g₁, ..., g₀g₁...gₙ)`. -/
def diagonal_succ (n : ℕ) :
  diagonal k G (n + 1) ≅ left_regular k G ⊗ trivial k G ((fin n → G) →₀ k) :=
(linearization k G).map_iso (Action_diagonal_succ G n)
  ≪≫ (as_iso ((linearization k G).μ (Action.left_regular G) _)).symm
  ≪≫ tensor_iso (iso.refl _) (linearization_trivial_iso k G (fin n → G))

variables {k G n}

lemma diagonal_succ_hom_single (f : Gⁿ⁺¹) (a : k) :
  (diagonal_succ k G n).hom.hom (single f a) =
  single (f 0) 1 ⊗ₜ single (λ i, (f i)⁻¹ * f i.succ) a :=
begin
  dunfold diagonal_succ,
  simpa only [iso.trans_hom, iso.symm_hom, Action.comp_hom, Module.comp_def, linear_map.comp_apply,
    functor.map_iso_hom, linearization_map_hom_single (Action_diagonal_succ G n).hom f a,
    as_iso_inv, linearization_μ_inv_hom, Action_diagonal_succ_hom_apply, finsupp_tensor_finsupp',
    linear_equiv.trans_symm, lcongr_symm, linear_equiv.trans_apply, lcongr_single,
    tensor_product.lid_symm_apply, finsupp_tensor_finsupp_symm_single,
    linear_equiv.coe_to_linear_map],
end

lemma diagonal_succ_inv_single_single (g : G) (f : Gⁿ) (a b : k) :
  (diagonal_succ k G n).inv.hom (finsupp.single g a ⊗ₜ finsupp.single f b) =
  single (g • partial_prod f) (a * b) :=
begin
  dunfold diagonal_succ,
  simp only [iso.trans_inv, iso.symm_inv, iso.refl_inv, tensor_iso_inv, Action.tensor_hom,
    Action.comp_hom, Module.comp_def, linear_map.comp_apply, as_iso_hom, functor.map_iso_inv,
    Module.monoidal_category.hom_apply, linearization_trivial_iso_inv_hom_apply,
    linearization_μ_hom, Action.id_hom ((linearization k G).obj _), Action_diagonal_succ_inv_apply,
    Module.id_apply, linear_equiv.coe_to_linear_map,
    finsupp_tensor_finsupp'_single_tmul_single k (Action.left_regular G).V,
    linearization_map_hom_single (Action_diagonal_succ G n).inv (g, f) (a * b)],
end

lemma diagonal_succ_inv_single_left (g : G) (f : Gⁿ →₀ k) (r : k) :
  (diagonal_succ k G n).inv.hom (finsupp.single g r ⊗ₜ f) =
  finsupp.lift (Gⁿ⁺¹ →₀ k) k Gⁿ (λ f, single (g • partial_prod f) r) f :=
begin
  refine f.induction _ _,
  { simp only [tensor_product.tmul_zero, map_zero] },
  { intros a b x ha hb hx,
    simp only [lift_apply, smul_single', mul_one, tensor_product.tmul_add, map_add,
      diagonal_succ_inv_single_single, hx, finsupp.sum_single_index,
      mul_comm b, zero_mul, single_zero] },
end

lemma diagonal_succ_inv_single_right (g : G →₀ k) (f : Gⁿ) (r : k) :
  (diagonal_succ k G n).inv.hom (g ⊗ₜ finsupp.single f r) =
  finsupp.lift _ k G (λ a, single (a • partial_prod f) r) g :=
begin
  refine g.induction _ _,
  { simp only [tensor_product.zero_tmul, map_zero], },
  { intros a b x ha hb hx,
    simp only [lift_apply, smul_single', map_add, hx, diagonal_succ_inv_single_single,
      tensor_product.add_tmul, finsupp.sum_single_index, zero_mul, single_zero] }
end

end Rep
variables (k G n)
open_locale tensor_product
open representation

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
    (diagonal_succ k G n).symm).to_linear_equiv }

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
namespace Rep
variables (n) [group G] (A : Rep k G)
open group_cohomology.resolution

/-- Given a `k`-linear `G`-representation `A`, the set of representation morphisms
`Hom(k[Gⁿ⁺¹], A)` is `k`-linearly isomorphic to the set of functions `Gⁿ → A`. -/
noncomputable def diagonal_hom_equiv :
  (Rep.of_mul_action k G (fin (n + 1) → G) ⟶ A) ≃ₗ[k] ((fin n → G) → A) :=
linear.hom_congr k ((diagonal_succ k G n).trans
  ((representation.of_mul_action k G G).Rep_of_tprod_iso 1)) (iso.refl _) ≪≫ₗ
  ((Rep.monoidal_closed.linear_hom_equiv_comm _ _ _) ≪≫ₗ (Rep.left_regular_hom_equiv _))
  ≪≫ₗ (finsupp.llift A k k (fin n → G)).symm

variables {n A}

/-- Given a `k`-linear `G`-representation `A`, `diagonal_hom_equiv` is a `k`-linear isomorphism of
the set of representation morphisms `Hom(k[Gⁿ⁺¹], A)` with `Fun(Gⁿ, A)`. This lemma says that this
sends a morphism of representations `f : k[Gⁿ⁺¹] ⟶ A` to the function
`(g₁, ..., gₙ) ↦ f(1, g₁, g₁g₂, ..., g₁g₂...gₙ).` -/
lemma diagonal_hom_equiv_apply (f : Rep.of_mul_action k G (fin (n + 1) → G) ⟶ A)
  (x : fin n → G) : diagonal_hom_equiv n A f x = f.hom (finsupp.single (fin.partial_prod x) 1) :=
begin
  unfold diagonal_hom_equiv,
  simpa only [linear_equiv.trans_apply, Rep.left_regular_hom_equiv_apply,
    monoidal_closed.linear_hom_equiv_comm_hom, finsupp.llift_symm_apply, tensor_product.curry_apply,
    linear.hom_congr_apply, iso.refl_hom, iso.trans_inv, Action.comp_hom, Module.comp_def,
    linear_map.comp_apply, representation.Rep_of_tprod_iso_inv_apply,
    diagonal_succ_inv_single_single (1 : G) x, one_smul, one_mul],
end

/-- Given a `k`-linear `G`-representation `A`, `diagonal_hom_equiv` is a `k`-linear isomorphism of
the set of representation morphisms `Hom(k[Gⁿ⁺¹], A)` with `Fun(Gⁿ, A)`. This lemma says that the
inverse map sends a function `f : Gⁿ → A` to the representation morphism sending
`(g₀, ... gₙ) ↦ ρ(g₀)(f(g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ))`, where `ρ` is the representation attached
to `A`. -/
lemma diagonal_hom_equiv_symm_apply (f : (fin n → G) → A) (x : fin (n + 1) → G) :
  ((diagonal_hom_equiv n A).symm f).hom (finsupp.single x 1)
    = A.ρ (x 0) (f (λ (i : fin n), (x ↑i)⁻¹ * x i.succ)) :=
begin
  unfold diagonal_hom_equiv,
  simp only [linear_equiv.trans_symm, linear_equiv.symm_symm, linear_equiv.trans_apply,
    Rep.left_regular_hom_equiv_symm_apply, linear.hom_congr_symm_apply, Action.comp_hom,
    iso.refl_inv, category.comp_id, Rep.monoidal_closed.linear_hom_equiv_comm_symm_hom,
    iso.trans_hom, Module.comp_def, linear_map.comp_apply, representation.Rep_of_tprod_iso_apply,
    diagonal_succ_hom_single x (1 : k), tensor_product.uncurry_apply, Rep.left_regular_hom_hom,
    finsupp.lift_apply, Rep.ihom_obj_ρ, representation.lin_hom_apply, finsupp.sum_single_index,
    zero_smul, one_smul, Rep.of_ρ, Rep.Action_ρ_eq_ρ, Rep.trivial_def (x 0)⁻¹,
    finsupp.llift_apply A k k],
end

/-- Auxiliary lemma for defining group cohomology, used to show that the isomorphism
`diagonal_hom_equiv` commutes with the differentials in two complexes which compute
group cohomology. -/
lemma diagonal_hom_equiv_symm_partial_prod_succ
  (f : (fin n → G) → A) (g : fin (n + 1) → G) (a : fin (n + 1)) :
  ((diagonal_hom_equiv n A).symm f).hom (finsupp.single (fin.partial_prod g ∘ a.succ.succ_above) 1)
    = f (fin.mul_nth (a : ℕ) g) :=
begin
  simp only [diagonal_hom_equiv_symm_apply, fin.coe_succ, function.comp_app,
    fin.succ_succ_above_zero, fin.partial_prod_zero, map_one, fin.coe_eq_cast_succ,
    fin.succ_succ_above_succ, linear_map.one_apply, fin.partial_prod_succ],
  congr,
  ext,
  by_cases (x : ℕ) < a,
  { rw [fin.succ_above_below, fin.succ_above_below, inv_mul_cancel_left, fin.mul_nth_lt_apply _ h],
    { refl },
    { assumption },
    { rw [fin.cast_succ_lt_iff_succ_le, fin.succ_le_succ_iff, fin.le_iff_coe_le_coe],
      exact le_of_lt h }},
  { by_cases hx : (x : ℕ) = a,
    { rw [fin.mul_nth_eq_apply _ hx, fin.succ_above_below, fin.succ_above_above,
        fin.cast_succ_fin_succ, fin.partial_prod_succ, mul_assoc,
        inv_mul_cancel_left, fin.add_nat_one],
      { refl },
      { simpa only [fin.le_iff_coe_le_coe, ←hx] },
      { rw [fin.cast_succ_lt_iff_succ_le, fin.succ_le_succ_iff, fin.le_iff_coe_le_coe],
        exact le_of_eq hx }},
    { rw [fin.mul_nth_neg_apply _ h hx, fin.succ_above_above, fin.succ_above_above,
        fin.partial_prod_succ, fin.cast_succ_fin_succ, fin.partial_prod_succ, inv_mul_cancel_left,
        fin.add_nat_one],
      { exact not_lt.1 h },
      { rw [fin.le_iff_coe_le_coe, fin.coe_succ],
        exact nat.succ_le_of_lt (lt_of_le_of_ne (not_lt.1 h) (ne.symm hx)) }}}
end

end Rep
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
  ((forget₂ (Rep k G) _).obj $ Rep.trivial k G k)) :=
(homotopy_equiv.of_iso (comp_forget_augmented_iso k G).symm).trans $
  (simplicial_object.augmented.extra_degeneracy.homotopy_equiv
    (extra_degeneracy_comp_forget_augmented_to_Module k G)).trans
  (homotopy_equiv.of_iso $ (chain_complex.single₀ (Module.{u} k)).map_iso
    (@finsupp.linear_equiv.finsupp_unique k k _ _ _ (⊤_ (Type u))
      types.terminal_iso.to_equiv.unique).to_Module_iso)

/-- The hom of `k`-linear `G`-representations `k[G¹] → k` sending `∑ nᵢgᵢ ↦ ∑ nᵢ`. -/
def ε : Rep.of_mul_action k G (fin 1 → G) ⟶ Rep.trivial k G k :=
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
  (Rep.trivial k G k) :=
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
  ProjectiveResolution (Rep.trivial k G k) :=
(ε_to_single₀ k G).to_single₀_ProjectiveResolution (X_projective k G)

instance : enough_projectives (Rep k G) :=
Rep.equivalence_Module_monoid_algebra.enough_projectives_iff.2
  (Module.Module_enough_projectives.{u})

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is a trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
standard resolution of `k` called `group_cohomology.resolution k G`. -/
def group_cohomology.Ext_iso (V : Rep k G) (n : ℕ) :
  ((Ext k (Rep k G) n).obj (opposite.op $ Rep.trivial k G k)).obj V ≅
    (((((linear_yoneda k (Rep k G)).obj V).right_op.map_homological_complex _).obj
      (group_cohomology.resolution k G)).homology n).unop :=
by let := (((linear_yoneda k (Rep k G)).obj V).right_op.left_derived_obj_iso
  n (group_cohomology.ProjectiveResolution k G)).unop.symm; exact this
