/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import algebraic_topology.alternating_face_map_complex
import algebraic_topology.cech_nerve
import algebraic_topology.extra_degeneracy
import algebraic_topology.thingy
import category_theory.abelian.exact
import representation_theory.basic
import representation_theory.Rep
import representation_theory.homology_lemmas

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
by the universal cover of the classifying space of `G`. We prove this `G`-set is isomorphic to the
Čech nerve of the natural arrow of `G`-sets `G ⟶ {pt}`.

## Main definitions

 * `group_cohomology.resolution.to_tensor`
 * `group_cohomology.resolution.of_tensor`
 * `Rep.of_mul_action`
 * `group_cohomology.resolution.equiv_tensor`
 * `group_cohomology.resolution.of_mul_action_basis`
 * `classifying_space_universal_cover`
 * `classifying_space_universal_cover.cech_nerve_iso`
 * `group_cohomology.resolution`

## TODO

 * Use the freeness of `k[Gⁿ⁺¹]` to build a projective resolution of the (trivial) `k[G]`-module
   `k`, and so develop group cohomology.

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

universes u v u' v' w w' t t'

variables {k G : Type u} [comm_ring k] {n : ℕ}

open_locale tensor_product
open category_theory

local notation `Gⁿ` := fin n → G
local notation `Gⁿ⁺¹` := fin (n + 1) → G

namespace group_cohomology.resolution

open finsupp (hiding lift) fin (partial_prod) representation

section basis
variables (k G n) [group G]
/-
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
-/
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

open category_theory.limits category_theory.arrow
variables (G) [monoid G] (m : simplex_categoryᵒᵖ)

variables (ι : Type w) [fintype ι] {C : Type u} [category.{v} C] [has_finite_products C]
  [has_terminal C] (X : C)

/-- The diagram `option ι ⥤ C` sending `none` to the terminal object and `some j` to `X`. -/
def wide_cospan : wide_pullback_shape ι ⥤ C :=
wide_pullback_shape.wide_cospan (terminal C) (λ i : ι, X) (λ i, terminal.from X)

instance unique_to_wide_cospan_none (Y : C) : unique (Y ⟶ (wide_cospan ι X).obj none) :=
by unfold wide_cospan; dsimp; apply_instance

/-- The product `Xᶥ` is the vertex of a cone on `wide_cospan X m`. -/
def wide_cospan.limit_cone : limit_cone (wide_cospan ι X) :=
{ cone :=
  { X := ∏ (λ i : ι, X),
    π :=
    { app := λ X, option.cases_on X (terminal.from _) (λ i, limit.π _ ⟨i⟩),
      naturality' := λ i j f,
      begin
      cases f,
      { cases i,
        all_goals { dsimp, simp }},
      { dsimp,
        simp only [terminal.comp_from],
        exact subsingleton.elim _ _ }
      end } },
  is_limit :=
  { lift := λ s, limits.pi.lift (λ j, s.π.app (some j)),
    fac' := λ s j, option.cases_on j (subsingleton.elim _ _) (λ j, limit.lift_π _ _),
    uniq' := λ s f h,
    begin
      ext j,
      dunfold limits.pi.lift,
      rw limit.lift_π,
      dsimp,
      rw ←h (some j.as),
      congr,
      ext,
      refl,
    end } }

instance has_wide_pullback : has_wide_pullback (arrow.mk (terminal.from X)).right
  (λ i : ι, (arrow.mk (terminal.from X)).left)
  (λ i, (arrow.mk (terminal.from X)).hom) :=
⟨⟨wide_cospan.limit_cone ι X⟩⟩

/-- I want to say Gⁿ with diagonal action is the product of n copies of G with left regular action
in Action (Type u) G, not sure this is the best way. -/
def diagonal_as_limit_cone (ι : Type v) (G : Type (max v u)) [monoid G] :
  limit_cone (discrete.functor (λ i : ι, Action.of_mul_action G G)) :=
{ cone :=
  { X := Action.of_mul_action G (ι → G),
    π :=
    { app := λ i, ⟨λ f, f i.as, λ g, by ext; refl⟩,
      naturality' := λ i j f, by { ext, discrete_cases, cases f, congr } } },
  is_limit :=
  { lift := λ s,
    { hom := λ x i, (s.π.app ⟨i⟩).hom x,
      comm' := λ g,
      begin
        ext,
        dsimp,
        exact congr_fun ((s.π.app ⟨j⟩).comm g) i,
      end },
    fac' := λ s j,
    begin
      ext,
      dsimp,
      rw discrete.mk_as,
    end,
    uniq' := λ s f h,
    begin
      ext x j,
      dsimp at *,
      rw ←h ⟨j⟩,
      congr,
    end } }

/-- The `m`th object of the Čech nerve of the `G`-set hom `G ⟶ {pt}` is isomorphic to `Gᵐ⁺¹` with
the diagonal action. -/
def cech_nerve_obj_iso :
  (cech_nerve (arrow.mk (terminal.from (Action.of_mul_action G G)))).obj m
    ≅ Action.of_mul_action G (fin (m.unop.len + 1) → G) :=
(is_limit.cone_point_unique_up_to_iso (limit.is_limit _) (wide_cospan.limit_cone
  (fin (m.unop.len + 1)) (Action.of_mul_action G G)).2).trans $
  limit.iso_limit_cone (diagonal_as_limit_cone _ _)

/-- The Čech nerve of the `G`-set hom `G ⟶ {pt}` is naturally isomorphic to `EG`, the universal
cover of the classifying space of `G` as a simplicial `G`-set. -/
def cech_nerve_iso : cech_nerve (arrow.mk (terminal.from (Action.of_mul_action G G)))
  ≅ classifying_space_universal_cover G :=
(@nat_iso.of_components _ _ _ _ (classifying_space_universal_cover G)
  (cech_nerve (arrow.mk (terminal.from (Action.of_mul_action G G))))
(λ n, (cech_nerve_obj_iso G n).symm) $ λ m n f,  wide_pullback.hom_ext
  (λ j, (arrow.mk (terminal.from (Action.of_mul_action G G))).hom) _ _
(λ j, begin
  simp only [category.assoc],
  dsimp [cech_nerve_obj_iso],
  rw [wide_pullback.lift_π, category.assoc],
  erw [limit.cone_point_unique_up_to_iso_hom_comp (wide_cospan.limit_cone _ _).2,
    limit.cone_point_unique_up_to_iso_hom_comp (diagonal_as_limit_cone _ _).2, category.assoc],
  dunfold wide_pullback.π,
  erw [limit.cone_point_unique_up_to_iso_inv_comp, limit.iso_limit_cone_inv_π],
  refl,
end)
(@subsingleton.elim _ (@unique.subsingleton _ (limits.unique_to_terminal _)) _ _)).symm

/-- The `m`th object of the Čech nerve of the function
`G ⟶ {pt}` is isomorphic to the set `Gᵐ⁺¹`. -/
def forget_nerve_iso_obj :
  (cech_nerve (arrow.mk $ terminal.from G)).obj m ≅ (fin (m.unop.len + 1) → G) :=
(limit.iso_limit_cone (wide_cospan.limit_cone _ _)).trans $ types.product_iso _

/-- The Čech nerve of the function `G ⟶ {pt}` is naturally isomorphic to `EG`, the universal
cover of the classifying space of `G` as a simplicial set. -/
def forget_nerve_iso : cech_nerve (arrow.mk $ terminal.from G)
  ≅ classifying_space_universal_cover G ⋙ forget _ :=
(@nat_iso.of_components _ _ _ _ (classifying_space_universal_cover G ⋙ forget _)
  (cech_nerve (arrow.mk $ terminal.from G))
  (λ m, (forget_nerve_iso_obj G m).symm) $
λ m n f, wide_pullback.hom_ext (λ j, (arrow.mk $ terminal.from G).hom) _ _
(λ j, begin
  simp only [category.assoc],
  dsimp [forget_nerve_iso_obj],
  rw [wide_pullback.lift_π, category.assoc],
  erw [limit.cone_point_unique_up_to_iso_hom_comp (wide_cospan.limit_cone _ _).2,
    limit.cone_point_unique_up_to_iso_hom_comp (types.product_limit_cone _).2, category.assoc],
  dunfold wide_pullback.π,
  erw [limit.cone_point_unique_up_to_iso_inv_comp, limit.iso_limit_cone_inv_π],
  refl,
end)
(@subsingleton.elim _ (@unique.subsingleton _ (limits.unique_to_terminal _)) _ _)).symm


variables (k G)

def aug_cover : simplicial_object.augmented (Type u) :=
simplicial_object.augment (classifying_space_universal_cover G ⋙ forget _) (terminal _)
(terminal.from _) $ λ i g h, subsingleton.elim _ _

def aug_iso : (arrow.mk $ terminal.from G).augmented_cech_nerve ≅ aug_cover G :=
comma.iso_mk (forget_nerve_iso G) (iso.refl _) $
begin
  ext1, ext1,
  exact (@subsingleton.elim _ (@unique.subsingleton _ (limits.unique_to_terminal _)) _ _),
end

def split_epi : split_epi (arrow.mk $ terminal.from G).hom :=
{ section_ := λ x, (1 : G),
  id' := @subsingleton.elim _ (@unique.subsingleton _ (limits.unique_to_terminal _)) _ _ }

def extra_degen_nerve :
  simplicial_object.augmented.extra_degeneracy (arrow.mk $ terminal.from G).augmented_cech_nerve :=
augmented_cech_nerve.extra_degeneracy (arrow.mk $ terminal.from G) (split_epi G)

def extra_degen_cover :
  simplicial_object.augmented.extra_degeneracy (aug_cover G) :=
simplicial_object.augmented.extra_degeneracy.of_iso (aug_iso G) (extra_degen_nerve G)

def Module_cover : simplicial_object.augmented (Module.{u} k) :=
((simplicial_object.augmented.whiskering _ _).obj (Module.free k)).obj (aug_cover G)

def extra_degen_Module_cover :
  simplicial_object.augmented.extra_degeneracy (Module_cover k G) :=
(Module.free k).map_extra_degeneracy (aug_cover G) (extra_degen_cover G)

def resn := (algebraic_topology.alternating_face_map_complex (Rep k G)).obj
  (classifying_space_universal_cover G ⋙ (Rep.linearization k G).1.1)

def forget_resn := ((forget₂ (Rep k G) (Module.{u} k)).map_homological_complex _).obj (resn k G)

lemma forget_free_eq : forget (Action (Type u) (Mon.of G)) ⋙ Module.free.{u} k
  = (Rep.linearization k G).1.1 ⋙ forget₂ (Rep k G) (Module.{u} k) :=
category_theory.functor.ext (λ X, by refl) (λ X Y f, by ext; refl)

lemma functor.comp_assoc {A : Type u} [category.{v} A] {B : Type u'} [category.{v'} B]
  {C : Type w} [category.{w'} C] {D : Type t} [category.{t'} D]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) : (F ⋙ G) ⋙ H = F ⋙ G ⋙ H :=
begin
  refine category_theory.functor.ext _ _,
  intro, refl,
  intros,
  simp only [functor.comp_map, eq_to_hom_refl, category.comp_id, category.id_comp],

end

lemma eq_forget_resn : (algebraic_topology.alternating_face_map_complex.obj
  (simplicial_object.augmented.drop.obj (Module_cover k G))) = forget_resn k G :=
begin
  show algebraic_topology.alternating_face_map_complex.obj
    ((_ ⋙ _) ⋙ _) = _,
  rw [functor.comp_assoc, forget_free_eq, ←functor.comp_assoc],
  exact (category_theory.functor.congr_obj
    (algebraic_topology.map_alternating_face_map_complex _) _).symm,
end

def homotopy_equiv.of_iso {ι : Type*} {V : Type u} [category.{v} V] [preadditive V]
  {c : complex_shape ι} {C D : homological_complex V c} (f : C ≅ D) :
  homotopy_equiv C D :=
{ hom := f.hom,
  inv := f.inv,
  homotopy_hom_inv_id := homotopy.of_eq f.3,
  homotopy_inv_hom_id := homotopy.of_eq f.4 }

def homotopy_equiv.of_eq {ι : Type*} {V : Type u} [category.{v} V] [preadditive V]
  {c : complex_shape ι} {C D : homological_complex V c} (h : C = D) :
  homotopy_equiv C D := homotopy_equiv.of_iso (eq_to_iso h)

instance : unique (terminal (Type u)) := equiv.unique (types.terminal_iso).to_equiv

instance : unique ((@simplicial_object.augmented.point (Type u) _).obj (aug_cover G)) :=
equiv.unique (types.terminal_iso).to_equiv

def single_iso : (chain_complex.single₀ (Module k)).obj
  (simplicial_object.augmented.point.obj (Module_cover k G)) ≅
  (chain_complex.single₀ (Module k)).obj (Module.of k k) :=
homological_complex.hom.iso_of_components (λ i, nat.rec_on i
  (finsupp.linear_equiv.finsupp_unique k k (terminal (Type u))).to_Module_iso (λ j hj, iso.refl _)) $
begin
   intros i j hij,
   cases hij,
   ext,
   simp only [chain_complex.single₀_obj_X_d, comp_zero, zero_comp],
end

def forget_resn_homotopy_equiv : homotopy_equiv (forget_resn k G)
    ((chain_complex.single₀ (Module k)).obj (Module.of k k)) :=
(homotopy_equiv.of_eq (eq_forget_resn k G).symm).trans $
  (simplicial_object.augmented.extra_degeneracy.preadditive.homotopy_equivalence
  (extra_degen_Module_cover k G)).trans (homotopy_equiv.of_iso $ single_iso k G)

def resolution := (algebraic_topology.alternating_face_map_complex (Rep k G)).obj
  (classifying_space_universal_cover G ⋙ (Rep.linearization k G).1.1)

theorem forget_resn_exact (n : ℕ) :
  exact ((forget_resn k G).d (n + 2) (n + 1)) ((forget_resn k G).d (n + 1) n) :=
(preadditive.exact_iff_homology_zero _ _).2 ⟨(forget_resn k G).d_comp_d _ _ _,
  ⟨(chain_complex.succth _ _).symm.trans ((homology_obj_iso_of_homotopy_equiv
  (forget_resn_homotopy_equiv k G) _).trans homology_zero_zero)⟩⟩

variables {k G}

lemma ffs2 {k : Type u} [comm_ring k] {C D : chain_complex (Module.{u} k) ℕ}
  (H : C ≅ D) {i j : ℕ} (hij : (complex_shape.down ℕ).rel i j) :
  H.2.1 i ≫ C.d i j ≫ H.1.1 j = D.d i j :=
begin
  rw [←category.assoc, H.2.2 i j hij, category.assoc, ←homological_complex.comp_f,
    homological_complex.congr_hom H.4 j, homological_complex.id_f, category.comp_id],
end

instance ffs1 {k : Type u} [comm_ring k] (C D : chain_complex (Module.{u} k) ℕ)
  (H : C ≅ D) (i : ℕ) : is_iso (H.1.1 i) :=
⟨⟨H.2.1 i, homological_complex.congr_hom H.3 i, homological_complex.congr_hom H.4 i⟩⟩

instance ffs4  {k : Type u} [comm_ring k] (C D : chain_complex (Module.{u} k) ℕ)
  (H : C ≅ D) (i : ℕ) : is_iso (H.2.1 i) :=
⟨⟨H.1.1 i, homological_complex.congr_hom H.4 i, homological_complex.congr_hom H.3 i⟩⟩

lemma yeugh {k : Type u} [comm_ring k] {C D : chain_complex (Module.{u} k) ℕ}
  (H : C ≅ D) (i j l : ℕ) (hij : (complex_shape.down ℕ).rel i j) (hjl : (complex_shape.down ℕ).rel j l) :
  exact (C.d i j) (C.d j l) ↔ exact (D.d i j) (D.d j l) :=
begin
  rw [←ffs2 H hij, ←ffs2 H hjl, exact_iso_comp, ←category.assoc, exact_comp_iso],
  exact (exact_comp_hom_inv_comp_iff (homological_complex.hom.iso_app H j)).symm,
end

theorem noice (n : ℕ) :
  exact ((resolution k G).d (n + 2) (n + 1)) ((resolution k G).d (n + 1) n) :=
functor.exact_of_exact_map (forget₂ (Rep k G) (Module.{u} k)) (forget_resn_exact _ _ _)

end classifying_space_universal_cover
namespace group_cohomology.resolution

section differential
variables (k G)
/-- The `k`-linear map underlying the differential in the standard resolution of `k` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ)`. -/
def d (n : ℕ) : ((fin (n + 1) → G) →₀ k) →ₗ[k] ((fin n → G) →₀ k) :=
finsupp.lift ((fin n → G) →₀ k) k (fin (n + 1) → G) (λ g, (@finset.univ (fin (n + 1)) _).sum
  (λ p, finsupp.single (g ∘ p.succ_above) ((-1 : k) ^ (p : ℕ))))

variables {k G}

@[simp] lemma d_of {n : ℕ} (c : fin (n + 1) → G) :
  d k G n (finsupp.single c 1) = finset.univ.sum (λ p : fin (n + 1), finsupp.single
    (c ∘ p.succ_above) ((-1 : k) ^ (p : ℕ))) :=
by simp [d]

end differential
end group_cohomology.resolution
variables (k G) [monoid G]

/-- The standard resolution of `k` as a trivial representation, defined as the alternating
face map complex of a simplicial `k`-linear `G`-representation. -/
def group_cohomology.resolution := (algebraic_topology.alternating_face_map_complex (Rep k G)).obj
  (classifying_space_universal_cover G ⋙ (Rep.linearization k G).1.1)

namespace group_cohomology.resolution

/- Leaving this here for now - not sure it should exist or where it should go. Everything I tried
to avoid this lemma was messy or gave me weird errors. -/
lemma int_cast_smul {k V : Type*} [comm_ring k] [add_comm_group V] [module k V] (r : ℤ) (x : V) :
  (r : k) • x = r • x :=
algebra_map_smul k r x

/-- The `n`th object of the standard resolution of `k` is definitionally isomorphic to `k[Gⁿ⁺¹]`
equipped with the representation induced by the diagonal action of `G`. -/
def X_iso (n : ℕ) :
  (group_cohomology.resolution k G).X n ≅ Rep.of_mul_action k G (fin (n + 1) → G) := iso.refl _

/-- Simpler expression for the differential in the standard resolution of `k` as a
`G`-representation. It sends `(g₀, ..., gₙ₊₁) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ₊₁)`. -/
theorem d_eq (n : ℕ) :
  ((group_cohomology.resolution k G).d (n + 1) n).hom = d k G (n + 1) :=
begin
  ext x y,
  dsimp [group_cohomology.resolution],
  simpa [←@int_cast_smul k, simplicial_object.δ],
end

end group_cohomology.resolution
