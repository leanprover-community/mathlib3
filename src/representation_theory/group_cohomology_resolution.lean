/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import representation_theory.Rep
import representation_theory.basic

/-!
# The structure of the `k[G]`-module `k[Gⁿ]`

This file contains facts about an important `k[G]`-module structure on `k[Gⁿ]`, where `k` is a
commutative ring and `G` is a group. The module structure arises from the representation
`G →* End(k[Gⁿ])` induced by the diagonal action of `G` on `Gⁿ.`

In particular, we define an isomorphism of `k`-linear `G`-representations between `k[Gⁿ⁺¹]` and
`k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`).

This allows us to define a `k[G]`-basis on `k[Gⁿ⁺¹]`, by mapping the natural `k[G]`-basis of
`k[G] ⊗ₖ k[Gⁿ]` along the isomorphism.

## Main definitions

 * `group_cohomology.resolution.to_tensor`
 * `group_cohomology.resolution.of_tensor`
 * `Rep.of_mul_action`
 * `group_cohomology.resolution.equiv_tensor`
 * `group_cohomology.resolution.of_mul_action_basis`

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

universes u

variables {k G : Type u} [comm_ring k] {n : ℕ}

open_locale tensor_product

local notation `Gⁿ` := fin n → G
local notation `Gⁿ⁺¹` := fin (n + 1) → G

namespace group_cohomology.resolution

open finsupp (hiding lift) fin (partial_prod) representation

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

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G`. -/
abbreviation _root_.Rep.of_mul_action (G : Type u) [monoid G] (H : Type u) [mul_action G H] :
  Rep k G :=
Rep.of $ representation.of_mul_action k G H

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

-- not quite sure which simp lemmas to make here
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
  (fin n → G) (⟨linear_equiv.refl k _⟩)) (of_mul_action_basis_aux k G n)

lemma of_mul_action_free :
  module.free (monoid_algebra k G) (of_mul_action k G (fin (n + 1) → G)).as_module :=
module.free.of_basis (of_mul_action_basis k G n)

end group_cohomology.resolution
