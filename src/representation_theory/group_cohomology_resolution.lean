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

In particular, we define morphisms of `k`-linear `G`-representations between `k[Gⁿ⁺¹]` and
`k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`).

## Main definitions

 * `group_cohomology.resolution.to_tensor`
 * `group_cohomology.resolution.of_tensor`
 * `Rep.of_mul_action`

## TODO

 * Show that `group_cohomology.resolution.to_tensor` and `group_cohomology.resolution.of_tensor` are
   mutually inverse.
 * Use the above to deduce that `k[Gⁿ⁺¹]` is free over `k[G]`.
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
  erw [lift_apply, sum_single_index, tensor_product.smul_tmul'],
  { simp },
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
  dsimp,
  simp [of_mul_action_def, of_tensor_aux_single, mul_smul],
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

end group_cohomology.resolution
