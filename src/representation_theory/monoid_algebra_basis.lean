/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import representation_theory.Rep
import representation_theory.basic

/-!
# The structure of the `k[G]`-module `k[Gⁿ]`

This file contains API for the `k[G]`-module `k[Gⁿ]`, where `k` is a commutative ring, `G` is
a group, and we express the module structure as the representation `G →* End(k[Gⁿ])` induced by the
diagonal action of `G` on `Gⁿ.`

In particular, we define morphisms of `k`-linear `G`-representations between `k[Gⁿ⁺¹]` and
`k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) which we will later show
define an isomorphism. From this we will deduce that `k[Gⁿ⁺¹]` is free over `k[G]`.
The freeness of these modules means we can use them to build a projective resolution of the
(trivial) `k[G]`-module `k`, which is useful in group cohomology.

## Main definitions

  * representation.of_mul_action
  * Rep.of_mul_action
  * to_tensor
  * of_tensor

## Implementation notes

We express `k[G]`-module structures on a group `V` as `k`-linear representations of `G` on `V`, as
this simplifies some proofs and also makes it easier to work with different structures on the same
`V`. This is because `module` is a class, and there is only one notation for scalar multiplication,
`•`; representations, meanwhile, give us more flexibility, by avoiding typeclass inference.

We bundle the type `k[Gⁿ]` - or more generally `k[H]` when `H` has `G`-action - and the
representation together as a term of type `Rep k G`, and we call it `Rep.of_mul_action k G H.` This
is so we can talk about morphisms of representations.

-/

noncomputable theory
universes v u
variables (k G : Type u) [comm_ring k] (n : ℕ)

local notation `Gⁿ` := fin n → G
local notation `Gⁿ⁺¹` := fin (n + 1) → G

open monoid_algebra

namespace Rep
section monoid
variables [monoid G] (H : Type u) [mul_action G H]

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G.` -/
abbreviation of_mul_action : Rep k G := Rep.of (representation.of_mul_action k G H)

variables {k G n}

-- No idea what to call these or where to put them; would move them, but then they can't be private.
/-- Sends `(g₁, ..., gₙ) ↦ (1, g₁, g₁g₂, ..., g₁...gₙ)` -/
private def to_prod (f : fin n → G) (i : fin (n + 1)) : G :=
((list.of_fn f).take i).prod

@[simp] private lemma to_prod_zero (f : Gⁿ) :
  to_prod f 0 = 1 :=
by simp [to_prod]

private lemma to_prod_succ (f : Gⁿ) (j : fin n) :
  to_prod f j.succ = to_prod f j.cast_succ * (f j) :=
by simp [to_prod, list.take_succ, list.of_fn_nth_val, dif_pos j.is_lt, ←option.coe_def]

private lemma to_prod_succ' (f : Gⁿ⁺¹) (j : fin (n + 1)) :
  to_prod f j.succ = f 0 * to_prod (fin.tail f) j :=
by simpa [to_prod]

end monoid

variables [group G] (n)
open_locale tensor_product

/-- The `k`-linear map from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` sending `(g₀, ..., gₙ)`
to `g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)` -/
def to_tensor_aux :
  of_mul_action k G Gⁿ⁺¹ →ₗ[k] (G →₀ k) ⊗[k] (Gⁿ →₀ k) :=
finsupp.lift ((G →₀ k) ⊗[k] (Gⁿ →₀ k)) k Gⁿ⁺¹
  (λ x, finsupp.single (x 0) 1 ⊗ₜ[k] finsupp.single (λ i, (x i)⁻¹ * x i.succ) 1)

variables {k G n}

private lemma to_tensor_aux_single (f : fin (n + 1) → G) (m : k) :
  to_tensor_aux k G n (finsupp.single f m) =
    finsupp.single (f 0) m ⊗ₜ finsupp.single (λ i, (f i)⁻¹ * f i.succ) 1 :=
begin
  erw [finsupp.lift_apply, finsupp.sum_single_index, tensor_product.smul_tmul'],
  { simp },
  { simp },
end

private lemma to_tensor_aux_comm (g : G) (x : fin (n + 1) → G) :
  to_tensor_aux k G n (representation.of_mul_action k G Gⁿ⁺¹ g (finsupp.single x 1))
  = tensor_product.map (representation.of_mul_action k G G g) 1
    (to_tensor_aux k G n (finsupp.single x 1)) :=
by simp [representation.of_mul_action_apply', to_tensor_aux_single, mul_assoc, inv_mul_cancel_left]

variables (k G n)

/-- A hom of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)` -/
def to_tensor : of_mul_action k G Gⁿ⁺¹ ⟶ Rep.of
  ((representation.of_mul_action k G G).tprod (1 : G →* module.End k (Gⁿ →₀ k))) :=
{ hom := to_tensor_aux k G n,
  comm' := λ g, by ext; exact to_tensor_aux_comm _ _ }

variables {k G n}

@[simp] lemma to_tensor_single (f : fin (n + 1) → G) (m : k) :
  (to_tensor k G n).hom (finsupp.single f m) =
    finsupp.single (f 0) m ⊗ₜ finsupp.single (λ i, (f i)⁻¹ * f i.succ) 1 :=
to_tensor_aux_single _ _

variables (k G n)

/-- The `k`-linear map from `k[G] ⊗ₖ k[Gⁿ]` to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)` -/
def of_tensor_aux :
  monoid_algebra k G ⊗[k] (Gⁿ →₀ k) →ₗ[k] of_mul_action k G Gⁿ⁺¹ :=
tensor_product.lift (finsupp.lift _ _ _ $ λ g, finsupp.lift _ _ _
  (λ f, monoid_algebra.of _ Gⁿ⁺¹ (g • to_prod f)))

variables {k G n}

private lemma of_tensor_aux_single (g : G) (m : k) (x : (fin n → G) →₀ k) :
  of_tensor_aux k G n ((finsupp.single g m) ⊗ₜ x) = finsupp.lift (of_mul_action k G
    Gⁿ⁺¹) k Gⁿ (λ f, finsupp.single (g • to_prod f) m) x :=
by simp [of_tensor_aux, finsupp.sum_single_index, finsupp.smul_sum, mul_comm m]

private lemma of_tensor_aux_comm (g h : G) (x : fin n → G) :
  of_tensor_aux k G n (tensor_product.map (representation.of_mul_action k G G g)
    (1 : module.End k (Gⁿ →₀ k)) (finsupp.single h (1 : k) ⊗ₜ finsupp.single x (1 : k)))
  = representation.of_mul_action k G Gⁿ⁺¹ g (of_tensor_aux k G n
    (finsupp.single h 1 ⊗ₜ finsupp.single x 1)) :=
begin
  dsimp,
  simp [representation.of_mul_action_apply', of_tensor_aux_single, mul_smul],
end

variables (k G n)

/-- A hom of `k`-linear representations of `G` from `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)` -/
def of_tensor :
  Rep.of ((representation.of_mul_action k G G).tprod (1 : G →* module.End k (Gⁿ →₀ k)))
    ⟶ of_mul_action k G Gⁿ⁺¹ :=
{ hom := of_tensor_aux k G n,
  comm' := λ g, by { ext, congr' 1, exact (of_tensor_aux_comm _ _ _) }}

variables {k G n}

@[simp] lemma of_tensor_single (g : G) (m : k) (x : Gⁿ →₀ k) :
  (of_tensor k G n).hom ((finsupp.single g m) ⊗ₜ x) = finsupp.lift (of_mul_action k G
    Gⁿ⁺¹) k Gⁿ (λ f, finsupp.single (g • to_prod f) m) x :=
of_tensor_aux_single _ _ _

lemma of_tensor_single' (g : G →₀ k) (x : Gⁿ) (r : k) :
  (of_tensor k G n).hom (g ⊗ₜ finsupp.single x r) =
    finsupp.lift _ k G (λ a, finsupp.single (a • to_prod x) r) g :=
by simp [of_tensor, of_tensor_aux]

end Rep
