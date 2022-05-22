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
(mainly) a group, and the module structure is induced by the diagonal action of `G` on `Gⁿ.`

In particular, we define `k[G]`-linear maps between `k[Gⁿ⁺¹]` and `k[G] ⊗ₖ k[Gⁿ]` which we will
later show define an isomorphism. From this we will deduce that `k[Gⁿ⁺¹]` is free over `k[G]`.

The freeness of these modules means we can use them to build a projective resolution of the
(trivial) `k[G]`-module `k`, which is useful in group cohomology.

## Main definitions

  * mul_action_to_ρ
  * mul_action_to_Rep
  * to_tensor
  * of_tensor

## Implementation notes

We bundle the type `k[Gⁿ]` - or more generally `k[H]` when `H` has `G`-action - and the
`k[G]`-module structure together as a term of type `Rep k G`, and we call it
`mul_action_to_Rep k G H.` The representation `ρ: G →* End(k[H])` is then induced by the `G`-action
on `H`. This is so we only define a `k[G]`-module instance on `mul_action_to_Rep k G H` and not
directly on `monoid_algebra k H`, which could cause diamonds.

-/

noncomputable theory
universes v u
variables {k G : Type u} [comm_ring k]

open monoid_algebra
namespace Rep

section
variables [monoid G]

/- Not sure where to put the next several things; either `representation_theory.Rep` or
`representation_theory.basic`, neither of which import the other. -/

/-- A term of type `Rep k G` has the natural structure of a `k[G]`-module, with an element
`g : G` acting by `g • x = (ρ g) x` -/
instance module' (V : Rep k G) : module (monoid_algebra k G) V :=
representation.as_module V.ρ

variables {V : Type u} [add_comm_group V] [module k V] {ρ : representation k G V}

lemma smul_def (g : monoid_algebra k G) (x : Rep.of ρ) : g • x = lift k G _ ρ g x := rfl

@[simp] lemma single_smul (g : G) (r : k) (x : Rep.of ρ) :
  ((•) : monoid_algebra k G → Rep.of ρ → Rep.of ρ)
    (finsupp.single g r : monoid_algebra k G) x = r • ρ g x :=
by rw [smul_def, lift_single]; refl

instance : smul_comm_class (monoid_algebra k G) k (Rep.of ρ) := has_scalar.comp.smul_comm_class _

instance : is_scalar_tower k (monoid_algebra k G) (Rep.of ρ) :=
{ smul_assoc := λ x y z, by simp only [smul_def, alg_hom.map_smul, linear_map.smul_apply] }

variables (k G) (H : Type u) [mul_action G H]

/-- A `G`-action on `H` induces a representation `G →* End(k[H])` in the natural way. -/
@[simps] def mul_action_to_ρ : representation k G (monoid_algebra k H) :=
{ to_fun := λ g, finsupp.lmap_domain k k ((•) g),
  map_one' := by { ext x y, dsimp, simp },
  map_mul' := λ x y, by { ext z w, simp [mul_smul] }}

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G.` -/
abbreviation mul_action_to_Rep : Rep k G := Rep.of (mul_action_to_ρ k G H)

variables {k G H}

@[simp] lemma single_smul_single (g : G) (x : H) (r s : k) :
  ((•) : monoid_algebra k G → mul_action_to_Rep k G H → mul_action_to_Rep k G H)
  (finsupp.single g r) (finsupp.single x s) = finsupp.single (g • x) (r * s) :=
by simp

lemma of_smul_of [mul_one_class H] (g : G) (x : H) :
  (monoid_algebra.of k G g • monoid_algebra.of k H x : mul_action_to_Rep k G H)
    = monoid_algebra.of k H (g • x) := by simp

-- terrible name....
lemma map_smul_of_map_smul_of {H : Type u} [monoid H] (ρ : representation k G (monoid_algebra k H))
  {P : Type u} [add_comm_monoid P] [module k P] [module (monoid_algebra k G) P]
  [is_scalar_tower k (monoid_algebra k G) P] (f : Rep.of ρ →ₗ[k] P)
  (h : ∀ (g : G) (x : H), f (monoid_algebra.of k G g • (monoid_algebra.of k H x))
    = monoid_algebra.of k G g • f (monoid_algebra.of k H x))
  (g : monoid_algebra k G) (x : Rep.of ρ) : f (g • x) = g • f x :=
(equivariant_of_linear_of_comm f (by
 { intros a b,
   exact b.induction_on (by exact h a) (by intros; simp only [smul_add, map_add, *])
   (λ r s hs, by rw [smul_comm (_ : monoid_algebra k G), f.map_smul, hs,
      smul_comm _ (_ : monoid_algebra k G), f.map_smul]; { apply_instance })})).map_smul _ _

variables {n : ℕ}

-- No idea what to call these or where to put them; would move them, but then they can't be private.
/-- Sends `(g₁, ..., gₙ) ↦ (1, g₁, g₁g₂, ..., g₁...gₙ)` -/
private def to_prod (f : fin n → G) (i : fin (n + 1)) : G :=
((list.of_fn f).take i).prod

@[simp] private lemma to_prod_zero (f : fin n → G) :
  to_prod f 0 = 1 :=
by simp [to_prod]

private lemma to_prod_succ (f : fin n → G) (j : fin n) :
  to_prod f j.succ = to_prod f j.cast_succ * (f j) :=
by simp [to_prod, list.take_succ, list.of_fn_nth_val, dif_pos j.is_lt, ←option.coe_def]

private lemma to_prod_succ' (f : fin (n + 1) → G) (j : fin (n + 1)) :
  to_prod f j.succ = f 0 * to_prod (fin.tail f) j :=
by simpa [to_prod]

end

variables [group G] (n : ℕ) (k G)
open_locale tensor_product

/-- The `k`-linear map from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` sending `(g₀, ..., gₙ)`
to `g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)` -/
def to_tensor_aux : mul_action_to_Rep k G (fin (n + 1) → G) →ₗ[k] monoid_algebra k G
  ⊗[k] mul_action_to_Rep k G (fin n → G) :=
finsupp.lift (monoid_algebra k G ⊗[k] mul_action_to_Rep k G (fin n → G)) k (fin (n + 1) → G)
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

variables (k G n)

/-- The `k[G]`-linear map from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` sending `(g₀, ..., gₙ)`
to `g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)` -/
def to_tensor : mul_action_to_Rep k G (fin (n + 1) → G) →ₗ[monoid_algebra k G] monoid_algebra k G
  ⊗[k] mul_action_to_Rep k G (fin n → G) :=
equivariant_of_linear_of_comm (to_tensor_aux k G n) $ λ g x, map_smul_of_map_smul_of _ _
  (λ h x, by simp [of_smul_of, single_smul_single, to_tensor_aux_single,
    tensor_product.smul_tmul', mul_assoc]) _ _

variables {k G n}

@[simp] lemma to_tensor_single (f : fin (n + 1) → G) (m : k) :
  to_tensor k G n (finsupp.single f m) =
    finsupp.single (f 0) m ⊗ₜ finsupp.single (λ i, (f i)⁻¹ * f i.succ) 1 :=
to_tensor_aux_single _ _

variables (k G n)

/-- The `k`-linear map from `k[G] ⊗ₖ k[Gⁿ]` to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)` -/
def of_tensor_aux : monoid_algebra k G ⊗[k] mul_action_to_Rep k G (fin n → G)
    →ₗ[k] mul_action_to_Rep k G (fin (n + 1) → G) :=
tensor_product.lift (finsupp.lift _ _ _ $ λ g, finsupp.lift _ _ _
  (λ f, monoid_algebra.of _ (fin (n + 1) → G) (g • to_prod f)))

variables {k G n}

private lemma of_tensor_aux_single (g : G) (m : k) (x : mul_action_to_Rep k G (fin n → G)) :
  of_tensor_aux k G n ((finsupp.single g m) ⊗ₜ x) = finsupp.lift (mul_action_to_Rep k G
    (fin (n + 1) → G)) k (fin n → G) (λ f, finsupp.single (g • to_prod f) m) x :=
by simp [of_tensor_aux, finsupp.sum_single_index, finsupp.smul_sum, mul_comm m]

variables (k G n)

/-- The `k[G]`-linear map from `k[G] ⊗ₖ k[Gⁿ]` to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)` -/
def of_tensor : monoid_algebra k G ⊗[k] mul_action_to_Rep k G (fin n → G)
  →ₗ[monoid_algebra k G] mul_action_to_Rep k G (fin (n + 1) → G) :=
monoid_algebra.equivariant_of_linear_of_comm (of_tensor_aux k G n) $ λ g x,
begin
  refine tensor_product.induction_on x (by simp) (λ x y, _) (λ y z hz hy, by simp only
    [smul_add, linear_map.map_add, hy, hz]),
  { erw [←finsupp.sum_single x, tensor_product.sum_tmul],
    simp only [finset.smul_sum, linear_map.map_sum],
    refine finset.sum_congr rfl (λ f hf, _),
    simp only [tensor_product.smul_tmul', smul_eq_mul, monoid_algebra.single_mul_single, one_mul,
      of_tensor_aux_single, ←linear_map.map_smul, finsupp.lift_apply, finsupp.smul_sum],
    exact finsupp.sum_congr (λ j hj, by rw [smul_comm (_ : monoid_algebra k G), single_smul_single,
      one_mul, smul_smul]; apply_instance) },
end

variables {k G n}

@[simp] lemma of_tensor_single (g : G) (m : k) (x : mul_action_to_Rep k G (fin n → G)) :
  of_tensor k G n ((finsupp.single g m) ⊗ₜ x) = finsupp.lift (mul_action_to_Rep k G
    (fin (n + 1) → G)) k (fin n → G) (λ f, finsupp.single (g • to_prod f) m) x :=
of_tensor_aux_single _ _ _

lemma of_tensor_single' (g : monoid_algebra k G) (x : fin n → G) (r : k) :
  of_tensor k G n (g ⊗ₜ finsupp.single x r) =
    finsupp.lift _ k G (λ a, finsupp.single (a • to_prod x) r) g :=
by simp [of_tensor, of_tensor_aux]

end Rep
