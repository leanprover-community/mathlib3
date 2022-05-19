/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import representation_theory.Rep
import representation_theory.basic

/-!
# The `k[G]`-module `k[Gⁿ⁺¹]` is free

This file proves `k[Gⁿ⁺¹]` is a free `k[G]`-module, where `k` is a commutative ring, `G` is a
group, and the module structure is induced by the diagonal action of `G` on `Gⁿ⁺¹.` We do this by
defining a `k[G]`-linear isomorphism with the free `k[G]`-module on the set of orbits of the
diagonal action of `G` on `Gⁿ⁺¹`.

The freeness of these modules means we can use them to build a projective resolution of the
(trivial) `k[G]`-module `k`, which is useful in group cohomology.

## Main definitions

  * mul_action_to_ρ
  * mul_action_to_Rep
  * to_basis
  * of_basis
  * basis (CHANGE WHEN I'VE CHANGED THESE NAMES....)

## Implementation notes

We bundle the type `k[Gⁿ]` - or more generally `k[H]` when `H` has `G`-action - and the
`k[G]`-module structure together as a term of type `Rep k G`, and we call it
`mul_action_to_Rep k G H.` The representation `ρ: G →* End(k[H])` is the induced by the `G`-action
on `H`. This is so we only define a `k[G]`-module instance on `mul_action_to_Rep k G H` and not
directly on `monoid_algebra k H`, which could cause diamonds.

-/

noncomputable theory
universes v u
variables {k G : Type u} [comm_ring k]

open monoid_algebra (lift) (of)

namespace Rep
section

variables [monoid G]

--will move to representation_theory.Rep
/-- A term of type `Rep k G` has the natural structure of a `k[G]`-module, with an element
`g : G` acting by `g • x = (ρ g) x` -/
instance module' [monoid G] (V : Rep k G) : module (monoid_algebra k G) V :=
representation.as_module V.ρ

lemma smul_def [monoid G] {V : Type u} [add_comm_group V]
  [module k V] {ρ : representation k G V} (g : monoid_algebra k G) (x : Rep.of ρ) :
  g • x = lift k G _ ρ g x := rfl

instance Rep.smul_comm_class {V : Type u} [add_comm_group V] [module k V]
  (ρ : representation k G V) :
  smul_comm_class (monoid_algebra k G) k (Rep.of ρ) :=
@has_scalar.comp.smul_comm_class _ (monoid_algebra k G) (Rep.of ρ) k _ _ _ _

instance Rep.is_scalar_tower {V : Type u} [add_comm_group V] [module k V]
  (ρ : representation k G V) :
  is_scalar_tower k (monoid_algebra k G) (Rep.of ρ) :=
{ smul_assoc := λ x y z, by
    simp only [Rep.smul_def, alg_hom.map_smul, linear_map.smul_apply] }

variables (k G) (n : ℕ)

/-- Given monoids `G, H`, a `G`-action on `H` induces a representation `G →* End(k[H])` in the
natural way. -/
@[simps] def mul_action_to_ρ (H : Type*) [monoid H] [mul_action G H] :
  representation k G (monoid_algebra k H) :=
{ to_fun := λ g, finsupp.lmap_domain k k ((•) g),
  map_one' := by { ext x y, dsimp, simp },
  map_mul' := λ x y, by { ext z w, simp [mul_smul] }}

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G.` -/
abbreviation mul_action_to_Rep (H : Type u) [monoid H] [mul_action G H] :
  Rep k G := Rep.of (mul_action_to_ρ k G H)

variables {k G}

lemma single_smul_single {H : Type u} [monoid H] [mul_action G H]
  (g : G) (x : H) (r s : k) :
  ((•) : monoid_algebra k G → mul_action_to_Rep k G H → mul_action_to_Rep k G H)
  (finsupp.single g r) (finsupp.single x s) =
  finsupp.single (g • x) (r * s) :=
begin
  rw [Rep.smul_def, monoid_algebra.lift_single],
  dsimp,
  rw [finsupp.map_domain_single, finsupp.smul_single'],
end

lemma of_smul_of {H : Type u} [monoid H] [mul_action G H] (g : G) (x : H) :
  (monoid_algebra.of k G g • monoid_algebra.of k H x : mul_action_to_Rep k G H)
    = monoid_algebra.of k H (g • x) :=
by simp only [monoid_algebra.of_apply, single_smul_single, one_mul]

-- terrible name....
lemma map_smul_of_map_smul_of {H : Type u} [monoid H]
  (ρ : representation k G (monoid_algebra k H))
  {P : Type u} [add_comm_monoid P] [module k P]
  [module (monoid_algebra k G) P] [is_scalar_tower k (monoid_algebra k G) P]
  (f : Rep.of ρ →ₗ[k] P)
  (h : ∀ (g : G) (x : H), f (monoid_algebra.of k G g • (monoid_algebra.of k H x))
    = monoid_algebra.of k G g • f (monoid_algebra.of k H x))
  (g : monoid_algebra k G) (x : Rep.of ρ) : f (g • x) = g • f x :=
begin
  refine (monoid_algebra.equivariant_of_linear_of_comm f _).map_smul _ _,
  intros a b,
  refine b.induction_on (by exact h a) _ _,
  { intros s t hs ht,
    simp only [smul_add, f.map_add, hs, ht] },
  { intros r s hs,
    rw [smul_comm (_ : monoid_algebra k G), f.map_smul, hs,
      smul_comm _ (_ : monoid_algebra k G), f.map_smul];
    { apply_instance }}
end

variables (k G)

-- not sure where to put this, or how much to generalise it
/-- The hom `Gⁿ →* Gⁿ⁺¹` sending `(g₁, ..., gₙ) ↦ (1, g₁, ..., gₙ)` -/
def cons_one_mul_hom : (fin n → G) →* (fin (n + 1) → G) :=
{ to_fun := @fin.cons n (λ i, G) 1,
  map_one' := funext $ λ x, fin.induction_on x rfl
    (λ i ih, fin.cons_succ _ _ _),
  map_mul' := λ x y, funext $ λ i, fin.induction_on i (one_mul _).symm
    (λ x hx, by simp only [fin.cons_succ, pi.mul_apply]) }

/-- The `k`-algebra hom sending `k[Gⁿ] → k[Gⁿ⁺¹]` sending `(g₁, ..., gₙ) ↦ (1, g₁, ..., gₙ)` -/
def cons_one : monoid_algebra k (fin n → G) →ₐ[k] monoid_algebra k (fin (n + 1) → G) :=
monoid_algebra.map_domain_alg_hom k k (cons_one_mul_hom G n)

variables {k G n}

lemma cons_one_of (g : fin n → G) :
  cons_one k G n (monoid_algebra.of k _ g) = monoid_algebra.of k
    (fin (n + 1) → G) (fin.cons 1 g) :=
finsupp.map_domain_single

end

variables (k G) [group G] (n : ℕ)

/-- The quotient of `Gⁿ⁺¹` by the diagonal action of `G` -/
abbreviation orbit_quot := quotient (mul_action.orbit_rel G (fin (n + 1) → G))

instance : is_scalar_tower k (monoid_algebra k G) (orbit_quot G n →₀ monoid_algebra k G) :=
finsupp.is_scalar_tower _ _

-- not sure how to name; should probably be in the monoid_algebra namespace instead
/-- The map sending `g = (g₀, ..., gₙ) : k[Gⁿ⁺¹]` to `g₀ • ⟦g⟧`, as an element of the free
`k[G]`-module on the set `Gⁿ⁺¹` modulo the diagonal action of `G`. -/
def to_basis_aux : monoid_algebra k (fin (n + 1) → G) →ₗ[k]
  (orbit_quot G n →₀ monoid_algebra k G) :=
(@finsupp.lmap_domain (fin (n + 1) → G) (monoid_algebra k G) k
 _ _ _ (orbit_quot G n) quotient.mk').comp
(finsupp.lift (monoid_algebra (monoid_algebra k G) (fin (n + 1) → G))
  k (fin (n + 1) → G) $ λ g, finsupp.single g (finsupp.single (g 0) 1))

variables {k G n}

lemma to_basis_single (g : fin (n + 1) → G) (r : k) :
  to_basis_aux k G n (finsupp.single g r)
    = finsupp.single (quotient.mk' g : orbit_quot G n) (finsupp.single (g 0) r) :=
by simp [to_basis_aux]

variables (k G n)

/-- The `k[G]`-linear map on `k[Gⁿ⁺¹]` sending `g` to `g₀ • ⟦g⟧` as an element of the free
`k[G]`-module on the set `Gⁿ⁺¹` modulo the diagonal action of `G`. -/
def to_basis : mul_action_to_Rep k G (fin (n + 1) → G) →ₗ[monoid_algebra k G]
  (orbit_quot G n →₀ monoid_algebra k G) :=
monoid_algebra.equivariant_of_linear_of_comm (to_basis_aux k G n) $ λ h y,
begin
  refine map_smul_of_map_smul_of _ _ (λ g x, _) _ _,
  rw of_smul_of,
  simp [to_basis_single, @quotient.sound' _ (mul_action.orbit_rel G (fin (n + 1) → G))
     _ _ (set.mem_range_self g)],
end

/-- Inverse of `to_basis` from the free `k[G]`-module on `Gⁿ⁺¹/G` to `k[Gⁿ⁺¹]`,
sending `⟦g⟧ ∈ Gⁿ⁺¹/G` to `g₀⁻¹ • g ∈ k[Gⁿ⁺¹]` -/
def of_basis : (orbit_quot G n →₀ monoid_algebra k G)
  →ₗ[monoid_algebra k G] mul_action_to_Rep k G (fin (n + 1) → G) :=
finsupp.lift (mul_action_to_Rep k G (fin (n + 1) → G)) (monoid_algebra k G) (orbit_quot G n)
  (λ y, quotient.lift_on' y (λ x, monoid_algebra.of _ _ ((x 0)⁻¹ • x)) $
  begin
    rintros a b ⟨c, rfl⟩,
    dsimp,
    congr' 1,
    ext i,
    simp [mul_assoc]
  end)

variables {k G n}

lemma basis_left_inv (x : mul_action_to_Rep k G (fin (n + 1) → G)) :
  of_basis k G n (to_basis k G n x) = x :=
begin
  refine add_monoid_hom.ext_iff.1 (@finsupp.add_hom_ext _ _ _ _ _
    ((of_basis k G n).comp $ to_basis k G n).to_add_monoid_hom
     (add_monoid_hom.id _) (λ g y, _)) x,
  dsimp [of_basis],
  erw to_basis_single,
  simp [single_smul_single, smul_inv_smul],
end

lemma basis_right_inv (x : orbit_quot G n →₀ monoid_algebra k G) :
  to_basis k G n (of_basis k G n x) = x :=
begin
  refine add_monoid_hom.ext_iff.1 (@finsupp.add_hom_ext _ _ _ _ _
    ((to_basis k G n).comp $ of_basis k G n).to_add_monoid_hom
     (add_monoid_hom.id _) (λ a b, quotient.induction_on' a $ λ c, _)) x,
  dsimp [of_basis],
  simp only [quotient.lift_on'_mk', zero_smul, monoid_algebra.of_apply,
    finsupp.sum_single_index, linear_map.map_smul, finsupp.lift_apply],
  erw to_basis_single,
  simp only [finsupp.smul_single', smul_eq_mul, pi.smul_apply, mul_left_inv],
  erw mul_one,
  congr' 1,
  exact quotient.sound' (mul_action.mem_orbit _ _)
end

variables (k G n)

/-- An isomorphism of `k[Gⁿ⁺¹]` with the free `k[G]`-module on the set `Gⁿ⁺¹`
  modulo the diagonal action of `G`, given by `to_basis`. -/
def basis : basis (orbit_quot G n)
  (monoid_algebra k G) (mul_action_to_Rep k G (fin (n + 1) → G)) :=
{ repr :=
  { inv_fun := of_basis k G n,
    left_inv := basis_left_inv,
    right_inv := basis_right_inv, ..to_basis _ G n } }

instance  : module.free (monoid_algebra k G) (mul_action_to_Rep k G (fin (n + 1) → G)) :=
module.free.of_basis (basis k G n)

end Rep
