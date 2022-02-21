/-
Copyright (c) 2021 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import algebra.monoid_algebra.basic
import tactic.basic

/-!
# Group rings

This file defines the group ring `k[G]` of a group `G` with coefficients in a semiring `k`. A
`G`-module with a compatible `k`-module structure is an `k[G]`-module.

We develop an API allowing us to show `k[Gⁿ]` is a free `k[G]`-module for `n ≥ 1`. This
will be used to construct a projective resolution of the trivial `k[G]`-module `k`.

## Main definitions

* `group_algebra.has_scalar`: if a group `G` acts on a `k`-module `M` then there is an induced
action of the group algebra `k[G]` on `M`.
* `group_algebra.mk_linear`: defines the `k[G]`-linear map induced by a `k`-linear map which is
also `G`-linear, when the `k` and `G` actions are compatible.
* `group_algebra.is_scalar_tower'`: the actions of `k` and `k[G]` on `k[Gⁿ]` are compatible.

## Implementation notes

Although `group_algebra k G` is just `monoid_algebra k G`, we make the definition `group_algebra`
so we can separate material relevant to group cohomology into the namespace `group_algebra`.
We make it an abbreviation because we want the instances on `monoid_algebra` to apply to
`group_algebra` without code duplication.
(Some of this file is done in terms of monoids for the sake of generality, but after future
additions, the bulk of the file will be about groups.)

## Tags

group ring, group cohomology, monoid algebra
-/

noncomputable theory

universes u₁ u₂ u₃

/-- The group ring `k[G]` of a group `G` with coefficients in a ring `k` (although this is defined
for any type `G` and any semiring `k`, inducing less algebraic structure). -/
abbreviation group_algebra (k : Type*) [semiring k] (G : Type*) := monoid_algebra k G

namespace group_algebra

open monoid_algebra

/-- Given a map `• : G → M → M` for `M` a `k`-module, the map `k[G] → M → M` sending
`(Σ kᵢgᵢ, m) ↦ Σ kᵢ• (gᵢ • m)`. If this were an instance, it would conflict with the natural
action of `k[k]` on itself given by multiplication. -/
protected def has_scalar {k : Type*} [semiring k] {G : Type*} {M : Type*}
  [add_comm_monoid M] [has_scalar G M] [module k M] :
  has_scalar (group_algebra k G) M :=
⟨λ g m, finsupp.total G M k (λ g, g • m) g⟩

section

local attribute [instance] group_algebra.has_scalar

lemma smul_def {k : Type*} [semiring k] {G : Type*} {M : Type*}
  [add_comm_monoid M] [has_scalar G M] [module k M]
  (r : group_algebra k G) (x : M) :
  r • x = finsupp.total G M k (λ g, g • x) r := rfl

/-- Given a map `• : G → M → M` for `M` a `k`-module, `(r • Σ kᵢgᵢ) • m = r • (Σ kᵢ • (gᵢ • m))`
for all `r ∈ k`, `Σ kᵢgᵢ ∈ k[G]`, `m ∈ M.` -/
instance {k : Type*} [semiring k] {G : Type*}
  {M : Type*} [add_comm_monoid M] [has_scalar G M] [module k M] :
  is_scalar_tower k (group_algebra k G) M :=
{ smul_assoc := λ g x m, show finsupp.total _ _ _ _ _ = g • finsupp.total _ _ _ _ _,
    by simp only [ring_hom.id_apply, linear_map.map_smul] }

/-- Expresses the action of `k[G]` on a `k`-module `M` induced by a compatible `G`-action as a
ring hom `k[G] →+* End(M)`. Helpful for showing that the action makes `M` a `k[G]`-module. -/
lemma smul_eq_lift_nc_ring_hom {k : Type u₁} [semiring k] {G : Type u₂} [monoid G] {M : Type u₃}
  [add_comm_monoid M] [distrib_mul_action G M] [module k M] [smul_comm_class k G M]
  (r : group_algebra k G) (x : M) :
  r • x = lift_nc_ring_hom (module.to_add_monoid_End k M)
    (distrib_mul_action.to_add_monoid_End _ M) (λ _ _, add_monoid_hom.ext $ smul_comm _ _) r x :=
eq.trans (by refl) (add_monoid_hom.finsupp_sum_apply r _ x : _).symm

/-- If `M` has compatible `G`-module and `k`-module structures for a semiring `k`,
it is also a `k[G]`-module. -/
def action_to_module {k : Type*} [semiring k] {G : Type*} [monoid G]
  {M : Type*} [add_comm_monoid M] [distrib_mul_action G M] [module k M]
  [smul_comm_class k G M] : module (group_algebra k G) M :=
{ smul := (•),
  one_smul := λ b, by rw [smul_eq_lift_nc_ring_hom, map_one, add_monoid.coe_one, id],
  mul_smul := λ g h m, by simp only [smul_eq_lift_nc_ring_hom, map_mul, add_monoid.coe_mul],
  smul_add := λ g b c, by simp only [smul_eq_lift_nc_ring_hom, add_monoid_hom.map_add],
  smul_zero := λ x, by rw [smul_eq_lift_nc_ring_hom, add_monoid_hom.map_zero],
  add_smul := λ r s x, linear_map.map_add _ _ _,
  zero_smul := λ x, linear_map.map_zero _ }

end

section

variables {k : Type*} [semiring k] {G : Type*} [monoid G]

lemma smul_of_eq_single (g : G) (r : k) :
  r • (of k G g) = finsupp.single g r :=
by simp only [mul_one, finsupp.smul_single', of_apply]

lemma mk_linear_smul {P : Type*} {P' : Type*} [add_comm_monoid P] [add_comm_monoid P']
  [module k P] [module k P']
  [module (group_algebra k G) P] [module (group_algebra k G) P']
  [is_scalar_tower k (group_algebra k G) P] [is_scalar_tower k (group_algebra k G) P']
  (f : P →ₗ[k] P') (H : ∀ g x, f (of k G g • x) = of k G g • f x)
  (r : group_algebra k G) (x : P) :
  f (r • x) = r • f x :=
begin
  refine r.induction_on (λ g, by exact H g x) _ _,
  { intros a b ha hb,
    simp only [add_smul, f.map_add, ha, hb] },
  { intros r a ha,
    simp only [smul_assoc, f.map_smul, ha] }
end

/-- Makes a `k[G]`-linear map from a `k`-linear map that is also `G`-linear. -/
@[simps] def mk_linear {P : Type*} {P' : Type*} [add_comm_monoid P] [add_comm_monoid P']
  [module k P] [module k P']
  [module (group_algebra k G) P] [module (group_algebra k G) P']
  [is_scalar_tower k (group_algebra k G) P] [is_scalar_tower k (group_algebra k G) P']
  (f : P →ₗ[k] P') (H : ∀ g x, f (of k G g • x) = of k G g • f x) :
  P →ₗ[group_algebra k G] P' :=
{ map_smul' := mk_linear_smul f H, ..f }

/-- Makes a `k[G]`-linear isomorphism from a `k`-linear isomorphism which is also `G`-linear. -/
@[simps] def mk_equiv {P : Type*} {P' : Type*} [add_comm_monoid P] [add_comm_monoid P']
  [module k P] [module k P']
  [module (group_algebra k G) P] [module (group_algebra k G) P']
  [is_scalar_tower k (group_algebra k G) P] [is_scalar_tower k (group_algebra k G) P']
  (f : P ≃ₗ[k] P') (H : ∀ g x, f (of k G g • x) = of k G g • f x) :
  P ≃ₗ[group_algebra k G] P' :=
{ ..f.to_equiv, ..mk_linear f.to_linear_map H }

end

variables {k : Type*} [comm_semiring k] {G : Type*} [group G] {n : ℕ}

instance {H : Type*} [mul_action G H] : distrib_mul_action G (group_algebra k H) :=
finsupp.comap_distrib_mul_action

/-- If `k[H]` is a `k[G]`-module, then a `k`-linear map `f: k[H] →ₗ P` of `k[G]`-modules which
satisfies `f(g • h) = g • f(h)` for all `g ∈ G, h ∈ H` is `k[G]`-linear. -/
lemma map_smul_of_map_smul_of {H : Type*} [monoid H] [module (group_algebra k G) (group_algebra k H)]
  {P : Type*} [add_comm_monoid P] [module k P] [module (group_algebra k G) P]
  [is_scalar_tower k (group_algebra k G) (group_algebra k H)]
  [is_scalar_tower k (group_algebra k G) P] (f : group_algebra k H →ₗ[k] P)
  (h : ∀ (g : G) (x : H), f (of k G g • of k H x) = of k G g • f (of k H x)) (g : group_algebra k G)
  (x : group_algebra k H) : f (g • x) = g • f x :=
begin
  rw mk_linear_smul,
  intros a b,
  refine b.induction_on (by exact h a) _ _,
  { intros s t hs ht,
    simp only [smul_add, f.map_add, hs, ht] },
  { intros r s hs,
    simp only [smul_algebra_smul_comm, f.map_smul, hs] }
end

instance : smul_comm_class k G (group_algebra k (fin n → G)) :=
{ smul_comm := λ x y z,
  begin
    refine z.induction_on _ _ _,
    { intro z,
      simp only [finsupp.smul_single', finsupp.comap_smul_single, of_apply] },
    { intros f g hf hg,
      simp only [hf, hg, smul_add] },
    { intros r f hf,
      ext,
      simp only [finsupp.comap_smul_apply, finsupp.coe_smul, pi.smul_apply]}
  end }

instance : module (group_algebra k G) (group_algebra k (fin n → G)) :=
action_to_module

lemma single_smul_single (g : G) (x : fin n → G) (r s : k) :
  ((•) : group_algebra k G → group_algebra k (fin n → G) → group_algebra k (fin n → G))
  (finsupp.single g r) (finsupp.single x s) =
  finsupp.single (g • x) (r * s) :=
begin
  show finsupp.total _ _ _ _ _ = _,
  simp only [finsupp.smul_single', finsupp.total_single, finsupp.comap_smul_single],
end

lemma of_smul_of (g : G) (x : fin n → G) :
  of k G g • of k (fin n → G) x = of k (fin n → G) (g • x) :=
show finsupp.total _ _ _ _ _ = _, by simp

instance is_scalar_tower' : is_scalar_tower k (group_algebra k G) (group_algebra k (fin n → G)) :=
{ smul_assoc := λ x y z,
  begin
    refine y.induction_on _ _ _,
    { intro y,
      refine z.induction_on _ _ _,
      { intro z,
        simp only [single_smul_single, mul_one, finsupp.smul_single', of_apply] },
      { intros f g hf hg,
        simp only [hf, hg, smul_add] },
      { intros r f hf,
        simp only [smul_def, mul_one, finsupp.smul_single', one_smul,
          finsupp.total_single, of_apply] at hf ⊢}},
    { intros f g hf hg,
      simp only [smul_add, add_smul, hf, hg] },
    { intros r f hf,
      simp only [smul_def, ring_hom.id_apply, linear_map.map_smulₛₗ] }
  end }

end group_algebra
