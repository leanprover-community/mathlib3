/-
Copyright (c) 2021 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import algebra.monoid_algebra.basic
import tactic.basic

/-!
# Group algebras

This file defines the group algebra `k[G]` of a group `G` with coefficients in a semiring `k`. A
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

We don't want the group cohomology relevant instances defined here to apply to `monoid_algebra`, so
we make `group_algebra` a definition instead of an abbreviation. This leads to some code
duplication as we must copy over some instances from `monoid_algebra`.

Some of this file is done in terms of monoids for the sake of generality, but after future
additions, the bulk of the file will be about groups.

## Tags

group algebra, group ring, group cohomology, monoid algebra
-/

noncomputable theory

universes u₁ u₂ u₃

/-- The group ring `k[G]` of a group `G` with coefficients in a ring `k` (although this is defined
for any type `G` and any semiring `k`, inducing less algebraic structure). -/
@[derive [inhabited, add_comm_monoid]] def group_algebra (k : Type*) [semiring k] (G : Type*) :=
monoid_algebra k G

namespace group_algebra

variables {k : Type*} {G : Type*}

open monoid_algebra

section

instance [semiring k] : has_coe_to_fun (group_algebra k G) (λ _, G → k) :=
monoid_algebra.has_coe_to_fun k G

instance [semiring k] [nontrivial k] [nonempty G] : nontrivial (group_algebra k G) :=
monoid_algebra.nontrivial

instance [semiring k] [mul_one_class G] : non_assoc_semiring (group_algebra k G) :=
monoid_algebra.non_assoc_semiring

instance [semiring k] [monoid G] : semiring (group_algebra k G) :=
monoid_algebra.semiring

instance [comm_semiring k] [comm_monoid G] : comm_semiring (group_algebra k G) :=
monoid_algebra.comm_semiring

instance [ring k] : add_comm_group (group_algebra k G) :=
monoid_algebra.add_comm_group

instance [ring k] [monoid G] : ring (group_algebra k G) :=
monoid_algebra.ring

instance [comm_ring k] [comm_monoid G] : comm_ring (group_algebra k G) :=
monoid_algebra.comm_ring

instance {R : Type*} [semiring k] [monoid R] [distrib_mul_action R k] :
  has_scalar R (group_algebra k G) :=
monoid_algebra.has_scalar

instance {R : Type*} [semiring k] [monoid R] [distrib_mul_action R k] :
  distrib_mul_action R (group_algebra k G) :=
monoid_algebra.distrib_mul_action

instance {R : Type*} [semiring k] [semiring R] [module R k] :
  module R (group_algebra k G) :=
finsupp.module G k

instance {A : Type*} [comm_semiring k] [semiring A] [algebra k A] [monoid G] :
  algebra k (group_algebra A G) :=
monoid_algebra.algebra

/-- The natural embedding of `G` into its group algebra `k[G]`. -/
def of (k : Type*) (G : Type*) [semiring k] [mul_one_class G] :
  G →* group_algebra k G :=
monoid_algebra.of k G

@[simp] lemma of_apply [semiring k] [mul_one_class G] (x : G) :
  of k G x = finsupp.single x 1 := rfl

lemma induction_on [semiring k] [monoid G] {p : group_algebra k G → Prop}
  (f : group_algebra k G) (hM : ∀ g, p (of k G g))
  (hadd : ∀ f g : group_algebra k G, p f → p g → p (f + g))
  (hsmul : ∀ (r : k) f, p f → p (r • f)) : p f :=
monoid_algebra.induction_on _ hM hadd hsmul

end

/-- Given a map `• : G → M → M` for `M` a `k`-module, the map `k[G] → M → M` sending
`(Σ kᵢgᵢ, m) ↦ Σ kᵢ• (gᵢ • m)`. If this were an instance, it would conflict with the natural
action of `k[k]` on itself given by multiplication. -/
protected def has_scalar' [semiring k] {M : Type*} [add_comm_monoid M]
  [has_scalar G M] [module k M] : has_scalar (group_algebra k G) M :=
⟨λ g m, finsupp.total G M k (λ g, g • m) g⟩

section

variables [semiring k]
local attribute [instance] group_algebra.has_scalar'

lemma smul_def {M : Type*} [add_comm_monoid M] [has_scalar G M] [module k M]
  (r : group_algebra k G) (x : M) :
  r • x = finsupp.total G M k (λ g, g • x) r := rfl

/-- Given a map `• : G → M → M` for `M` a `k`-module, `(r • Σ kᵢgᵢ) • m = r • (Σ kᵢ • (gᵢ • m))`
for all `r ∈ k`, `Σ kᵢgᵢ ∈ k[G]`, `m ∈ M.` -/
instance {M : Type*} [add_comm_monoid M] [has_scalar G M] [module k M] :
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
def action_to_module [monoid G] {M : Type*} [add_comm_monoid M]
  [distrib_mul_action G M] [module k M] [smul_comm_class k G M] :
  module (group_algebra k G) M :=
{ smul := (•),
  one_smul := λ b, by rw [smul_eq_lift_nc_ring_hom, map_one, add_monoid.coe_one, id],
  mul_smul := λ g h m, by simp only [smul_eq_lift_nc_ring_hom, map_mul, add_monoid.coe_mul],
  smul_add := λ g b c, by simp only [smul_eq_lift_nc_ring_hom, add_monoid_hom.map_add],
  smul_zero := λ x, by rw [smul_eq_lift_nc_ring_hom, add_monoid_hom.map_zero],
  add_smul := λ r s x, linear_map.map_add _ _ _,
  zero_smul := λ x, linear_map.map_zero _ }

end

section

variables [semiring k] [monoid G]

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
  induction r using group_algebra.induction_on,
  { exact H r x },
  { simp only [add_smul, f.map_add, *] },
  { simp only [smul_assoc, f.map_smul, *] }
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

variables [comm_semiring k] [group G] {n : ℕ}

instance comap_distrib_mul_action {H : Type*} [mul_action G H] :
  distrib_mul_action G (group_algebra k H) :=
finsupp.comap_distrib_mul_action

/-- If `k[H]` is a `k[G]`-module, then a `k`-linear map `f: k[H] →ₗ P` of `k[G]`-modules which
satisfies `f(g • h) = g • f(h)` for all `g ∈ G, h ∈ H` is `k[G]`-linear. -/
lemma map_smul_of_map_smul_of {H : Type*} [monoid H]
  [module (group_algebra k G) (group_algebra k H)] {P : Type*} [add_comm_monoid P] [module k P]
  [module (group_algebra k G) P] [is_scalar_tower k (group_algebra k G) (group_algebra k H)]
  [is_scalar_tower k (group_algebra k G) P] (f : group_algebra k H →ₗ[k] P)
  (h : ∀ (g : G) (x : H), f (of k G g • of k H x) = of k G g • f (of k H x))
  (g : group_algebra k G) (x : group_algebra k H) : f (g • x) = g • f x :=
begin
  rw mk_linear_smul,
  intros a b,
  refine b.induction_on (by exact h a) _ _,
  { intros s t hs ht,
    simp only [smul_add, f.map_add, hs, ht] },
  { intros r s hs,
    simp only [smul_algebra_smul_comm, f.map_smul, hs] }
end

instance {M} [monoid M] [mul_action G M] : smul_comm_class k G (group_algebra k M) :=
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

instance module' : module (group_algebra k G) (group_algebra k (fin n → G)) :=
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
    refine y.induction_on
      (λ w, _)
      (λ f g hf hg, by simp only [smul_add, add_smul, hf, hg])
      (λ r f hf, by simp only [smul_def, ring_hom.id_apply, linear_map.map_smulₛₗ]),
    exact z.induction_on
      (λ v, by simp only [mul_one, of_apply, finsupp.smul_single', single_smul_single])
      (λ f g hf hg, by simp only [hf, hg, smul_add])
      (λ r f hf, by simp only [smul_def, mul_one, one_smul, of_apply, finsupp.total_single,
        finsupp.smul_single']),
  end }

end group_algebra
