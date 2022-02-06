/-
Copyright (c) 2021 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import algebra.monoid_algebra.basic
import tactic.basic

/-!
# Group rings

This file defines the group ring `k[G]` of a group `G` with coefficients in a ring `k`. A
`G`-module with a compatible `k`-module structure is an `R[G]`-module.

We develop an API allowing us to show `k[Gⁿ]` is a free `k[G]`-module for `n ≥ 1`. This
will be used to construct a projective resolution of the trivial `k[G]`-module `k`.

## Implementation notes

Although `group_ring k G` is just `monoid_algebra k G`, we make the definition `group_ring`
so we can separate material relevant to group cohomology into the namespace `group_ring`.
We make it an abbreviation because we want the instances on `monoid_algebra` to apply to
`group_ring` without code duplication.

## Tags

group ring, group cohomology, monoid algebra
-/

noncomputable theory

/-- The group ring `k[G]` of a group `G` with coefficients in a ring `k` (although this is defined
  for any type `G` and any semiring `k`, inducing less algebraic structure). -/
abbreviation group_ring (k : Type*) [semiring k] (G : Type*) := monoid_algebra k G

namespace group_ring

open monoid_algebra

/-- Given a map `• : G × M → M` for `M` a `k`-module, the map `k[G] × M → M` sending
`(Σ kᵢgᵢ, m) ↦ Σ kᵢ• (gᵢ • m)`. If this were an instance, it would conflict with the natural
action of `k[k]` on itself given by multiplication. -/
protected def has_scalar {k : Type*} [semiring k] {G : Type*} {M : Type*}
  [add_comm_monoid M] [has_scalar G M] [module k M] :
  has_scalar (group_ring k G) M :=
⟨λ g m, finsupp.total G M k (λ g, g • m) g⟩

section

local attribute [instance] group_ring.has_scalar

lemma smul_def {k : Type*} [semiring k] {G : Type*} {M : Type*}
  [add_comm_monoid M] [has_scalar G M] [module k M]
  (r : group_ring k G) (x : M) :
  r • x = finsupp.total G M k (λ g, g • x) r := rfl

/-- Given a map `• : G × M → M` for `M` a `k`-module, `(r • Σ kᵢgᵢ) • m = r • (Σ kᵢ • (gᵢ • m))`
for all `r ∈ k`, `Σ kᵢgᵢ ∈ k[G]`, `m ∈ M.` -/
instance {k : Type*} [semiring k] {G : Type*}
  {M : Type*} [add_comm_monoid M] [has_scalar G M] [module k M] :
  is_scalar_tower k (group_ring k G) M :=
{ smul_assoc := λ g x m, show finsupp.total _ _ _ _ _ = g • finsupp.total _ _ _ _ _,
    by simp only [ring_hom.id_apply, linear_map.map_smulₛₗ] }

/-- If `M` has compatible `G`-module and `k`-module structures for a semiring `k`,
it is also a `k[G]`-module. -/
def action_to_module {k : Type*} [semiring k] {G : Type*} [monoid G]
  {M : Type*} [add_comm_monoid M] [distrib_mul_action G M] [module k M]
  [smul_comm_class k G M] : module (group_ring k G) M :=
{ smul := (•),
  one_smul := λ b, by
  { dsimp,
    show finsupp.total _ _ _ _ _ = _,
    erw [finsupp.total_single],
    simp only [one_smul] },
  mul_smul := λ g h m, by
  { refine g.induction_on _ _ _,
    { intros g,
      dsimp,
      rw [monoid_algebra.mul_def, finsupp.sum_single_index],
      { simp only [smul_def, one_mul, one_smul, finsupp.total_single],
        simp only [finsupp.total_single, linear_map.map_finsupp_sum],
        rw [finsupp.total_apply, finsupp.smul_sum],
        simp only [mul_smul, smul_comm] },
      { simp }},
    { intros x y hx hy,
      simp only [smul_def, add_mul, linear_map.map_add] at ⊢ hx hy,
      simp only [hx, hy] },
    { intros r f hf,
      rw [smul_assoc, smul_mul_assoc, smul_assoc, hf] }},
  smul_add := λ g b c, by
    { simp only [smul_def, smul_add, finsupp.total_apply, finsupp.sum_add], },
  smul_zero := λ x, by
    simp only [smul_def, finsupp.total_apply, finsupp.sum_zero, smul_zero],
  add_smul := λ r s x, linear_map.map_add _ _ _,
  zero_smul := λ x, linear_map.map_zero _ }

end

section

variables {k : Type*} [semiring k] {G : Type*} [monoid G]

lemma smul_of_eq_single (g : G) (r : k) :
  r • (of k G g) = finsupp.single g r :=
by simp only [mul_one, finsupp.smul_single', of_apply]

lemma ext {P : Type*} [add_comm_monoid P] [module k P]
  (f : group_ring k G →ₗ[k] P) (g : group_ring k G →ₗ[k] P)
  (H : ∀ x, f (of k G x) = g (of k G x)) {x} :
  f x = g x :=
begin
  refine x.induction_on H _ _,
  { intros y z hy hz,
    rw [f.map_add, g.map_add, hy, hz] },
  { intros r y hy,
    rw [f.map_smul, g.map_smul, hy] }
end

lemma mk_linear_smul {P : Type*} {P' : Type*} [add_comm_monoid P] [add_comm_monoid P']
  [module k P] [module k P']
  [module (group_ring k G) P] [module (group_ring k G) P']
  [is_scalar_tower k (group_ring k G) P] [is_scalar_tower k (group_ring k G) P']
  (f : P →ₗ[k] P') (H : ∀ g x, f (of k G g • x) = of k G g • f x)
  (r : group_ring k G) (x : P) :
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
  [module (group_ring k G) P] [module (group_ring k G) P']
  [is_scalar_tower k (group_ring k G) P] [is_scalar_tower k (group_ring k G) P']
  (f : P →ₗ[k] P') (H : ∀ g x, f (of k G g • x) = of k G g • f x) :
  P →ₗ[group_ring k G] P' :=
{ map_smul' := mk_linear_smul f H, ..f }

/-- Makes a `k[G]`-linear isomorphism from a `k`-linear isomorphism which is also `G`-linear. -/
@[simps] def mk_equiv {P : Type*} {P' : Type*} [add_comm_monoid P] [add_comm_monoid P']
  [module k P] [module k P']
  [module (group_ring k G) P] [module (group_ring k G) P']
  [is_scalar_tower k (group_ring k G) P] [is_scalar_tower k (group_ring k G) P']
  (f : P ≃ₗ[k] P') (H : ∀ g x, f (of k G g • x) = of k G g • f x) :
  P ≃ₗ[group_ring k G] P' :=
{ ..f.to_equiv, ..mk_linear f.to_linear_map H }

end

variables {k : Type*} [comm_semiring k] {G : Type*} [group G] {n : ℕ}

instance {H : Type*} [mul_action G H] : distrib_mul_action G (group_ring k H) :=
finsupp.comap_distrib_mul_action

/-- If `k[H]` is a `k[G]`-module, then a `k`-linear map `f: k[H] →ₗ P` of `k[G]`-modules which
satisfies `f(g • h) = g • f(h)` for all `g ∈ G, h ∈ H` is `k[G]`-linear. -/
lemma map_smul_of_map_smul_of {H : Type*} [monoid H] [module (group_ring k G) (group_ring k H)]
  {P : Type*} [add_comm_monoid P] [module k P] [module (group_ring k G) P]
  [is_scalar_tower k (group_ring k G) (group_ring k H)]
  [is_scalar_tower k (group_ring k G) P] (f : group_ring k H →ₗ[k] P)
  (h : ∀ (g : G) (x : H), f (of k G g • of k H x) = of k G g • f (of k H x)) (g : group_ring k G)
  (x : group_ring k H) : f (g • x) = g • f x :=
begin
  rw mk_linear_smul,
  intros a b,
  refine b.induction_on (by exact h a) _ _,
  { intros s t hs ht,
    simp only [smul_add, f.map_add, hs, ht] },
  { intros r s hs,
    simp only [smul_algebra_smul_comm, f.map_smul, hs] }
end

instance : smul_comm_class k G (group_ring k (fin n → G)) :=
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

instance : module (group_ring k G) (group_ring k (fin n → G)) :=
action_to_module

lemma single_smul_single (g : G) (x : fin n → G) (r s : k) :
  ((•) : group_ring k G → group_ring k (fin n → G) → group_ring k (fin n → G))
  (finsupp.single g r) (finsupp.single x s) =
  finsupp.single (g • x) (r * s) :=
begin
  show finsupp.total _ _ _ _ _ = _,
  simp only [finsupp.smul_single', finsupp.total_single, finsupp.comap_smul_single],
end

lemma of_smul_of (g : G) (x : fin n → G) :
  of k G g • of k (fin n → G) x = of k (fin n → G) (g • x) :=
show finsupp.total _ _ _ _ _ = _, by simp

instance is_scalar_tower' : is_scalar_tower k (group_ring k G) (group_ring k (fin n → G)) :=
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

end group_ring
