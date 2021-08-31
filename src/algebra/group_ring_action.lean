/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import group_theory.group_action.group
import data.equiv.ring
import ring_theory.subring

/-!
# Group action on rings

This file defines the typeclass of monoid acting on semirings `mul_semiring_action M R`,
and the corresponding typeclass of invariant subrings.

Note that `algebra` does not satisfy the axioms of `mul_semiring_action`.

## Implementation notes

There is no separate typeclass for group acting on rings, group acting on fields, etc.
They are all grouped under `mul_semiring_action`.

## Tags

group action, invariant subring

-/

universes u v
open_locale big_operators

/-- Typeclass for multiplicative actions by monoids on semirings. -/
class mul_semiring_action (M : Type u) [monoid M] (R : Type v) [semiring R]
  extends distrib_mul_action M R :=
(smul_one : ∀ (g : M), (g • 1 : R) = 1)
(smul_mul : ∀ (g : M) (x y : R), g • (x * y) = (g • x) * (g • y))

export mul_semiring_action (smul_one)

section semiring

variables (M G : Type u) [monoid M] [group G]
variables (A R S F : Type v) [add_monoid A] [semiring R] [comm_semiring S] [field F]

variables {M R}
lemma smul_mul' [mul_semiring_action M R] (g : M) (x y : R) :
  g • (x * y) = (g • x) * (g • y) :=
mul_semiring_action.smul_mul g x y

variables (M R)

/-- Each element of the monoid defines a additive monoid homomorphism. -/
def distrib_mul_action.to_add_monoid_hom [distrib_mul_action M A] (x : M) : A →+ A :=
{ to_fun   := (•) x,
  map_zero' := smul_zero x,
  map_add' := smul_add x }

/-- Each element of the group defines an additive monoid isomorphism. -/
def distrib_mul_action.to_add_equiv [distrib_mul_action G A] (x : G) : A ≃+ A :=
{ .. distrib_mul_action.to_add_monoid_hom G A x,
  .. mul_action.to_perm_hom G A x }

/-- Each element of the group defines an additive monoid homomorphism. -/
def distrib_mul_action.hom_add_monoid_hom [distrib_mul_action M A] : M →* add_monoid.End A :=
{ to_fun := distrib_mul_action.to_add_monoid_hom M A,
  map_one' := add_monoid_hom.ext $ λ x, one_smul M x,
  map_mul' := λ x y, add_monoid_hom.ext $ λ z, mul_smul x y z }

/-- Each element of the monoid defines a semiring homomorphism. -/
def mul_semiring_action.to_ring_hom [mul_semiring_action M R] (x : M) : R →+* R :=
{ map_one' := smul_one x,
  map_mul' := smul_mul' x,
  .. distrib_mul_action.to_add_monoid_hom M R x }

theorem to_ring_hom_injective [mul_semiring_action M R] [has_faithful_scalar M R] :
  function.injective (mul_semiring_action.to_ring_hom M R) :=
λ m₁ m₂ h, eq_of_smul_eq_smul $ λ r, ring_hom.ext_iff.1 h r

/-- Each element of the group defines a semiring isomorphism. -/
def mul_semiring_action.to_semiring_equiv [mul_semiring_action G R] (x : G) : R ≃+* R :=
{ .. distrib_mul_action.to_add_equiv G R x,
  .. mul_semiring_action.to_ring_hom G R x }

section
variables {M G R}

/-- A stronger version of `submonoid.distrib_mul_action`. -/
instance submonoid.mul_semiring_action [mul_semiring_action M R] (H : submonoid M) :
  mul_semiring_action H R :=
{ smul := (•),
  smul_one := λ h, smul_one (h : M),
  smul_mul := λ h, smul_mul' (h : M),
  .. H.distrib_mul_action }

/-- A stronger version of `subgroup.distrib_mul_action`. -/
instance subgroup.mul_semiring_action [mul_semiring_action G R] (H : subgroup G) :
  mul_semiring_action H R :=
H.to_submonoid.mul_semiring_action

/-- A stronger version of `subsemiring.distrib_mul_action`. -/
instance subsemiring.mul_semiring_action {R'} [semiring R'] [mul_semiring_action R' R]
  (H : subsemiring R') :
  mul_semiring_action H R :=
H.to_submonoid.mul_semiring_action

/-- A stronger version of `subring.distrib_mul_action`. -/
instance subring.mul_semiring_action {R'} [ring R'] [mul_semiring_action R' R]
  (H : subring R') :
  mul_semiring_action H R :=
H.to_subsemiring.mul_semiring_action

end

section prod
variables [mul_semiring_action M R] [mul_semiring_action M S]

lemma list.smul_prod (g : M) (L : list R) : g • L.prod = (L.map $ (•) g).prod :=
(mul_semiring_action.to_ring_hom M R g).map_list_prod L

lemma multiset.smul_prod (g : M) (m : multiset S) : g • m.prod = (m.map $ (•) g).prod :=
(mul_semiring_action.to_ring_hom M S g).map_multiset_prod m

lemma smul_prod (g : M) {ι : Type*} (f : ι → S) (s : finset ι) :
  g • ∏ i in s, f i = ∏ i in s, g • f i :=
(mul_semiring_action.to_ring_hom M S g).map_prod f s

end prod

section simp_lemmas

variables {M G A R}

attribute [simp] smul_one smul_mul' smul_zero smul_add

@[simp] lemma smul_inv' [mul_semiring_action M F] (x : M) (m : F) : x • m⁻¹ = (x • m)⁻¹ :=
(mul_semiring_action.to_ring_hom M F x).map_inv _

@[simp] lemma smul_pow [mul_semiring_action M R] (x : M) (m : R) (n : ℕ) :
  x • m ^ n = (x • m) ^ n :=
begin
  induction n with n ih,
  { rw [pow_zero, pow_zero], exact smul_one x },
  { rw [pow_succ, pow_succ], exact (smul_mul' x m (m ^ n)).trans (congr_arg _ ih) }
end

end simp_lemmas

end semiring

section ring

variables (M : Type u) [monoid M] {R : Type v} [ring R] [mul_semiring_action M R]
variables (S : subring R)
open mul_action

/-- A typeclass for subrings invariant under a `mul_semiring_action`. -/
class is_invariant_subring : Prop :=
(smul_mem : ∀ (m : M) {x : R}, x ∈ S → m • x ∈ S)

instance is_invariant_subring.to_mul_semiring_action [is_invariant_subring M S] :
  mul_semiring_action M S :=
{ smul := λ m x, ⟨m • x, is_invariant_subring.smul_mem m x.2⟩,
  one_smul := λ s, subtype.eq $ one_smul M s,
  mul_smul := λ m₁ m₂ s, subtype.eq $ mul_smul m₁ m₂ s,
  smul_add := λ m s₁ s₂, subtype.eq $ smul_add m s₁ s₂,
  smul_zero := λ m, subtype.eq $ smul_zero m,
  smul_one := λ m, subtype.eq $ smul_one m,
  smul_mul := λ m s₁ s₂, subtype.eq $ smul_mul' m s₁ s₂ }

end ring
