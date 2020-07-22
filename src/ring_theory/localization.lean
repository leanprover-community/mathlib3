/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston
-/

import data.equiv.ring
import tactic.ring_exp
import ring_theory.ideal_operations
import group_theory.monoid_localization
import ring_theory.algebraic
import ring_theory.integral_closure

/-!
# Localizations of commutative rings

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R`, `f x = f y` iff there exists `c ∈ M` such that `x * c = y * c`.

Given such a localization map `f : R →+* S`, we can define the surjection
`localization_map.mk'` sending `(x, y) : R × M` to `f x * (f y)⁻¹`, and
`localization_map.lift`, the homomorphism from `S` induced by a homomorphism from `R` which maps
elements of `M` to invertible elements of the codomain. Similarly, given commutative rings
`P, Q`, a submonoid `T` of `P` and a localization map for `T` from `P` to `Q`, then a homomorphism
`g : R →+* P` such that `g(M) ⊆ T` induces a homomorphism of localizations,
`localization_map.map`, from `S` to `Q`.

We show the localization as a quotient type, defined in `group_theory.monoid_localization` as
`submonoid.localization`, is a `comm_ring` and that the natural ring hom
`of : R →+* localization M` is a localization map.

We show that a localization at the complement of a prime ideal is a local ring.

We prove some lemmas about the `R`-algebra structure of `S`.

When `R` is an integral domain, we define `fraction_map R K` as an abbreviation for
`localization (non_zero_divisors R) K`, the natural map to `R`'s field of fractions.

We show that a `comm_ring` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field. We use this to show the field of fractions as a quotient type, `fraction_ring`, is
a field.

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A ring localization map is defined to be a localization map of the underlying `comm_monoid` (a
`submonoid.localization_map`) which is also a ring hom. To prove most lemmas about a
`localization_map` `f` in this file we invoke the corresponding proof for the underlying
`comm_monoid` localization map `f.to_localization_map`, which can be found in
`group_theory.monoid_localization` and the namespace `submonoid.localization_map`.

To apply a localization map `f` as a function, we use `f.to_map`, as coercions don't work well for
this structure.

To reason about the localization as a quotient type, use `mk_eq_of_mk'` and associated lemmas.
These show the quotient map `mk : R → M → localization M` equals the surjection
`localization_map.mk'` induced by the map `of : localization_map M (localization M)`
(where `of` establishes the localization as a quotient type satisfies the characteristic
predicate). The lemma `mk_eq_of_mk'` hence gives you access to the results in the rest of the file,
which are about the `localization_map.mk'` induced by any localization map.

We define a copy of the localization map `f`'s codomain `S` carrying the data of `f` so that
instances on `S` induced by `f` can 'know' the map needed to induce the instance.

The proof that "a `comm_ring` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field" is a `def` rather than an `instance`, so if you want to reason about a field of
fractions `K`, assume `[field K]` instead of just `[comm_ring K]`.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/
variables {R : Type*} [comm_ring R] (M : submonoid R) (S : Type*) [comm_ring S]
          {P : Type*} [comm_ring P]

open function

set_option old_structure_cmd true

/-- The type of ring homomorphisms satisfying the characteristic predicate: if `f : R →+* S`
satisfies this predicate, then `S` is isomorphic to the localization of `R` at `M`.
We later define an instance coercing a localization map `f` to its codomain `S` so
that instances on `S` induced by `f` can 'know' the map needed to induce the instance. -/
@[nolint has_inhabited_instance] structure localization_map
extends ring_hom R S, submonoid.localization_map M S

/-- The ring hom underlying a `localization_map`. -/
add_decl_doc localization_map.to_ring_hom

/-- The `comm_monoid` `localization_map` underlying a `comm_ring` `localization_map`.
See `group_theory.monoid_localization` for its definition. -/
add_decl_doc localization_map.to_localization_map

variables {M S}

namespace ring_hom

/-- Makes a localization map from a `comm_ring` hom satisfying the characteristic predicate. -/
def to_localization_map (f : R →+* S) (H1 : ∀ y : M, is_unit (f y))
  (H2 : ∀ z, ∃ x : R × M, z * f x.2 = f x.1) (H3 : ∀ x y, f x = f y ↔ ∃ c : M, x * c = y * c) :
  localization_map M S :=
{ map_units' := H1,
  surj' := H2,
  eq_iff_exists' := H3,
  .. f }

end ring_hom

/-- Makes a `comm_ring` localization map from an additive `comm_monoid` localization map of
`comm_ring`s. -/
def submonoid.localization_map.to_ring_localization
  (f : submonoid.localization_map M S)
  (h : ∀ x y, f.to_map (x + y) = f.to_map x + f.to_map y) :
  localization_map M S :=
{ ..ring_hom.mk' f.to_monoid_hom h, ..f }

namespace localization_map

variables (f : localization_map M S)

/-- We define a copy of the localization map `f`'s codomain `S` carrying the data of `f` so that
instances on `S` induced by `f` can 'know` the map needed to induce the instance. -/
@[nolint unused_arguments has_inhabited_instance]
def codomain (f : localization_map M S) := S

instance : comm_ring f.codomain := by assumption
instance {K : Type*} [field K] (f : localization_map M K) : field f.codomain := by assumption

/-- Short for `to_ring_hom`; used for applying a localization map as a function. -/
abbreviation to_map := f.to_ring_hom

lemma map_units (y : M) : is_unit (f.to_map y) := f.6 y

lemma surj (z) : ∃ x : R × M, z * f.to_map x.2 = f.to_map x.1 := f.7 z

lemma eq_iff_exists {x y} : f.to_map x = f.to_map y ↔ ∃ c : M, x * c = y * c := f.8 x y

@[ext] lemma ext {f g : localization_map M S}
  (h : ∀ x, f.to_map x = g.to_map x) : f = g :=
begin
  cases f, cases g,
  simp only at *,
  exact funext h
end

lemma ext_iff {f g : localization_map M S} : f = g ↔ ∀ x, f.to_map x = g.to_map x :=
⟨λ h x, h ▸ rfl, ext⟩

lemma to_map_injective : injective (@localization_map.to_map _ _ M S _) :=
λ _ _ h, ext $ ring_hom.ext_iff.1 h

/-- Given `a : S`, `S` a localization of `R`, `is_integer a` iff `a` is in the image of
the localization map from `R` to `S`. -/
def is_integer (a : S) : Prop := a ∈ set.range f.to_map

variables {f}

lemma is_integer_add {a b} (ha : f.is_integer a) (hb : f.is_integer b) :
  f.is_integer (a + b) :=
begin
  rcases ha with ⟨a', ha⟩,
  rcases hb with ⟨b', hb⟩,
  use a' + b',
  rw [f.to_map.map_add, ha, hb]
end

lemma is_integer_mul {a b} (ha : f.is_integer a) (hb : f.is_integer b) :
  f.is_integer (a * b) :=
begin
  rcases ha with ⟨a', ha⟩,
  rcases hb with ⟨b', hb⟩,
  use a' * b',
  rw [f.to_map.map_mul, ha, hb]
end

lemma is_integer_smul {a : R} {b} (hb : f.is_integer b) :
  f.is_integer (f.to_map a * b) :=
begin
  rcases hb with ⟨b', hb⟩,
  use a * b',
  rw [←hb, f.to_map.map_mul]
end

variables (f)

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the right, matching the argument order in `localization_map.surj`.
-/
lemma exists_integer_multiple' (a : S) :
  ∃ (b : M), is_integer f (a * f.to_map b) :=
let ⟨⟨num, denom⟩, h⟩ := f.surj a in ⟨denom, set.mem_range.mpr ⟨num, h.symm⟩⟩

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the left, matching the argument order in the `has_scalar` instance.
-/
lemma exists_integer_multiple (a : S) :
  ∃ (b : M), is_integer f (f.to_map b * a) :=
by { simp_rw mul_comm _ a, apply exists_integer_multiple' }

/-- Given `z : S`, `f.to_localization_map.sec z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x` (so this lemma is true by definition). -/
lemma sec_spec {f : localization_map M S} (z : S) :
  z * f.to_map (f.to_localization_map.sec z).2 = f.to_map (f.to_localization_map.sec z).1 :=
classical.some_spec $ f.surj z

/-- Given `z : S`, `f.to_localization_map.sec z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x`, so this lemma is just an application of `S`'s commutativity. -/
lemma sec_spec' {f : localization_map M S} (z : S) :
  f.to_map (f.to_localization_map.sec z).1 = f.to_map (f.to_localization_map.sec z).2 * z :=
by rw [mul_comm, sec_spec]

open_locale big_operators

/-- We can clear the denominators of a finite set of fractions. -/
lemma exist_integer_multiples_of_finset (s : finset S) :
  ∃ (b : M), ∀ a ∈ s, is_integer f (f.to_map b * a) :=
begin
  haveI := classical.prop_decidable,
  use ∏ a in s, (f.to_localization_map.sec a).2,
  intros a ha,
  use (∏ x in s.erase a, (f.to_localization_map.sec x).2) * (f.to_localization_map.sec a).1,
  rw [ring_hom.map_mul, sec_spec', ←mul_assoc, ←f.to_map.map_mul],
  congr' 2,
  refine trans _ ((submonoid.subtype M).map_prod _ _).symm,
  rw [mul_comm, ←finset.prod_insert (s.not_mem_erase a), finset.insert_erase ha],
  refl,
end

lemma map_right_cancel {x y} {c : M} (h : f.to_map (c * x) = f.to_map (c * y)) :
  f.to_map x = f.to_map y :=
f.to_localization_map.map_right_cancel h

lemma map_left_cancel {x y} {c : M} (h : f.to_map (x * c) = f.to_map (y * c)) :
  f.to_map x = f.to_map y :=
f.to_localization_map.map_left_cancel h

lemma eq_zero_of_fst_eq_zero {z x} {y : M}
  (h : z * f.to_map y = f.to_map x) (hx : x = 0) : z = 0 :=
by rw [hx, f.to_map.map_zero] at h; exact (f.map_units y).mul_left_eq_zero.1 h

/-- Given a localization map `f : R →+* S`, the surjection sending `(x, y) : R × M` to
`f x * (f y)⁻¹`. -/
noncomputable def mk' (f : localization_map M S) (x : R) (y : M) : S :=
f.to_localization_map.mk' x y

@[simp] lemma mk'_sec (z : S) :
  f.mk' (f.to_localization_map.sec z).1 (f.to_localization_map.sec z).2 = z :=
f.to_localization_map.mk'_sec _

lemma mk'_mul (x₁ x₂ : R) (y₁ y₂ : M) :
  f.mk' (x₁ * x₂) (y₁ * y₂) = f.mk' x₁ y₁ * f.mk' x₂ y₂ :=
f.to_localization_map.mk'_mul _ _ _ _

lemma mk'_one (x) : f.mk' x (1 : M) = f.to_map x :=
f.to_localization_map.mk'_one _

lemma mk'_spec (x) (y : M) :
  f.mk' x y * f.to_map y = f.to_map x :=
f.to_localization_map.mk'_spec _ _

lemma mk'_spec' (x) (y : M) :
  f.to_map y * f.mk' x y = f.to_map x :=
f.to_localization_map.mk'_spec' _ _

theorem eq_mk'_iff_mul_eq {x} {y : M} {z} :
  z = f.mk' x y ↔ z * f.to_map y = f.to_map x :=
f.to_localization_map.eq_mk'_iff_mul_eq

theorem mk'_eq_iff_eq_mul {x} {y : M} {z} :
  f.mk' x y = z ↔ f.to_map x = z * f.to_map y :=
f.to_localization_map.mk'_eq_iff_eq_mul

lemma mk'_surjective (z : S) : ∃ x (y : M), f.mk' x y = z :=
let ⟨r, hr⟩ := f.surj z in ⟨r.1, r.2, (f.eq_mk'_iff_mul_eq.2 hr).symm⟩

lemma mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : M} :
  f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ f.to_map (x₁ * y₂) = f.to_map (x₂ * y₁) :=
f.to_localization_map.mk'_eq_iff_eq

protected lemma eq {a₁ b₁} {a₂ b₂ : M} :
  f.mk' a₁ a₂ = f.mk' b₁ b₂ ↔ ∃ c : M, a₁ * b₂ * c = b₁ * a₂ * c :=
f.to_localization_map.eq

lemma eq_iff_eq (g : localization_map M P) {x y} :
  f.to_map x = f.to_map y ↔ g.to_map x = g.to_map y :=
f.to_localization_map.eq_iff_eq g.to_localization_map

lemma mk'_eq_iff_mk'_eq (g : localization_map M P) {x₁ x₂}
  {y₁ y₂ : M} : f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ g.mk' x₁ y₁ = g.mk' x₂ y₂ :=
f.to_localization_map.mk'_eq_iff_mk'_eq g.to_localization_map

lemma mk'_eq_of_eq {a₁ b₁ : R} {a₂ b₂ : M} (H : b₁ * a₂ = a₁ * b₂) :
  f.mk' a₁ a₂ = f.mk' b₁ b₂ :=
f.to_localization_map.mk'_eq_of_eq H

@[simp] lemma mk'_self {x : R} (hx : x ∈ M) : f.mk' x ⟨x, hx⟩ = 1 :=
f.to_localization_map.mk'_self' _ hx

@[simp] lemma mk'_self' {x : M} : f.mk' x x = 1 :=
f.to_localization_map.mk'_self _

lemma mk'_self'' {x : M} : f.mk' x.1 x = 1 :=
f.mk'_self'

lemma mul_mk'_eq_mk'_of_mul (x y : R) (z : M) :
  f.to_map x * f.mk' y z = f.mk' (x * y) z :=
f.to_localization_map.mul_mk'_eq_mk'_of_mul _ _ _

lemma mk'_eq_mul_mk'_one (x : R) (y : M) :
  f.mk' x y = f.to_map x * f.mk' 1 y :=
(f.to_localization_map.mul_mk'_one_eq_mk' _ _).symm

@[simp] lemma mk'_mul_cancel_left (x : R) (y : M) :
  f.mk' (y * x) y = f.to_map x :=
f.to_localization_map.mk'_mul_cancel_left _ _

lemma mk'_mul_cancel_right (x : R) (y : M) :
  f.mk' (x * y) y = f.to_map x :=
f.to_localization_map.mk'_mul_cancel_right _ _

@[simp] lemma mk'_mul_mk'_eq_one (x y : M) :
  f.mk' x y * f.mk' y x = 1 :=
by rw [←f.mk'_mul, mul_comm]; exact f.mk'_self _

lemma mk'_mul_mk'_eq_one' (x : R) (y : M) (h : x ∈ M) :
  f.mk' x y * f.mk' y ⟨x, h⟩ = 1 :=
f.mk'_mul_mk'_eq_one ⟨x, h⟩ _

lemma is_unit_comp (j : S →+* P) (y : M) :
  is_unit (j.comp f.to_map y) :=
f.to_localization_map.is_unit_comp j.to_monoid_hom _

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →+* P` such that `g(M) ⊆ units P`, `f x = f y → g x = g y` for all `x y : R`. -/
lemma eq_of_eq {g : R →+* P} (hg : ∀ y : M, is_unit (g y)) {x y} (h : f.to_map x = f.to_map y) :
  g x = g y :=
@submonoid.localization_map.eq_of_eq _ _ _ _ _ _ _
  f.to_localization_map g.to_monoid_hom hg _ _ h

lemma mk'_add (x₁ x₂ : R) (y₁ y₂ : M) :
  f.mk' (x₁ * y₂ + x₂ * y₁) (y₁ * y₂) = f.mk' x₁ y₁ + f.mk' x₂ y₂ :=
f.mk'_eq_iff_eq_mul.2 $ eq.symm
begin
  rw [mul_comm (_ + _), mul_add, mul_mk'_eq_mk'_of_mul, ←eq_sub_iff_add_eq, mk'_eq_iff_eq_mul,
      mul_comm _ (f.to_map _), mul_sub, eq_sub_iff_add_eq, ←eq_sub_iff_add_eq', ←mul_assoc,
      ←f.to_map.map_mul, mul_mk'_eq_mk'_of_mul, mk'_eq_iff_eq_mul],
  simp only [f.to_map.map_add, submonoid.coe_mul, f.to_map.map_mul],
  ring_exp,
end

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →+* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` sending `z : S` to `g x * (g y)⁻¹`, where `(x, y) : R × M` are such that
`z = f x * (f y)⁻¹`. -/
noncomputable def lift {g : R →+* P} (hg : ∀ y : M, is_unit (g y)) : S →+* P :=
ring_hom.mk' (@submonoid.localization_map.lift _ _ _ _ _ _ _
  f.to_localization_map g.to_monoid_hom hg) $
begin
  intros x y,
  rw [f.to_localization_map.lift_spec, mul_comm, add_mul, ←sub_eq_iff_eq_add, eq_comm,
      f.to_localization_map.lift_spec_mul, mul_comm _ (_ - _), sub_mul, eq_sub_iff_add_eq',
      ←eq_sub_iff_add_eq, mul_assoc, f.to_localization_map.lift_spec_mul],
  show g _ * (g _ * g _) = g _ * (g _ * g _ - g _ * g _),
  repeat {rw ←g.map_mul},
  rw [←g.map_sub, ←g.map_mul],
  apply f.eq_of_eq hg,
  erw [f.to_map.map_mul, sec_spec', mul_sub, f.to_map.map_sub],
  simp only [f.to_map.map_mul, sec_spec'],
  ring_exp,
end

variables {g : R →+* P} (hg : ∀ y : M, is_unit (g y))

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : R, y ∈ M`. -/
lemma lift_mk' (x y) :
  f.lift hg (f.mk' x y) = g x * ↑(is_unit.lift_right (g.to_monoid_hom.mrestrict M) hg y)⁻¹ :=
f.to_localization_map.lift_mk' _ _ _

lemma lift_mk'_spec (x v) (y : M) :
  f.lift hg (f.mk' x y) = v ↔ g x = g y * v :=
f.to_localization_map.lift_mk'_spec _ _ _ _

@[simp] lemma lift_eq (x : R) :
  f.lift hg (f.to_map x) = g x :=
f.to_localization_map.lift_eq _ _

lemma lift_eq_iff {x y : R × M} :
  f.lift hg (f.mk' x.1 x.2) = f.lift hg (f.mk' y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2) :=
f.to_localization_map.lift_eq_iff _

@[simp] lemma lift_comp : (f.lift hg).comp f.to_map = g :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ f.to_localization_map.lift_comp _

@[simp] lemma lift_of_comp (j : S →+* P) :
  f.lift (f.is_unit_comp j) = j :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ f.to_localization_map.lift_of_comp j.to_monoid_hom

lemma epic_of_localization_map {j k : S →+* P}
  (h : ∀ a, j.comp f.to_map a = k.comp f.to_map a) : j = k :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ @submonoid.localization_map.epic_of_localization_map
  _ _ _ _ _ _ _ f.to_localization_map j.to_monoid_hom k.to_monoid_hom h

lemma lift_unique {j : S →+* P}
  (hj : ∀ x, j (f.to_map x) = g x) : f.lift hg = j :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ @submonoid.localization_map.lift_unique
  _ _ _ _ _ _ _ f.to_localization_map g.to_monoid_hom hg j.to_monoid_hom hj

@[simp] lemma lift_id (x) : f.lift f.map_units x = x :=
f.to_localization_map.lift_id _

/-- Given two localization maps `f : R →+* S, k : R →+* P` for a submonoid `M ⊆ R`,
the hom from `P` to `S` induced by `f` is left inverse to the hom from `S` to `P`
induced by `k`. -/
@[simp] lemma lift_left_inverse {k : localization_map M S} (z : S) :
  k.lift f.map_units (f.lift k.map_units z) = z :=
f.to_localization_map.lift_left_inverse _

lemma lift_surjective_iff :
  surjective (f.lift hg) ↔ ∀ v : P, ∃ x : R × M, v * g x.2 = g x.1 :=
f.to_localization_map.lift_surjective_iff hg

lemma lift_injective_iff :
  injective (f.lift hg) ↔ ∀ x y, f.to_map x = f.to_map y ↔ g x = g y :=
f.to_localization_map.lift_injective_iff hg

variables {T : submonoid P} (hy : ∀ y : M, g y ∈ T) {Q : Type*} [comm_ring Q]
          (k : localization_map T Q)

/-- Given a `comm_ring` homomorphism `g : R →+* P` where for submonoids `M ⊆ R, T ⊆ P` we have
`g(M) ⊆ T`, the induced ring homomorphism from the localization of `R` at `M` to the
localization of `P` at `T`: if `f : R →+* S` and `k : P →+* Q` are localization maps for `M`
and `T` respectively, we send `z : S` to `k (g x) * (k (g y))⁻¹`, where `(x, y) : R × M` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def map : S →+* Q :=
@lift _ _ _ _ _ _ _ f (k.to_map.comp g) $ λ y, k.map_units ⟨g y, hy y⟩

variables {k}

lemma map_eq (x) :
  f.map hy k (f.to_map x) = k.to_map (g x) :=
f.lift_eq (λ y, k.map_units ⟨g y, hy y⟩) x

@[simp] lemma map_comp :
  (f.map hy k).comp f.to_map = k.to_map.comp g :=
f.lift_comp $ λ y, k.map_units ⟨g y, hy y⟩

lemma map_mk' (x) (y : M) :
  f.map hy k (f.mk' x y) = k.mk' (g x) ⟨g y, hy y⟩ :=
@submonoid.localization_map.map_mk' _ _ _ _ _ _ _ f.to_localization_map
g.to_monoid_hom _ hy _ _ k.to_localization_map _ _

@[simp] lemma map_id (z : S) :
  f.map (λ y, show ring_hom.id R y ∈ M, from y.2) f z = z :=
f.lift_id _

/-- If `comm_ring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
lemma map_comp_map {A : Type*} [comm_ring A] {U : submonoid A} {W} [comm_ring W]
  (j : localization_map U W) {l : P →+* A} (hl : ∀ w : T, l w ∈ U) :
  (k.map hl j).comp (f.map hy k) = f.map (λ x, show l.comp g x ∈ U, from hl ⟨g x, hy x⟩) j :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ @submonoid.localization_map.map_comp_map _ _ _ _ _ _ _
  f.to_localization_map g.to_monoid_hom _ hy _ _ k.to_localization_map
    _ _ _ _ _ j.to_localization_map l.to_monoid_hom hl

/-- If `comm_ring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
lemma map_map {A : Type*} [comm_ring A] {U : submonoid A} {W} [comm_ring W]
  (j : localization_map U W) {l : P →+* A} (hl : ∀ w : T, l w ∈ U) (x) :
  k.map hl j (f.map hy k x) = f.map (λ x, show l.comp g x ∈ U, from hl ⟨g x, hy x⟩) j x :=
by rw ←f.map_comp_map hy j hl; refl

/-- Given localization maps `f : R →+* S, k : P →+* Q` for submonoids `M, T` respectively, an
isomorphism `j : R ≃+* P` such that `j(M) = T` induces an isomorphism of localizations
`S ≃+* Q`. -/
noncomputable def ring_equiv_of_ring_equiv (k : localization_map T Q) (h : R ≃+* P)
  (H : M.map h.to_monoid_hom = T) :
  S ≃+* Q :=
(f.to_localization_map.mul_equiv_of_mul_equiv k.to_localization_map H).to_ring_equiv $
(@lift _ _ _ _ _ _ _ f (k.to_map.comp h.to_ring_hom)
  (λ y, k.map_units ⟨(h y), H ▸ set.mem_image_of_mem h y.2⟩)).map_add

@[simp] lemma ring_equiv_of_ring_equiv_eq_map_apply {j : R ≃+* P}
  (H : M.map j.to_monoid_hom = T) (x) :
  f.ring_equiv_of_ring_equiv k j H x =
    f.map (λ y : M, show j.to_monoid_hom y ∈ T, from H ▸ set.mem_image_of_mem j y.2) k x := rfl

lemma ring_equiv_of_ring_equiv_eq_map {j : R ≃+* P} (H : M.map j.to_monoid_hom = T) :
  (f.ring_equiv_of_ring_equiv k j H).to_monoid_hom =
    f.map (λ y : M, show j.to_monoid_hom y ∈ T, from H ▸ set.mem_image_of_mem j y.2) k := rfl

@[simp] lemma ring_equiv_of_ring_equiv_eq {j : R ≃+* P} (H : M.map j.to_monoid_hom = T) (x) :
  f.ring_equiv_of_ring_equiv k j H (f.to_map x) = k.to_map (j x) :=
f.to_localization_map.mul_equiv_of_mul_equiv_eq H _

lemma ring_equiv_of_ring_equiv_mk' {j : R ≃+* P} (H : M.map j.to_monoid_hom = T) (x y) :
  f.ring_equiv_of_ring_equiv k j H (f.mk' x y) =
    k.mk' (j x) ⟨j y, H ▸ set.mem_image_of_mem j y.2⟩ :=
f.to_localization_map.mul_equiv_of_mul_equiv_mk' H _ _

end localization_map

namespace localization

variables {M}

instance : has_add (localization M) :=
⟨λ z w, con.lift_on₂ z w
  (λ x y : R × M, mk ((x.2 : R) * y.1 + y.2 * x.1) (x.2 * y.2)) $
λ r1 r2 r3 r4 h1 h2, (con.eq _).2
begin
  rw r_eq_r' at h1 h2 ⊢,
  cases h1 with t₅ ht₅,
  cases h2 with t₆ ht₆,
  use t₆ * t₅,
  calc ((r1.2 : R) * r2.1 + r2.2 * r1.1) * (r3.2 * r4.2) * (t₆ * t₅) =
      (r2.1 * r4.2 * t₆) * (r1.2 * r3.2 * t₅) + (r1.1 * r3.2 * t₅) * (r2.2 * r4.2 * t₆) : by ring
      ... = (r3.2 * r4.1 + r4.2 * r3.1) * (r1.2 * r2.2) * (t₆ * t₅) : by rw [ht₆, ht₅]; ring
end⟩

instance : has_neg (localization M) :=
⟨λ z, con.lift_on z (λ x : R × M, mk (-x.1) x.2) $
  λ r1 r2 h, (con.eq _).2
begin
  rw r_eq_r' at h ⊢,
  cases h with t ht,
  use t,
  rw [neg_mul_eq_neg_mul_symm, neg_mul_eq_neg_mul_symm, ht],
  ring,
end⟩

instance : has_zero (localization M) :=
⟨mk 0 1⟩

private meta def tac := `[{
  intros,
  refine quotient.sound' (r_of_eq _),
  simp only [prod.snd_mul, prod.fst_mul, submonoid.coe_mul],
  ring }]

instance : comm_ring (localization M) :=
{ zero := 0,
  one  := 1,
  add  := (+),
  mul  := (*),
  add_assoc      := λ m n k, quotient.induction_on₃' m n k (by tac),
  zero_add       := λ y, quotient.induction_on' y (by tac),
  add_zero       := λ y, quotient.induction_on' y (by tac),
  neg            := has_neg.neg,
  add_left_neg   := λ y, quotient.induction_on' y (by tac),
  add_comm       := λ y z, quotient.induction_on₂' z y (by tac),
  left_distrib   := λ m n k, quotient.induction_on₃' m n k (by tac),
  right_distrib  := λ m n k, quotient.induction_on₃' m n k (by tac),
   ..localization.comm_monoid M }

variables (M)
/-- Natural hom sending `x : R`, `R` a `comm_ring`, to the equivalence class of
`(x, 1)` in the localization of `R` at a submonoid. -/
def of : localization_map M (localization M) :=
(localization.monoid_of M).to_ring_localization $
  λ x y, (con.eq _).2 $ r_of_eq $ by simp [add_comm]

variables {M}

lemma monoid_of_eq_of (x) : (monoid_of M).to_map x = (of M).to_map x := rfl

lemma mk_one_eq_of (x) : mk x 1 = (of M).to_map x := rfl

lemma mk_eq_mk'_apply (x y) : mk x y = (of M).mk' x y :=
mk_eq_monoid_of_mk'_apply _ _

@[simp] lemma mk_eq_mk' : mk = (of M).mk' :=
mk_eq_monoid_of_mk'

variables (f : localization_map M S)
/-- Given a localization map `f : R →+* S` for a submonoid `M`, we get an isomorphism
between the localization of `R` at `M` as a quotient type and `S`. -/
noncomputable def ring_equiv_of_quotient :
  localization M ≃+* S :=
(mul_equiv_of_quotient f.to_localization_map).to_ring_equiv $
((of M).lift f.map_units).map_add

variables {f}

@[simp] lemma ring_equiv_of_quotient_apply (x) :
  ring_equiv_of_quotient f x = (of M).lift f.map_units x := rfl

@[simp] lemma ring_equiv_of_quotient_mk' (x y) :
  ring_equiv_of_quotient f ((of M).mk' x y) = f.mk' x y :=
mul_equiv_of_quotient_mk' _ _

lemma ring_equiv_of_quotient_mk (x y) :
  ring_equiv_of_quotient f (mk x y) = f.mk' x y :=
mul_equiv_of_quotient_mk _ _

@[simp] lemma ring_equiv_of_quotient_of (x) :
  ring_equiv_of_quotient f ((of M).to_map x) = f.to_map x :=
mul_equiv_of_quotient_monoid_of _

@[simp] lemma ring_equiv_of_quotient_symm_mk' (x y) :
  (ring_equiv_of_quotient f).symm (f.mk' x y) = (of M).mk' x y :=
mul_equiv_of_quotient_symm_mk' _ _

lemma ring_equiv_of_quotient_symm_mk (x y) :
  (ring_equiv_of_quotient f).symm (f.mk' x y) = mk x y :=
mul_equiv_of_quotient_symm_mk _ _

@[simp] lemma ring_equiv_of_quotient_symm_of (x) :
  (ring_equiv_of_quotient f).symm (f.to_map x) = (of M).to_map x :=
mul_equiv_of_quotient_symm_monoid_of _

end localization
variables {M}

section at_prime

variables (I : ideal R) [hp : I.is_prime]
include hp
namespace ideal

/-- The complement of a prime ideal `I ⊆ R` is a submonoid of `R`. -/
def prime_compl :
  submonoid R :=
{ carrier := (Iᶜ : set R),
  one_mem' := by convert I.ne_top_iff_one.1 hp.1; refl,
  mul_mem' := λ x y hnx hny hxy, or.cases_on (hp.2 hxy) hnx hny }

end ideal

namespace localization_map
variables (S)

/-- A localization map from `R` to `S` where the submonoid is the complement of a prime
ideal of `R`. -/
@[reducible] def at_prime :=
localization_map I.prime_compl S

end localization_map
namespace localization

/-- The localization of `R` at the complement of a prime ideal, as a quotient type. -/
@[reducible] def at_prime :=
localization I.prime_compl

end localization
namespace localization_map

variables {I}

/-- When `f` is a localization map from `R` at the complement of a prime ideal `I`, we use a
copy of the localization map `f`'s codomain `S` carrying the data of `f` so that the `local_ring`
instance on `S` can 'know' the map needed to induce the instance. -/
instance at_prime.local_ring (f : at_prime S I) : local_ring f.codomain :=
local_of_nonunits_ideal
  (λ hze, begin
    rw [←f.to_map.map_one, ←f.to_map.map_zero] at hze,
    obtain ⟨t, ht⟩ := f.eq_iff_exists.1 hze,
    exact ((show (t : R) ∉ I, from t.2) (have htz : (t : R) = 0, by simpa using ht.symm,
      htz.symm ▸ I.zero_mem))
    end)
  (begin
    intros x y hx hy hu,
    cases is_unit_iff_exists_inv.1 hu with z hxyz,
    have : ∀ {r s}, f.mk' r s ∈ nonunits S → r ∈ I, from
      λ r s, (@not_imp_comm _ _ (classical.dec _) (classical.dec _)).1
        (λ nr, is_unit_iff_exists_inv.2 ⟨f.mk' s ⟨r, nr⟩, f.mk'_mul_mk'_eq_one' _ _ nr⟩),
    rcases f.mk'_surjective x with ⟨rx, sx, hrx⟩,
    rcases f.mk'_surjective y with ⟨ry, sy, hry⟩,
    rcases f.mk'_surjective z with ⟨rz, sz, hrz⟩,
    rw [←hrx, ←hry, ←hrz, ←f.mk'_add, ←f.mk'_mul,
        ←f.mk'_self I.prime_compl.one_mem] at hxyz,
    rw ←hrx at hx, rw ←hry at hy,
    cases f.eq.1 hxyz with t ht,
    simp only [mul_one, one_mul, submonoid.coe_mul, subtype.coe_mk] at ht,
    rw [←sub_eq_zero, ←sub_mul] at ht,
    have hr := (hp.mem_or_mem_of_mul_eq_zero ht).resolve_right t.2,
    have := I.neg_mem_iff.1 ((ideal.add_mem_iff_right _ _).1 hr),
    { exact not_or (mt hp.mem_or_mem (not_or sx.2 sy.2)) sz.2 (hp.mem_or_mem this)},
    { exact I.mul_mem_right (I.add_mem (I.mul_mem_right (this hx)) (I.mul_mem_right (this hy)))}
  end)

end localization_map
namespace localization

/-- The localization of `R` at the complement of a prime ideal is a local ring. -/
instance at_prime.local_ring : local_ring (localization I.prime_compl) :=
localization_map.at_prime.local_ring (of I.prime_compl)

end localization
end at_prime
namespace localization_map
variables (f : localization_map M S)

section ideals

theorem map_comap (J : ideal S) :
  ideal.map f.to_map (ideal.comap f.to_map J) = J :=
le_antisymm (ideal.map_le_iff_le_comap.2 (le_refl _)) $ λ x hJ,
begin
  obtain ⟨r, s, hx⟩ := f.mk'_surjective x,
  rw ←hx at ⊢ hJ,
  exact ideal.mul_mem_right _ (ideal.mem_map_of_mem (show f.to_map r ∈ J, from
    f.mk'_spec r s ▸ @ideal.mul_mem_right _ _ J (f.mk' r s) (f.to_map s) hJ)),
end

/-- If `S` is the localization of `R` at a submonoid, the ordering of ideals of `S` is
embedded in the ordering of ideals of `R`. -/
def le_order_embedding :
  ((≤) : ideal S → ideal S → Prop) ≼o
  ((≤) : ideal R → ideal R → Prop) :=
{ to_fun := λ J, ideal.comap f.to_map J,
  inj'   := function.left_inverse.injective f.map_comap,
  ord'   := λ J₁ J₂, ⟨ideal.comap_mono, λ hJ,
    f.map_comap J₁ ▸ f.map_comap J₂ ▸ ideal.map_mono hJ⟩ }

end ideals

/-!
### `algebra` section

Defines the `R`-algebra instance on a copy of `S` carrying the data of the localization map
`f` needed to induce the `R`-algebra structure. -/

/-- We use a copy of the localization map `f`'s codomain `S` carrying the data of `f` so that the
`R`-algebra instance on `S` can 'know' the map needed to induce the `R`-algebra structure. -/
instance : algebra R f.codomain := f.to_map.to_algebra

end localization_map
namespace localization

instance : algebra R (localization M) := localization_map.algebra (of M)

end localization
namespace localization_map
variables (f : localization_map M S)

@[simp] lemma of_id (a : R) :
  (algebra.of_id R f.codomain) a = f.to_map a :=
rfl

@[simp] lemma algebra_map_eq : algebra_map R f.codomain = f.to_map := rfl

variables (f)
/-- Localization map `f` from `R` to `S` as an `R`-linear map. -/
def lin_coe : R →ₗ[R] f.codomain :=
{ to_fun    := f.to_map,
  map_add'  := f.to_map.map_add,
  map_smul' := f.to_map.map_mul }

variables {f}

instance coe_submodules : has_coe (ideal R) (submodule R f.codomain) :=
⟨λ I, submodule.map f.lin_coe I⟩

lemma mem_coe (I : ideal R) {x : S} :
  x ∈ (I : submodule R f.codomain) ↔ ∃ y : R, y ∈ I ∧ f.to_map y = x :=
iff.rfl

@[simp] lemma lin_coe_apply {x} : f.lin_coe x = f.to_map x := rfl

variables {g : R →+* P}
variables {T : submonoid P} (hy : ∀ y : M, g y ∈ T) {Q : Type*} [comm_ring Q]
(k : localization_map T Q)

lemma map_smul (x : f.codomain) (z : R) :
  f.map hy k (z • x : f.codomain) = @has_scalar.smul P k.codomain _ (g z) (f.map hy k x) :=
show f.map hy k (f.to_map z * x) = k.to_map (g z) * f.map hy k x,
by rw [ring_hom.map_mul, map_eq]

section integer_normalization

open finsupp polynomial
open_locale classical

/-- `coeff_integer_normalization p` gives the coefficients of the polynomial
`integer_normalization p` -/
noncomputable def coeff_integer_normalization (p : polynomial f.codomain) (i : ℕ) : R :=
if hi : i ∈ p.support
then classical.some (classical.some_spec
      (f.exist_integer_multiples_of_finset (p.support.image p.coeff))
      (p.coeff i)
      (finset.mem_image.mpr ⟨i, hi, rfl⟩))
else 0

lemma coeff_integer_normalization_mem_support (p : polynomial f.codomain) (i : ℕ)
  (h : coeff_integer_normalization p i ≠ 0) : i ∈ p.support :=
begin
  contrapose h,
  rw [ne.def, not_not, coeff_integer_normalization, dif_neg h]
end

/-- `integer_normalization g` normalizes `g` to have integer coefficients
by clearing the denominators -/
noncomputable def integer_normalization : polynomial f.codomain → polynomial R :=
λ p, on_finset p.support (coeff_integer_normalization p) (coeff_integer_normalization_mem_support p)

@[simp]
lemma integer_normalization_coeff (p : polynomial f.codomain) (i : ℕ) :
  (integer_normalization p).coeff i = coeff_integer_normalization p i := rfl

lemma integer_normalization_spec (p : polynomial f.codomain) :
  ∃ (b : M), ∀ i, f.to_map ((integer_normalization p).coeff i) = f.to_map b * p.coeff i :=
begin
  use classical.some (f.exist_integer_multiples_of_finset (p.support.image p.coeff)),
  intro i,
  rw [integer_normalization_coeff, coeff_integer_normalization],
  split_ifs with hi,
  { exact classical.some_spec (classical.some_spec
      (f.exist_integer_multiples_of_finset (p.support.image p.coeff))
      (p.coeff i)
      (finset.mem_image.mpr ⟨i, hi, rfl⟩)) },
  { convert (_root_.mul_zero (f.to_map _)).symm,
    { exact f.to_ring_hom.map_zero },
    { exact finsupp.not_mem_support_iff.mp hi } }
end

lemma integer_normalization_map_to_map (p : polynomial f.codomain) :
  ∃ (b : M), (integer_normalization p).map f.to_map = f.to_map b • p :=
let ⟨b, hb⟩ := integer_normalization_spec p in
⟨b, polynomial.ext (λ i, by { rw coeff_map, exact hb i })⟩

variables {R' : Type*} [comm_ring R']

lemma integer_normalization_eval₂_eq_zero (g : f.codomain →+* R') (p : polynomial f.codomain)
  {x : R'} (hx : eval₂ g x p = 0) : eval₂ (g.comp f.to_map) x (integer_normalization p) = 0 :=
let ⟨b, hb⟩ := integer_normalization_map_to_map p in
trans (eval₂_map f.to_map g x).symm (by rw [hb, eval₂_smul, hx, smul_zero])

lemma integer_normalization_aeval_eq_zero [algebra R R'] [algebra f.codomain R']
  [is_algebra_tower R f.codomain R'] (p : polynomial f.codomain)
  {x : R'} (hx : aeval x p = 0) : aeval x (integer_normalization p) = 0 :=
by rw [aeval_def, is_algebra_tower.algebra_map_eq R f.codomain R', algebra_map_eq,
    integer_normalization_eval₂_eq_zero _ _ hx]

end integer_normalization

end localization_map
variables (R)

/-- The submonoid of non-zero-divisors of a `comm_ring` `R`. -/
def non_zero_divisors : submonoid R :=
{ carrier := {x | ∀ z, z * x = 0 → z = 0},
  one_mem' := λ z hz, by rwa mul_one at hz,
  mul_mem' := λ x₁ x₂ hx₁ hx₂ z hz,
    have z * x₁ * x₂ = 0, by rwa mul_assoc,
    hx₁ z $ hx₂ (z * x₁) this }

variables {R}

lemma mul_mem_non_zero_divisors {a b : R} :
  a * b ∈ non_zero_divisors R ↔ a ∈ non_zero_divisors R ∧ b ∈ non_zero_divisors R :=
begin
  split,
  { intro h,
    split; intros x h'; apply h,
    { rw [←mul_assoc, h', zero_mul] },
    { rw [mul_comm a b, ←mul_assoc, h', zero_mul] } },
  { rintros ⟨ha, hb⟩ x hx,
    apply ha,
    apply hb,
    rw [mul_assoc, hx] },
end

variables (R) {A : Type*} [integral_domain A]

lemma eq_zero_of_ne_zero_of_mul_eq_zero
  {x y : A} (hnx : x ≠ 0) (hxy : y * x = 0) :
  y = 0 := or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

lemma mem_non_zero_divisors_iff_ne_zero {x : A} :
  x ∈ non_zero_divisors A ↔ x ≠ 0 :=
⟨λ hm hz, zero_ne_one (hm 1 $ by rw [hz, one_mul]).symm,
λ hnx z, eq_zero_of_ne_zero_of_mul_eq_zero hnx⟩

lemma map_ne_zero_of_mem_non_zero_divisors {B : Type*} [ring B] {g : A →+* B}
  (hg : injective g) {x : non_zero_divisors A} : g x ≠ 0 :=
λ h0, mem_non_zero_divisors_iff_ne_zero.1 x.2 $ g.injective_iff.1 hg x h0

lemma map_mem_non_zero_divisors {B : Type*} [integral_domain B] {g : A →+* B}
  (hg : injective g) {x : non_zero_divisors A} : g x ∈ non_zero_divisors B :=
λ z hz, eq_zero_of_ne_zero_of_mul_eq_zero
  (map_ne_zero_of_mem_non_zero_divisors hg) hz

variables (K : Type*)

/-- Localization map from an integral domain `R` to its field of fractions. -/
@[reducible] def fraction_map [comm_ring K] := localization_map (non_zero_divisors R) K

namespace fraction_map
open localization_map
variables {R K}

lemma to_map_eq_zero_iff [comm_ring K] (φ : fraction_map R K) {x : R} :
  x = 0 ↔ φ.to_map x = 0 :=
begin
  rw ← φ.to_map.map_zero,
  split; intro h,
  { rw h },
  { cases φ.eq_iff_exists.mp h with c hc,
    rw zero_mul at hc,
    exact c.2 x hc }
end

protected theorem injective [comm_ring K] (φ : fraction_map R K) :
  injective φ.to_map :=
φ.to_map.injective_iff.2 (λ _ h, φ.to_map_eq_zero_iff.mpr h)

protected lemma map_ne_zero_of_mem_non_zero_divisors [comm_ring K] (φ : fraction_map A K)
  (x : non_zero_divisors A) : φ.to_map x ≠ 0 :=
map_ne_zero_of_mem_non_zero_divisors φ.injective

local attribute [instance] classical.dec_eq

/-- A `comm_ring` `K` which is the localization of an integral domain `R` at `R - {0}` is an
integral domain. -/
def to_integral_domain [comm_ring K] (φ : fraction_map A K) : integral_domain K :=
{ eq_zero_or_eq_zero_of_mul_eq_zero :=
    begin
      intros z w h,
      cases φ.surj z with x hx,
      cases φ.surj w with y hy,
      have : z * w * φ.to_map y.2 * φ.to_map x.2 = φ.to_map x.1 * φ.to_map y.1, by
        rw [mul_assoc z, hy, ←hx]; ac_refl,
      erw h at this,
      rw [zero_mul, zero_mul, ←φ.to_map.map_mul] at this,
      cases eq_zero_or_eq_zero_of_mul_eq_zero (φ.to_map_eq_zero_iff.mpr this.symm) with H H,
        { exact or.inl (φ.eq_zero_of_fst_eq_zero hx H) },
      { exact or.inr (φ.eq_zero_of_fst_eq_zero hy H) },
    end,
  exists_pair_ne := ⟨φ.to_map 0, φ.to_map 1, λ h, zero_ne_one (φ.injective h)⟩,
  ..(infer_instance : comm_ring K) }

/-- The inverse of an element in the field of fractions of an integral domain. -/
protected noncomputable def inv [comm_ring K] (φ : fraction_map A K) (z : K) : K :=
if h : z = 0 then 0 else
φ.mk' (φ.to_localization_map.sec z).2 ⟨(φ.to_localization_map.sec z).1,
  mem_non_zero_divisors_iff_ne_zero.2 $ λ h0, h $ φ.eq_zero_of_fst_eq_zero (sec_spec z) h0⟩

protected lemma mul_inv_cancel [comm_ring K] (φ : fraction_map A K) (x : K) (hx : x ≠ 0) :
  x * φ.inv x = 1 :=
show x * dite _ _ _ = 1, by rw [dif_neg hx,
  ←is_unit.mul_left_inj (φ.map_units ⟨(φ.to_localization_map.sec x).1,
    mem_non_zero_divisors_iff_ne_zero.2 $ λ h0, hx $ φ.eq_zero_of_fst_eq_zero (sec_spec x) h0⟩),
  one_mul, mul_assoc, mk'_spec, ←eq_mk'_iff_mul_eq]; exact (φ.mk'_sec x).symm

/-- A `comm_ring` `K` which is the localization of an integral domain `R` at `R - {0}` is a
field. -/
noncomputable def to_field [comm_ring K] (φ : fraction_map A K) : field K :=
{ inv := φ.inv,
  mul_inv_cancel := φ.mul_inv_cancel,
  inv_zero := dif_pos rfl, ..φ.to_integral_domain }

variables {B : Type*} [integral_domain B] [field K] {L : Type*} [field L]
  (f : fraction_map A K) {g : A →+* L}

lemma mk'_eq_div {r s} : f.mk' r s = f.to_map r / f.to_map s :=
f.mk'_eq_iff_eq_mul.2 $ (div_mul_cancel _
    (f.map_ne_zero_of_mem_non_zero_divisors _)).symm

lemma is_unit_map_of_injective (hg : injective g)
  (y : non_zero_divisors A) : is_unit (g y) :=
is_unit.mk0 (g y) $ map_ne_zero_of_mem_non_zero_divisors hg

/-- Given an integral domain `A`, a localization map to its fields of fractions
`f : A →+* K`, and an injective ring hom `g : A →+* L` where `L` is a field, we get a
field hom sending `z : K` to `g x * (g y)⁻¹`, where `(x, y) : A × (non_zero_divisors A)` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def lift (hg : injective g) : K →+* L :=
f.lift $ is_unit_map_of_injective hg

/-- Given an integral domain `A`, a localization map to its fields of fractions
`f : A →+* K`, and an injective ring hom `g : A →+* L` where `L` is a field,
field hom induced from `K` to `L` maps `f x / f y` to `g x / g y` for all
`x : A, y ∈ non_zero_divisors A`. -/
@[simp] lemma lift_mk' (hg : injective g) (x y) :
  f.lift hg (f.mk' x y) = g x / g y :=
begin
  erw f.lift_mk' (is_unit_map_of_injective hg),
  erw submonoid.localization_map.mul_inv_left
  (λ y : non_zero_divisors A, show is_unit (g.to_monoid_hom y), from
    is_unit_map_of_injective hg y),
  exact (mul_div_cancel' _ (map_ne_zero_of_mem_non_zero_divisors hg)).symm,
end

/-- Given integral domains `A, B` and localization maps to their fields of fractions
`f : A →+* K, g : B →+* L` and an injective ring hom `j : A →+* B`, we get a field hom
sending `z : K` to `g (j x) * (g (j y))⁻¹`, where `(x, y) : A × (non_zero_divisors A)` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def map (g : fraction_map B L) {j : A →+* B} (hj : injective j) :
  K →+* L :=
f.map (λ y, mem_non_zero_divisors_iff_ne_zero.2 $
  map_ne_zero_of_mem_non_zero_divisors hj) g

/-- Given integral domains `A, B` and localization maps to their fields of fractions
`f : A →+* K, g : B →+* L`, an isomorphism `j : A ≃+* B` induces an isomorphism of
fields of fractions `K ≃+* L`. -/
noncomputable def field_equiv_of_ring_equiv (g : fraction_map B L) (h : A ≃+* B) :
  K ≃+* L :=
f.ring_equiv_of_ring_equiv g h
begin
  ext b,
  show b ∈ h.to_equiv '' _ ↔ _,
  erw [h.to_equiv.image_eq_preimage, set.preimage, set.mem_set_of_eq,
       mem_non_zero_divisors_iff_ne_zero, mem_non_zero_divisors_iff_ne_zero],
  exact h.symm.map_ne_zero_iff
end
/-- The cast from `int` to `rat` as a `fraction_map`. -/
def int.fraction_map : fraction_map ℤ ℚ :=
{ to_fun := coe,
  map_units' :=
  begin
    rintro ⟨x, hx⟩,
    rw [submonoid.mem_carrier, mem_non_zero_divisors_iff_ne_zero] at hx,
    simpa only [is_unit_iff_ne_zero, int.cast_eq_zero, ne.def, subtype.coe_mk] using hx,
  end,
  surj' :=
  begin
    rintro ⟨n, d, hd, h⟩,
    refine ⟨⟨n, ⟨d, _⟩⟩, rat.mul_denom_eq_num⟩,
    rwa [submonoid.mem_carrier, mem_non_zero_divisors_iff_ne_zero, int.coe_nat_ne_zero_iff_pos]
  end,
  eq_iff_exists' :=
  begin
    intros x y,
    rw [int.cast_inj],
    refine ⟨by { rintro rfl, use 1 }, _⟩,
    rintro ⟨⟨c, hc⟩, h⟩,
    apply int.eq_of_mul_eq_mul_right _ h,
    rwa [submonoid.mem_carrier, mem_non_zero_divisors_iff_ne_zero] at hc,
  end,
  ..int.cast_ring_hom ℚ }

lemma integer_normalization_eq_zero_iff {p : polynomial f.codomain} :
  integer_normalization p = 0 ↔ p = 0 :=
begin
  refine (polynomial.ext_iff.trans (polynomial.ext_iff.trans _).symm),
  obtain ⟨⟨b, nonzero⟩, hb⟩ := integer_normalization_spec p,
  split; intros h i,
  { apply f.to_map_eq_zero_iff.mpr,
    rw [hb i, h i],
    exact _root_.mul_zero _ },
  { have hi := h i,
    rw [polynomial.coeff_zero, f.to_map_eq_zero_iff, hb i] at hi,
    apply or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hi),
    intro h,
    apply mem_non_zero_divisors_iff_ne_zero.mp nonzero,
    exact f.to_map_eq_zero_iff.mpr h }
end

/-- A field is algebraic over the ring `A` iff it is algebraic over the field of fractions of `A`. -/
lemma comap_is_algebraic_iff [algebra A L] [algebra f.codomain L] [is_algebra_tower A f.codomain L] :
  algebra.is_algebraic A L ↔ algebra.is_algebraic f.codomain L :=
begin
  split; intros h x; obtain ⟨p, hp, px⟩ := h x,
  { refine ⟨p.map f.to_map, λ h, hp (polynomial.ext (λ i, _)), _⟩,
  { have : f.to_map (p.coeff i) = 0 := trans (polynomial.coeff_map _ _).symm (by simp [h]),
    exact f.to_map_eq_zero_iff.mpr this },
  { rwa [is_algebra_tower.aeval_apply _ f.codomain, algebra_map_eq] at px } },
  { exact ⟨integer_normalization p,
           mt f.integer_normalization_eq_zero_iff.mp hp,
           integer_normalization_aeval_eq_zero p px⟩ },
end

section num_denom

variables [unique_factorization_domain A] (φ : fraction_map A K)

lemma exists_reduced_fraction (x : φ.codomain) :
  ∃ (a : A) (b : non_zero_divisors A),
  (∀ {d}, d ∣ a → d ∣ b → is_unit d) ∧ φ.mk' a b = x :=
begin
  obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := φ.exists_integer_multiple x,
  obtain ⟨a', b', c', no_factor, rfl, rfl⟩ :=
    unique_factorization_domain.exists_reduced_factors' a b
      (mem_non_zero_divisors_iff_ne_zero.mp b_nonzero),
  obtain ⟨c'_nonzero, b'_nonzero⟩ := mul_mem_non_zero_divisors.mp b_nonzero,
  refine ⟨a', ⟨b', b'_nonzero⟩, @no_factor, _⟩,
  apply mul_left_cancel' (φ.map_ne_zero_of_mem_non_zero_divisors ⟨c' * b', b_nonzero⟩),
  simp only [subtype.coe_mk, φ.to_map.map_mul] at *,
  erw [←hab, mul_assoc, φ.mk'_spec' a' ⟨b', b'_nonzero⟩],
end

/-- `f.num x` is the numerator of `x : f.codomain` as a reduced fraction. -/
noncomputable def num (x : φ.codomain) : A :=
classical.some (φ.exists_reduced_fraction x)

/-- `f.num x` is the denominator of `x : f.codomain` as a reduced fraction. -/
noncomputable def denom (x : φ.codomain) : non_zero_divisors A :=
classical.some (classical.some_spec (φ.exists_reduced_fraction x))

lemma num_denom_reduced (x : φ.codomain) :
  ∀ {d}, d ∣ φ.num x → d ∣ φ.denom x → is_unit d :=
(classical.some_spec (classical.some_spec (φ.exists_reduced_fraction x))).1

@[simp] lemma mk'_num_denom (x : φ.codomain) : φ.mk' (φ.num x) (φ.denom x) = x :=
(classical.some_spec (classical.some_spec (φ.exists_reduced_fraction x))).2

lemma num_mul_denom_eq_num_iff_eq {x y : φ.codomain} :
  x * φ.to_map (φ.denom y) = φ.to_map (φ.num y) ↔ x = y :=
⟨ λ h, by simpa only [mk'_num_denom] using φ.eq_mk'_iff_mul_eq.mpr h,
  λ h, φ.eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_denom]) ⟩

lemma num_mul_denom_eq_num_iff_eq' {x y : φ.codomain} :
  y * φ.to_map (φ.denom x) = φ.to_map (φ.num x) ↔ x = y :=
⟨ λ h, by simpa only [eq_comm, mk'_num_denom] using φ.eq_mk'_iff_mul_eq.mpr h,
  λ h, φ.eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_denom]) ⟩

lemma num_mul_denom_eq_num_mul_denom_iff_eq {x y : φ.codomain} :
  φ.num y * φ.denom x = φ.num x * φ.denom y ↔ x = y :=
⟨ λ h, by simpa only [mk'_num_denom] using φ.mk'_eq_of_eq h,
  λ h, by rw h ⟩

lemma eq_zero_of_num_eq_zero {x : φ.codomain} (h : φ.num x = 0) : x = 0 :=
φ.num_mul_denom_eq_num_iff_eq'.mp (by rw [zero_mul, h, ring_hom.map_zero])

lemma is_integer_of_is_unit_denom {x : φ.codomain} (h : is_unit (φ.denom x : A)) : φ.is_integer x :=
begin
  cases h with d hd,
  have d_ne_zero : φ.to_map (φ.denom x) ≠ 0 := φ.map_ne_zero_of_mem_non_zero_divisors (φ.denom x),
  use ↑d⁻¹ * φ.num x,
  refine trans _ (φ.mk'_num_denom x),
  rw [φ.to_map.map_mul, φ.to_map.map_units_inv, hd],
  apply mul_left_cancel' d_ne_zero,
  rw [←mul_assoc, mul_inv_cancel d_ne_zero, one_mul, φ.mk'_spec']
end

lemma is_unit_denom_of_num_eq_zero {x : φ.codomain} (h : φ.num x = 0) : is_unit (φ.denom x : A) :=
φ.num_denom_reduced x (h.symm ▸ dvd_zero _) (dvd_refl _)

end num_denom

end fraction_map

namespace integral_closure

variables {L : Type*} [field K] [field L] {f : fraction_map A K}

open algebra

/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
def fraction_map_of_algebraic [algebra A L] (alg : is_algebraic A L)
  (inj : ∀ x, algebra_map A L x = 0 → x = 0) :
  fraction_map (integral_closure A L) L :=
(algebra_map (integral_closure A L) L).to_localization_map
  (λ ⟨⟨y, integral⟩, nonzero⟩,
    have y ≠ 0 := λ h, mem_non_zero_divisors_iff_ne_zero.mp nonzero (subtype.ext_iff_val.mpr h),
    show is_unit y, from ⟨⟨y, y⁻¹, mul_inv_cancel this, inv_mul_cancel this⟩, rfl⟩)
  (λ z, let ⟨x, y, hy, hxy⟩ := exists_integral_multiple (alg z) inj in
    ⟨⟨x, ⟨y, mem_non_zero_divisors_iff_ne_zero.mpr hy⟩⟩, hxy⟩)
  (λ x y, ⟨ λ (h : x.1 = y.1), ⟨1, by simpa using subtype.ext_iff_val.mpr h⟩,
            λ ⟨c, hc⟩, congr_arg (algebra_map _ L)
              (mul_right_cancel' (mem_non_zero_divisors_iff_ne_zero.mp c.2) hc) ⟩)

/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
def fraction_map_of_finite_extension [algebra A L] [algebra f.codomain L]
  [is_algebra_tower A f.codomain L] [finite_dimensional f.codomain L] :
  fraction_map (integral_closure A L) L :=
fraction_map_of_algebraic
  (f.comap_is_algebraic_iff.mpr is_algebraic_of_finite)
  (λ x hx, f.to_map_eq_zero_iff.mpr ((algebra_map f.codomain L).map_eq_zero.mp $
    (is_algebra_tower.algebra_map_apply _ _ _ _).symm.trans hx))

end integral_closure

variables (A)

/-- The fraction field of an integral domain as a quotient type. -/
@[reducible] def fraction_ring := localization (non_zero_divisors A)

/-- Natural hom sending `x : A`, `A` an integral domain, to the equivalence class of
`(x, 1)` in the field of fractions of `A`. -/
def of : fraction_map A (localization (non_zero_divisors A)) :=
localization.of (non_zero_divisors A)

namespace fraction_ring

variables {A}

noncomputable instance : field (fraction_ring A) :=
(of A).to_field

@[simp] lemma mk_eq_div {r s} : (localization.mk r s : fraction_ring A) =
  ((of A).to_map r / (of A).to_map s : fraction_ring A) :=
by erw [localization.mk_eq_mk', (of A).mk'_eq_div]

/-- Given an integral domain `A` and a localization map to a field of fractions
`f : A →+* K`, we get an isomorphism between the field of fractions of `A` as a quotient
type and `K`. -/
noncomputable def field_equiv_of_quotient {K : Type*} [field K] (f : fraction_map A K) :
  fraction_ring A ≃+* K :=
localization.ring_equiv_of_quotient f

end fraction_ring
