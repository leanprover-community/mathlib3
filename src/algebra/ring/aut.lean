/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import algebra.hom.aut
import algebra.ring.equiv
import algebra.group_ring_action

/-!
# Ring automorphisms

This file defines the automorphism group structure on `ring_aut R := ring_equiv R R`.

## Implementation notes

The definition of multiplication in the automorphism group agrees with function composition,
multiplication in `equiv.perm`, and multiplication in `category_theory.End`, but not with
`category_theory.comp`.

This file is kept separate from `data/equiv/ring` so that `group_theory.perm` is free to use
equivalences (and other files that use them) before the group structure is defined.

## Tags

ring_aut
-/

/-- The group of ring automorphisms. -/
@[reducible] def ring_aut (R : Type*) [has_mul R] [has_add R] := ring_equiv R R

namespace ring_aut
variables (R : Type*) [has_mul R] [has_add R]

/--
The group operation on automorphisms of a ring is defined by
`λ g h, ring_equiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance : group (ring_aut R) :=
by refine_struct
{ mul := λ g h, ring_equiv.trans h g,
  one := ring_equiv.refl R,
  inv := ring_equiv.symm,
  div := _,
  npow := @npow_rec _ ⟨ring_equiv.refl R⟩ ⟨λ g h, ring_equiv.trans h g⟩,
  zpow := @zpow_rec _ ⟨ring_equiv.refl R⟩ ⟨λ g h, ring_equiv.trans h g⟩ ⟨ring_equiv.symm⟩ };
intros; ext; try { refl }; apply equiv.left_inv

instance : inhabited (ring_aut R) := ⟨1⟩

/-- Monoid homomorphism from ring automorphisms to additive automorphisms. -/
def to_add_aut : ring_aut R →* add_aut R :=
by refine_struct { to_fun := ring_equiv.to_add_equiv }; intros; refl

/-- Monoid homomorphism from ring automorphisms to multiplicative automorphisms. -/
def to_mul_aut : ring_aut R →* mul_aut R :=
by refine_struct { to_fun := ring_equiv.to_mul_equiv }; intros; refl

/-- Monoid homomorphism from ring automorphisms to permutations. -/
def to_perm : ring_aut R →* equiv.perm R :=
by refine_struct { to_fun := ring_equiv.to_equiv }; intros; refl

/-- The tautological action by the group of automorphism of a ring `R` on `R`.-/
instance apply_mul_semiring_action {R : Type*} [semiring R] : mul_semiring_action (ring_aut R) R :=
{ smul := ($),
  smul_zero := ring_equiv.map_zero,
  smul_add := ring_equiv.map_add,
  smul_one := ring_equiv.map_one,
  smul_mul := ring_equiv.map_mul,
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl }

@[simp] protected lemma smul_def {R : Type*} [ring R] (f : ring_aut R) (r : R) : f • r = f r := rfl

instance apply_has_faithful_smul {R : Type*} [ring R] : has_faithful_smul (ring_aut R) R :=
 ⟨λ _ _, ring_equiv.ext⟩

end ring_aut
