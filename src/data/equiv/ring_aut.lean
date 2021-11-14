/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import data.equiv.mul_add_aut
import data.equiv.ring

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

end ring_aut
