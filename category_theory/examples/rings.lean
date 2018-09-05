/- Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl

Introduce CommRing -- the category of commutative rings.

Currently only the basic setup.
-/

import category_theory.functor
import algebra.ring
import analysis.topology.topological_structures

open category_theory

namespace category_theory.examples

@[reducible] def {u} CommRing : Type (u + 1) := Σ α : Type u, comm_ring α

@[reducible] def is_comm_ring_hom {α β} [comm_ring α] [comm_ring β] (f : α → β) : Prop :=
is_ring_hom f

instance : concrete_category @is_comm_ring_hom :=
⟨by introsI α ia; exact is_ring_hom.id,
  by introsI α β γ ia ib ic f g hf hg; exact is_ring_hom.comp f g⟩

instance : large_category CommRing := infer_instance

instance (R : CommRing) : comm_ring R.1 := R.2

instance (R S : CommRing) (f : category.hom R S) : is_ring_hom f.1 := f.2

@[simp] lemma comm_ring_hom.map_mul (R S : CommRing) (f : category.hom R S) (x y : R.1) :
  f.1 (x * y) = (f.1 x) * (f.1 y) :=
by rw f.2.map_mul
@[simp] lemma comm_ring_hom.map_add (R S : CommRing) (f : category.hom R S) (x y : R.1) :
  f.1 (x + y) = (f.1 x) + (f.1 y) :=
by rw f.2.map_add
@[simp] lemma comm_ring_hom.map_one (R S : CommRing) (f : category.hom R S) : f.1 1 = 1 :=
by rw f.2.map_one

end category_theory.examples
