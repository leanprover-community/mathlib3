-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.functor
import algebra.ring
import analysis.topology.topological_structures

open category_theory

namespace category_theory.examples

universe u₁

def CommRing : Type (u₁+1) := Σ α : Type u₁, comm_ring α

instance comm_ring_from_CommRing (R : CommRing) : comm_ring R.1 := R.2

structure comm_ring_hom (R S : CommRing.{u₁}) : Type u₁ :=
(map: R.1 → S.1)
(is_ring_hom : is_ring_hom map . obviously)

instance (R S : CommRing.{u₁}) (f : comm_ring_hom R S) : is_ring_hom f.map := f.is_ring_hom

@[simp] lemma comm_ring_hom.map_mul (R S : CommRing.{u₁}) (f : comm_ring_hom R S) (x y : R.1) : 
  f.map(x * y) = (f.map x) * (f.map y) := 
by rw f.is_ring_hom.map_mul
@[simp] lemma comm_ring_hom.map_add (R S : CommRing.{u₁}) (f : comm_ring_hom R S) (x y : R.1) : 
  f.map(x + y) = (f.map x) + (f.map y) := 
by rw f.is_ring_hom.map_add
@[simp] lemma comm_ring_hom.map_one (R S : CommRing.{u₁}) (f : comm_ring_hom R S) : f.map 1 = 1 := 
by rw f.is_ring_hom.map_one

def comm_ring_hom.id (R : CommRing) : comm_ring_hom R R :=
{ map := id }

@[simp] lemma comm_ring_hom.id_map (R : CommRing) (r : R.1) : (comm_ring_hom.id R).map r = r := rfl

def comm_ring_hom.comp {R S T : CommRing} (f: comm_ring_hom R S) (g : comm_ring_hom S T) : comm_ring_hom R T :=
{ map := λ x, g.map (f.map x) }

@[simp] lemma comm_ring_hom.comp_map {R S T: CommRing} (f : comm_ring_hom R S) (g : comm_ring_hom S T) (r : R.1) : 
  (comm_ring_hom.comp f g).map r = g.map (f.map r) := rfl

@[extensionality] lemma comm_ring_hom.ext {R S : CommRing} (f g : comm_ring_hom R S) (w : ∀ x : R.1, f.map x = g.map x) : f = g :=
begin
    induction f with fc,
    induction g with gc,
    tidy,
end

instance : large_category CommRing := 
{ hom  := comm_ring_hom,
  id   := comm_ring_hom.id,
  comp := @comm_ring_hom.comp }

end category_theory.examples
