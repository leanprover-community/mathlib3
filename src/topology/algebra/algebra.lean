/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.algebra.subalgebra
import topology.algebra.module

/-!
# Topological (sub)algebras

A topological algebra over a topological ring `R` is a
topological ring with a compatible continuous scalar multiplication by elements of `R`.

## Results

This is just a minimal stub for now!

The topological closure of a subalgebra is still a subalgebra,
which as an algebra is a topological algebra.
-/

open classical set topological_space algebra
open_locale classical

universes u v w
variables (R : Type*) [topological_space R] [comm_ring R] [topological_ring R]
variables (A : Type u) [topological_space A]
variables [ring A]

section topological_algebra

/-- A topological algebra over a topological ring `R` is a
topological ring with a compatible continuous scalar multiplication by elements of `R`. -/
class topological_algebra [algebra R A] [topological_ring A] : Prop :=
(continuous_algebra_map : continuous (algebra_map R A))

attribute [continuity] topological_algebra.continuous_algebra_map

end topological_algebra

section topological_algebra
variables {R A} [algebra R A] [topological_ring A]

@[priority 200] -- see Note [lower instance priority]
instance topological_algebra.to_topological_module [topological_algebra R A] :
  topological_semimodule R A :=
{ continuous_smul := begin
    simp_rw algebra.smul_def,
    continuity,
  end, }

/-- The closure of a subalgebra in a topological algebra as a subalgebra. -/
def subalgebra.topological_closure (s : subalgebra R A) : subalgebra R A :=
{ carrier := closure (s : set A),
  algebra_map_mem' := λ r, s.to_subring.subring_topological_closure (s.algebra_map_mem r),
  ..s.to_subring.topological_closure }

instance subalgebra.topological_closure_topological_ring (s : subalgebra R A) :
  topological_ring (s.topological_closure) :=
s.to_subring.topological_closure_topological_ring

instance subalgebra.topological_closure_topological_algebra
  [topological_algebra R A] (s : subalgebra R A) :
  topological_algebra R (s.topological_closure) :=
{ continuous_algebra_map :=
  begin
    change continuous (λ r, _),
    continuity,
  end }

lemma subalgebra.subring_topological_closure (s : subalgebra R A) :
  s ≤ s.topological_closure :=
subset_closure

lemma subalgebra.is_closed_topological_closure (s : subalgebra R A) :
  is_closed (s.topological_closure : set A) :=
by convert is_closed_closure

lemma subalgebra.topological_closure_minimal
  (s : subalgebra R A) {t : subalgebra R A} (h : s ≤ t) (ht : is_closed (t : set A)) :
  s.topological_closure ≤ t :=
closure_minimal h ht

end topological_algebra
