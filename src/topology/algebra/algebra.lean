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

section topological_algebra
variables (R : Type*) [topological_space R] [comm_ring R] [topological_ring R]
variables (A : Type u) [topological_space A]
variables [ring A]

/-- A topological algebra over a topological ring `R` is a
topological ring with a compatible continuous scalar multiplication by elements of `R`. -/
class topological_algebra [algebra R A] [topological_ring A] : Prop :=
(continuous_algebra_map : continuous (algebra_map R A))

attribute [continuity] topological_algebra.continuous_algebra_map

end topological_algebra

section topological_algebra
variables {R : Type*} [comm_ring R]
variables {A : Type u} [topological_space A]
variables [ring A]
variables [algebra R A] [topological_ring A]

@[priority 200] -- see Note [lower instance priority]
instance topological_algebra.to_topological_module
  [topological_space R] [topological_ring R] [topological_algebra R A] :
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

@[simp] lemma subalgebra.topological_closure_coe (s : subalgebra R A) :
  (s.topological_closure : set A) = closure (s : set A) :=
rfl

instance subalgebra.topological_closure_topological_ring (s : subalgebra R A) :
  topological_ring (s.topological_closure) :=
s.to_subring.topological_closure_topological_ring

instance subalgebra.topological_closure_topological_algebra
  [topological_space R] [topological_ring R] [topological_algebra R A] (s : subalgebra R A) :
  topological_algebra R (s.topological_closure) :=
{ continuous_algebra_map :=
  begin
    change continuous (λ r, _),
    continuity,
  end }

lemma subalgebra.subalgebra_topological_closure (s : subalgebra R A) :
  s ≤ s.topological_closure :=
subset_closure

lemma subalgebra.is_closed_topological_closure (s : subalgebra R A) :
  is_closed (s.topological_closure : set A) :=
by convert is_closed_closure

lemma subalgebra.topological_closure_minimal
  (s : subalgebra R A) {t : subalgebra R A} (h : s ≤ t) (ht : is_closed (t : set A)) :
  s.topological_closure ≤ t :=
closure_minimal h ht

/--
This is really a statement about topological algebra isomorphisms, but we don't have those,
so we use the clunky approach of talking about
an algebra homomorphism, and a separate homeomorphism, along with
a witness that as functions they are the same.
-/
lemma subalgebra.topological_closure_comap'_homeomorph
  (s : subalgebra R A)
  {B : Type*} [topological_space B] [ring B] [topological_ring B] [algebra R B]
  (f : B →ₐ[R] A) (f' : B ≃ₜ A) (w : (f : B → A) = f') :
  s.topological_closure.comap' f = (s.comap' f).topological_closure :=
begin
  apply subalgebra.ext_set,
  simp only [subalgebra.topological_closure_coe],
  simp only [subalgebra.coe_comap', subsemiring.coe_comap, alg_hom.coe_to_ring_hom],
  rw [w],
  exact f'.preimage_closure _,
end

end topological_algebra
