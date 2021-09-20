/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.algebra.subalgebra
import topology.algebra.module

/-!
# Topological (sub)algebras

A topological algebra over a topological semiring `R` is a topological ring with a compatible
continuous scalar multiplication by elements of `R`. We reuse typeclass `has_continuous_smul` for
topological algebras.

## Results

This is just a minimal stub for now!

The topological closure of a subalgebra is still a subalgebra,
which as an algebra is a topological algebra.
-/

open classical set topological_space algebra
open_locale classical

universes u v w

section topological_algebra
variables (R : Type*) [topological_space R] [comm_semiring R]
variables (A : Type u) [topological_space A]
variables [semiring A]

lemma continuous_algebra_map_iff_smul [algebra R A] [topological_ring A] :
  continuous (algebra_map R A) ↔ continuous (λ p : R × A, p.1 • p.2) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { simp only [algebra.smul_def], exact (h.comp continuous_fst).mul continuous_snd },
  { rw algebra_map_eq_smul_one', exact h.comp (continuous_id.prod_mk continuous_const) }
end

@[continuity]
lemma continuous_algebra_map [algebra R A] [topological_ring A] [has_continuous_smul R A] :
  continuous (algebra_map R A) :=
(continuous_algebra_map_iff_smul R A).2 continuous_smul

lemma has_continuous_smul_of_algebra_map [algebra R A] [topological_ring A]
  (h : continuous (algebra_map R A)) :
  has_continuous_smul R A :=
⟨(continuous_algebra_map_iff_smul R A).1 h⟩

end topological_algebra

section topological_algebra
variables {R : Type*} [comm_semiring R]
variables {A : Type u} [topological_space A]
variables [semiring A]
variables [algebra R A] [topological_ring A]

/-- The closure of a subalgebra in a topological algebra as a subalgebra. -/
def subalgebra.topological_closure (s : subalgebra R A) : subalgebra R A :=
{ carrier := closure (s : set A),
  algebra_map_mem' := λ r, s.to_subsemiring.subring_topological_closure (s.algebra_map_mem r),
  .. s.to_subsemiring.topological_closure }

@[simp] lemma subalgebra.topological_closure_coe (s : subalgebra R A) :
  (s.topological_closure : set A) = closure (s : set A) :=
rfl

instance subalgebra.topological_closure_topological_ring (s : subalgebra R A) :
  topological_ring (s.topological_closure) :=
s.to_subsemiring.topological_closure_topological_ring

instance subalgebra.topological_closure_topological_algebra
  [topological_space R] [has_continuous_smul R A] (s : subalgebra R A) :
  has_continuous_smul R (s.topological_closure) :=
s.to_submodule.topological_closure_has_continuous_smul

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
This is really a statement about topological algebra isomorphisms,
but we don't have those, so we use the clunky approach of talking about
an algebra homomorphism, and a separate homeomorphism,
along with a witness that as functions they are the same.
-/
lemma subalgebra.topological_closure_comap'_homeomorph
  (s : subalgebra R A)
  {B : Type*} [topological_space B] [ring B] [topological_ring B] [algebra R B]
  (f : B →ₐ[R] A) (f' : B ≃ₜ A) (w : (f : B → A) = f') :
  s.topological_closure.comap' f = (s.comap' f).topological_closure :=
begin
  apply set_like.ext',
  simp only [subalgebra.topological_closure_coe],
  simp only [subalgebra.coe_comap, subsemiring.coe_comap, alg_hom.coe_to_ring_hom],
  rw [w],
  exact f'.preimage_closure _,
end

end topological_algebra
