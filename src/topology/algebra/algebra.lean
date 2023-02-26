/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.algebra.subalgebra.basic
import topology.algebra.module.basic
import ring_theory.adjoin.basic

/-!
# Topological (sub)algebras

A topological algebra over a topological semiring `R` is a topological semiring with a compatible
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
variables (R : Type*) (A : Type u)
variables [comm_semiring R] [semiring A] [algebra R A]
variables [topological_space R] [topological_space A] [topological_semiring A]

lemma continuous_algebra_map_iff_smul :
  continuous (algebra_map R A) ↔ continuous (λ p : R × A, p.1 • p.2) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { simp only [algebra.smul_def], exact (h.comp continuous_fst).mul continuous_snd },
  { rw algebra_map_eq_smul_one', exact h.comp (continuous_id.prod_mk continuous_const) }
end

@[continuity]
lemma continuous_algebra_map [has_continuous_smul R A] :
  continuous (algebra_map R A) :=
(continuous_algebra_map_iff_smul R A).2 continuous_smul

lemma has_continuous_smul_of_algebra_map (h : continuous (algebra_map R A)) :
  has_continuous_smul R A :=
⟨(continuous_algebra_map_iff_smul R A).1 h⟩

variables [has_continuous_smul R A]

/-- The inclusion of the base ring in a topological algebra as a continuous linear map. -/
@[simps]
def algebra_map_clm : R →L[R] A :=
{ to_fun := algebra_map R A,
  cont := continuous_algebra_map R A,
  .. algebra.linear_map R A }

lemma algebra_map_clm_coe : ⇑(algebra_map_clm R A) = algebra_map R A := rfl

lemma algebra_map_clm_to_linear_map :
  (algebra_map_clm R A).to_linear_map = algebra.linear_map R A := rfl

end topological_algebra

section topological_algebra
variables {R : Type*} [comm_semiring R]
variables {A : Type u} [topological_space A]
variables [semiring A] [algebra R A]

instance subalgebra.has_continuous_smul [topological_space R] [has_continuous_smul R A]
  (s : subalgebra R A) :
  has_continuous_smul R s :=
s.to_submodule.has_continuous_smul

variables [topological_semiring A]

/-- The closure of a subalgebra in a topological algebra as a subalgebra. -/
def subalgebra.topological_closure (s : subalgebra R A) : subalgebra R A :=
{ carrier := closure (s : set A),
  algebra_map_mem' := λ r, s.to_subsemiring.le_topological_closure (s.algebra_map_mem r),
  .. s.to_subsemiring.topological_closure }

@[simp] lemma subalgebra.topological_closure_coe (s : subalgebra R A) :
  (s.topological_closure : set A) = closure (s : set A) :=
rfl

instance subalgebra.topological_semiring (s : subalgebra R A) : topological_semiring s :=
s.to_subsemiring.topological_semiring

lemma subalgebra.le_topological_closure (s : subalgebra R A) :
  s ≤ s.topological_closure :=
subset_closure

lemma subalgebra.is_closed_topological_closure (s : subalgebra R A) :
  is_closed (s.topological_closure : set A) :=
by convert is_closed_closure

lemma subalgebra.topological_closure_minimal
  (s : subalgebra R A) {t : subalgebra R A} (h : s ≤ t) (ht : is_closed (t : set A)) :
  s.topological_closure ≤ t :=
closure_minimal h ht

/-- If a subalgebra of a topological algebra is commutative, then so is its topological closure. -/
def subalgebra.comm_semiring_topological_closure [t2_space A] (s : subalgebra R A)
  (hs : ∀ (x y : s), x * y = y * x) : comm_semiring s.topological_closure :=
{ ..s.topological_closure.to_semiring,
  ..s.to_submonoid.comm_monoid_topological_closure hs }

/--
This is really a statement about topological algebra isomorphisms,
but we don't have those, so we use the clunky approach of talking about
an algebra homomorphism, and a separate homeomorphism,
along with a witness that as functions they are the same.
-/
lemma subalgebra.topological_closure_comap_homeomorph
  (s : subalgebra R A)
  {B : Type*} [topological_space B] [ring B] [topological_ring B] [algebra R B]
  (f : B →ₐ[R] A) (f' : B ≃ₜ A) (w : (f : B → A) = f') :
  s.topological_closure.comap f = (s.comap f).topological_closure :=
begin
  apply set_like.ext',
  simp only [subalgebra.topological_closure_coe],
  simp only [subalgebra.coe_comap, subsemiring.coe_comap, alg_hom.coe_to_ring_hom],
  rw [w],
  exact f'.preimage_closure _,
end

end topological_algebra

section ring
variables {R : Type*} [comm_ring R]
variables {A : Type u} [topological_space A]
variables [ring A]
variables [algebra R A] [topological_ring A]

/-- If a subalgebra of a topological algebra is commutative, then so is its topological closure.
See note [reducible non-instances]. -/
@[reducible] def subalgebra.comm_ring_topological_closure [t2_space A] (s : subalgebra R A)
  (hs : ∀ (x y : s), x * y = y * x) : comm_ring s.topological_closure :=
{ ..s.topological_closure.to_ring,
  ..s.to_submonoid.comm_monoid_topological_closure hs }

variables (R)
/-- The topological closure of the subalgebra generated by a single element. -/
def algebra.elemental_algebra (x : A) : subalgebra R A :=
(algebra.adjoin R ({x} : set A)).topological_closure

lemma algebra.self_mem_elemental_algebra (x : A) : x ∈ algebra.elemental_algebra R x :=
set_like.le_def.mp (subalgebra.le_topological_closure (algebra.adjoin R ({x} : set A))) $
  algebra.self_mem_adjoin_singleton R x

variables {R}

instance [t2_space A] {x : A} : comm_ring (algebra.elemental_algebra R x) :=
subalgebra.comm_ring_topological_closure _
begin
  letI : comm_ring (algebra.adjoin R ({x} : set A)) := algebra.adjoin_comm_ring_of_comm R
    (λ y hy z hz, by {rw [mem_singleton_iff] at hy hz, rw [hy, hz]}),
  exact λ _ _, mul_comm _ _,
end

end ring

section division_ring

/-- The action induced by `algebra_rat` is continuous. -/
instance division_ring.has_continuous_const_smul_rat
  {A} [division_ring A] [topological_space A] [has_continuous_mul A] [char_zero A] :
  has_continuous_const_smul ℚ A :=
⟨λ r, by { simpa only [algebra.smul_def] using continuous_const.mul continuous_id }⟩

end division_ring
