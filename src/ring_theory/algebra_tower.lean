/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import ring_theory.adjoin

universes u v w u₁

variables (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

section comm_semiring
variables [comm_semiring R] [comm_semiring S] [semiring A] [semiring B]
variables [algebra R S] [algebra S A] [algebra R A] [algebra S B] [algebra R B]

/-- Typeclass for a tower of three algebras. -/
class is_algebra_tower : Prop :=
(smul_assoc : ∀ (x : R) (y : S) (z : A), (x • y) • z = x • (y • z))

namespace is_algebra_tower

theorem algebra_map_eq [is_algebra_tower R S A] :
  algebra_map R A = (algebra_map S A).comp (algebra_map R S) :=
ring_hom.ext $ λ x, by simp_rw [ring_hom.comp_apply, algebra.algebra_map_eq_smul_one,
    smul_assoc, one_smul]

theorem algebra_map_apply [is_algebra_tower R S A] (x : R) :
  algebra_map R A x = algebra_map S A (algebra_map R S x) :=
by rw [algebra_map_eq R S A, ring_hom.comp_apply]

theorem of_algebra_map_eq (h : ∀ x, algebra_map R A x = algebra_map S A (algebra_map R S x)) :
  is_algebra_tower R S A :=
⟨λ x y z, by simp_rw [algebra.smul_def, ring_hom.map_mul, mul_assoc, h]⟩

@[ext] lemma algebra.ext {S : Type u} {A : Type v} [comm_semiring S] [semiring A]
  (h1 h2 : algebra S A) (h : ∀ {r : S} {x : A}, (by clear h2; exact r • x) = r • x) : h1 = h2 :=
begin
  unfreezingI { cases h1 with f1 g1 h11 h12, cases h2 with f2 g2 h21 h22,
  cases f1, cases f2, congr', { ext r x, exact h },
  ext r, erw [← mul_one (g1 r), ← h12, ← mul_one (g2 r), ← h22, h], refl }
end

variables [is_algebra_tower R S A]

theorem comap_eq : algebra.comap.algebra R S A = ‹_› :=
algebra.ext _ _ $ λ x (z : A),
calc  algebra_map R S x • z
    = (x • 1 : S) • z : by rw algebra.algebra_map_eq_smul_one
... = x • (1 : S) • z : by rw smul_assoc
... = (by exact x • z : A) : by rw one_smul

/-- In a tower, the canonical map from the middle element to the top element is an
algebra homomorphism over the bottom element. -/
def to_alg_hom : S →ₐ[R] A :=
{ commutes' := λ _, (algebra_map_apply _ _ _ _).symm,
  .. algebra_map S A }

end is_algebra_tower

end comm_semiring

section comm_ring

variables [comm_ring R] [comm_ring S] [comm_ring A] [algebra R S] [algebra S A] [algebra R A]
variables [is_algebra_tower R S A]

namespace is_algebra_tower

/-- If A/S/R is a tower of algebras then any S-subalgebra of A gives an R-subalgebra of A. -/
def subalgebra_comap (U : subalgebra S A) : subalgebra R A :=
{ carrier := U,
  range_le' := λ z ⟨x, hx⟩, U.range_le ⟨algebra_map R S x, by rwa ← algebra_map_apply⟩ }

theorem subalgebra_comap_top : subalgebra_comap R S A ⊤ = ⊤ :=
algebra.eq_top_iff.2 $ λ _, algebra.mem_top

theorem range_under_adjoin (t : set A) :
  (to_alg_hom R S A).range.under (algebra.adjoin _ t) =
    subalgebra_comap R S A (algebra.adjoin S t) :=
subalgebra.ext $ λ z, show z ∈ ring.closure _ ↔ z ∈ ring.closure _,
by { congr' 4, ext z, exact ⟨λ ⟨⟨x, y, h1⟩, h2⟩, ⟨y, h2 ▸ h1⟩, λ ⟨y, hy⟩, ⟨⟨z, y, hy⟩, rfl⟩⟩ }

instance : is_algebra_tower ℤ S A :=
of_algebra_map_eq _ _ _ $ λ x, ((algebra_map S A).map_int_cast x).symm

end is_algebra_tower

namespace algebra

theorem adjoin_algebra_map' {R : Type u} {S : Type v} {A : Type w}
  [comm_ring R] [comm_ring S] [comm_ring A] [algebra R S] [algebra S A] (s : set S) :
  adjoin R (algebra_map S (comap R S A) '' s) = subalgebra.map (adjoin R s) (to_comap R S A) :=
le_antisymm (adjoin_le $ set.image_subset_iff.2 $ λ y hy, ⟨y, subset_adjoin hy, rfl⟩)
  (subalgebra.map_le.2 $ adjoin_le $ λ y hy, subset_adjoin ⟨y, hy, rfl⟩)

theorem adjoin_algebra_map (R : Type u) (S : Type v) (A : Type w)
  [comm_ring R] [comm_ring S] [comm_ring A] [algebra R S] [algebra S A] [algebra R A]
  [is_algebra_tower R S A] (s : set S) :
  adjoin R (algebra_map S A '' s) = subalgebra.map (adjoin R s) (is_algebra_tower.to_alg_hom R S A) :=
le_antisymm (adjoin_le $ set.image_subset_iff.2 $ λ y hy, ⟨y, subset_adjoin hy, rfl⟩)
  (subalgebra.map_le.2 $ adjoin_le $ λ y hy, subset_adjoin ⟨y, hy, rfl⟩)

end algebra

end comm_ring
