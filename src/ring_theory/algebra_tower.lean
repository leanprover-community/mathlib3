/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import ring_theory.adjoin

universes u v w u₁

variables (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

/-- Typeclass for a tower of three algebras. -/
class is_algebra_tower [comm_semiring R] [comm_semiring S] [semiring A]
  [algebra R S] [algebra S A] [algebra R A] : Prop :=
(smul_assoc : ∀ (x : R) (y : S) (z : A), (x • y) • z = x • (y • z))

namespace is_algebra_tower

section semiring
variables [comm_semiring R] [comm_semiring S] [semiring A] [semiring B]
variables [algebra R S] [algebra S A] [algebra R A] [algebra S B] [algebra R B]

variables {R S A}
theorem of_algebra_map_eq (h : ∀ x, algebra_map R A x = algebra_map S A (algebra_map R S x)) :
  is_algebra_tower R S A :=
⟨λ x y z, by simp_rw [algebra.smul_def, ring_hom.map_mul, mul_assoc, h]⟩

variables [is_algebra_tower R S A] [is_algebra_tower R S B]

variables (R S A)
theorem algebra_map_eq :
  algebra_map R A = (algebra_map S A).comp (algebra_map R S) :=
ring_hom.ext $ λ x, by simp_rw [ring_hom.comp_apply, algebra.algebra_map_eq_smul_one,
    smul_assoc, one_smul]

theorem algebra_map_apply (x : R) : algebra_map R A x = algebra_map S A (algebra_map R S x) :=
by rw [algebra_map_eq R S A, ring_hom.comp_apply]

variables {R} (S) {A}
theorem algebra_map_smul (r : R) (x : A) : algebra_map R S r • x = r • x :=
by rw [algebra.algebra_map_eq_smul_one, smul_assoc, one_smul]

variables {R S A}
theorem smul_left_comm (r : R) (s : S) (x : A) : r • s • x = s • r • x :=
by simp_rw [algebra.smul_def, ← mul_assoc, algebra_map_apply R S A,
    ← (algebra_map S A).map_mul, mul_comm s]

@[ext] lemma algebra.ext {S : Type u} {A : Type v} [comm_semiring S] [semiring A]
  (h1 h2 : algebra S A) (h : ∀ {r : S} {x : A}, (by clear h2; exact r • x) = r • x) : h1 = h2 :=
begin
  unfreezingI { cases h1 with f1 g1 h11 h12, cases h2 with f2 g2 h21 h22,
  cases f1, cases f2, congr', { ext r x, exact h },
  ext r, erw [← mul_one (g1 r), ← h12, ← mul_one (g2 r), ← h22, h], refl }
end

variables (R S A)
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

@[simp] lemma to_alg_hom_apply (y : S) : to_alg_hom R S A y = algebra_map S A y := rfl

variables (R) {S A B}
/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrict_base (f : A →ₐ[S] B) : A →ₐ[R] B :=
{ commutes' := λ r, by { rw [algebra_map_apply R S A, algebra_map_apply R S B],
    exact f.commutes (algebra_map R S r) },
  .. (f : A →+* B) }

@[simp] lemma restrict_base_apply (f : A →ₐ[S] B) (x : A) : restrict_base R f x = f x := rfl

instance left : is_algebra_tower S S A :=
of_algebra_map_eq $ λ x, rfl

instance right : is_algebra_tower R S S :=
of_algebra_map_eq $ λ x, rfl

instance nat : is_algebra_tower ℕ S A :=
of_algebra_map_eq $ λ x, ((algebra_map S A).map_nat_cast x).symm

instance comap {R S A : Type*} [comm_semiring R] [comm_semiring S] [semiring A]
  [algebra R S] [algebra S A] : is_algebra_tower R S (algebra.comap R S A) :=
of_algebra_map_eq $ λ x, rfl

instance subsemiring (U : subsemiring S) : is_algebra_tower U S A :=
of_algebra_map_eq $ λ x, rfl

instance subring {S A : Type*} [comm_ring S] [ring A] [algebra S A]
  (U : set S) [is_subring U] : is_algebra_tower U S A :=
of_algebra_map_eq $ λ x, rfl

end semiring

section comm_semiring
variables [comm_semiring R] [comm_semiring A] [algebra R A]
variables [comm_semiring B] [algebra A B] [algebra R B] [is_algebra_tower R A B]

instance subalgebra (S : subalgebra R A) : is_algebra_tower R S A :=
of_algebra_map_eq $ λ x, rfl

instance polynomial : is_algebra_tower R A (polynomial B) :=
of_algebra_map_eq $ λ x, congr_arg polynomial.C $ algebra_map_apply R A B x

theorem aeval_apply (x : B) (p) : polynomial.aeval R B x p =
  polynomial.aeval A B x (polynomial.map (algebra_map R A) p) :=
by rw [polynomial.aeval_def, polynomial.aeval_def, polynomial.eval₂_map, algebra_map_eq R A B]

end comm_semiring

section ring
variables [comm_ring R] [comm_ring S] [ring A] [algebra R S] [algebra S A] [algebra R A]
variables [is_algebra_tower R S A]

/-- If A/S/R is a tower of algebras then any S-subalgebra of A gives an R-subalgebra of A. -/
def subalgebra_comap (U : subalgebra S A) : subalgebra R A :=
{ carrier := U,
  algebra_map_mem' := λ x, by { rw algebra_map_apply R S A, exact U.algebra_map_mem _ } }

theorem subalgebra_comap_top : subalgebra_comap R S A ⊤ = ⊤ :=
algebra.eq_top_iff.2 $ λ _, show _ ∈ (⊤ : subalgebra S A), from algebra.mem_top

end ring

section comm_ring
variables [comm_ring R] [comm_ring S] [comm_ring A] [algebra R S] [algebra S A] [algebra R A]
variables [is_algebra_tower R S A]

theorem range_under_adjoin (t : set A) :
  (to_alg_hom R S A).range.under (algebra.adjoin _ t) =
    subalgebra_comap R S A (algebra.adjoin S t) :=
subalgebra.ext $ λ z,
show z ∈ subsemiring.closure (set.range (algebra_map (to_alg_hom R S A).range A) ∪ t : set A) ↔
  z ∈ subsemiring.closure (set.range (algebra_map S A) ∪ t : set A),
from suffices set.range (algebra_map (to_alg_hom R S A).range A) = set.range (algebra_map S A),
  by rw this,
by { ext z, exact ⟨λ ⟨⟨x, y, h1⟩, h2⟩, ⟨y, h2 ▸ h1⟩, λ ⟨y, hy⟩, ⟨⟨z, y, hy⟩, rfl⟩⟩ }

instance int : is_algebra_tower ℤ S A :=
of_algebra_map_eq $ λ x, ((algebra_map S A).map_int_cast x).symm

end comm_ring

section division_ring
variables [field R] [division_ring S] [algebra R S] [char_zero R] [char_zero S]

instance rat : is_algebra_tower ℚ R S :=
of_algebra_map_eq $ λ x, ((algebra_map R S).map_rat_cast x).symm

end division_ring

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

namespace submodule

open is_algebra_tower

variables [comm_semiring R] [comm_semiring S] [semiring A]
variables [algebra R S] [algebra S A] [algebra R A] [is_algebra_tower R S A]

variables (R) {S A}
/-- Restricting the scalars of submodules in an algebra tower. -/
def restrict_scalars' (U : submodule S A) : submodule R A :=
{ smul_mem' := λ r x hx, algebra_map_smul S r x ▸ U.smul_mem _ hx, .. U }

variables (R S A)
theorem restrict_scalars'_top : restrict_scalars' R (⊤ : submodule S A) = ⊤ := rfl

variables {R S A}
theorem restrict_scalars'_injective (U₁ U₂ : submodule S A)
  (h : restrict_scalars' R U₁ = restrict_scalars' R U₂) : U₁ = U₂ :=
ext $ by convert set.ext_iff.1 (ext'_iff.1 h); refl

theorem restrict_scalars'_inj {U₁ U₂ : submodule S A} :
  restrict_scalars' R U₁ = restrict_scalars' R U₂ ↔ U₁ = U₂ :=
⟨restrict_scalars'_injective U₁ U₂, congr_arg _⟩

end submodule
