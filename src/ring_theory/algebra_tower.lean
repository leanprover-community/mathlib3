/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.algebra.tower
import algebra.invertible
import algebra.module.big_operators
import linear_algebra.basis

/-!
# Towers of algebras

We set up the basic theory of algebra towers.
An algebra tower A/S/R is expressed by having instances of `algebra A S`,
`algebra R S`, `algebra R A` and `is_scalar_tower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

In `field_theory/tower.lean` we use this to prove the tower law for finite extensions,
that if `R` and `S` are both fields, then `[A:R] = [A:S] [S:A]`.

In this file we prepare the main lemma:
if `{bi | i ∈ I}` is an `R`-basis of `S` and `{cj | j ∈ J}` is a `S`-basis
of `A`, then `{bi cj | i ∈ I, j ∈ J}` is an `R`-basis of `A`. This statement does not require the
base rings to be a field, so we also generalize the lemma to rings in this file.
-/

open_locale pointwise
universes u v w u₁

variables (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

namespace is_scalar_tower

section semiring
variables [comm_semiring R] [comm_semiring S] [semiring A] [semiring B]
variables [algebra R S] [algebra S A] [algebra S B] [algebra R A] [algebra R B]
variables [is_scalar_tower R S A] [is_scalar_tower R S B]

variables (R S A B)

/-- Suppose that `R -> S -> A` is a tower of algebras.
If an element `r : R` is invertible in `S`, then it is invertible in `A`. -/
def invertible.algebra_tower (r : R) [invertible (algebra_map R S r)] :
  invertible (algebra_map R A r) :=
invertible.copy (invertible.map (algebra_map S A) (algebra_map R S r)) (algebra_map R A r)
  (is_scalar_tower.algebra_map_apply R S A r)

/-- A natural number that is invertible when coerced to `R` is also invertible
when coerced to any `R`-algebra. -/
def invertible_algebra_coe_nat (n : ℕ) [inv : invertible (n : R)] :
  invertible (n : A) :=
by { haveI : invertible (algebra_map ℕ R n) := inv, exact invertible.algebra_tower ℕ R A n }

end semiring

section comm_semiring
variables [comm_semiring R] [comm_semiring A] [comm_semiring B]
variables [algebra R A] [algebra A B] [algebra R B] [is_scalar_tower R A B]

end comm_semiring

end is_scalar_tower

section algebra_map_coeffs

variables {R} (A) {ι M : Type*} [comm_semiring R] [semiring A] [add_comm_monoid M]
variables [algebra R A] [module A M] [module R M] [is_scalar_tower R A M]
variables (b : basis ι R M) (h : function.bijective (algebra_map R A))

/-- If `R` and `A` have a bijective `algebra_map R A` and act identically on `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module. -/
@[simps]
noncomputable def basis.algebra_map_coeffs : basis ι A M :=
b.map_coeffs (ring_equiv.of_bijective _ h) (λ c x, by simp)

lemma basis.algebra_map_coeffs_apply (i : ι) : b.algebra_map_coeffs A h i = b i :=
b.map_coeffs_apply _ _ _

@[simp] lemma basis.coe_algebra_map_coeffs : (b.algebra_map_coeffs A h : ι → M) = b :=
b.coe_map_coeffs _ _

end algebra_map_coeffs

section semiring

open finsupp
open_locale big_operators classical
universes v₁ w₁

variables {R S A}
variables [comm_semiring R] [semiring S] [add_comm_monoid A]
variables [algebra R S] [module S A] [module R A] [is_scalar_tower R S A]

theorem linear_independent_smul {ι : Type v₁} {b : ι → S} {ι' : Type w₁} {c : ι' → A}
  (hb : linear_independent R b) (hc : linear_independent S c) :
  linear_independent R (λ p : ι × ι', b p.1 • c p.2) :=
begin
  rw linear_independent_iff' at hb hc, rw linear_independent_iff'', rintros s g hg hsg ⟨i, k⟩,
  by_cases hik : (i, k) ∈ s,
  { have h1 : ∑ i in s.image prod.fst ×ˢ s.image prod.snd, g i • b i.1 • c i.2 = 0,
    { rw ← hsg, exact (finset.sum_subset finset.subset_product $ λ p _ hp,
        show g p • b p.1 • c p.2 = 0, by rw [hg p hp, zero_smul]).symm },
    rw finset.sum_product_right at h1,
    simp_rw [← smul_assoc, ← finset.sum_smul] at h1,
    exact hb _ _ (hc _ _ h1 k (finset.mem_image_of_mem _ hik)) i (finset.mem_image_of_mem _ hik) },
  exact hg _ hik
end

/-- `basis.smul (b : basis ι R S) (c : basis ι S A)` is the `R`-basis on `A`
where the `(i, j)`th basis vector is `b i • c j`. -/
noncomputable def basis.smul {ι : Type v₁} {ι' : Type w₁}
  (b : basis ι R S) (c : basis ι' S A) : basis (ι × ι') R A :=
basis.of_repr ((c.repr.restrict_scalars R) ≪≫ₗ
  ((finsupp.lcongr (equiv.refl _) b.repr) ≪≫ₗ
  ((finsupp_prod_lequiv R).symm ≪≫ₗ
  ((finsupp.lcongr (equiv.prod_comm ι' ι) (linear_equiv.refl _ _))))))

@[simp] theorem basis.smul_repr {ι : Type v₁} {ι' : Type w₁}
  (b : basis ι R S) (c : basis ι' S A) (x ij):
  (b.smul c).repr x ij = b.repr (c.repr x ij.2) ij.1 :=
by simp [basis.smul]

theorem basis.smul_repr_mk {ι : Type v₁} {ι' : Type w₁}
  (b : basis ι R S) (c : basis ι' S A) (x i j):
  (b.smul c).repr x (i, j) = b.repr (c.repr x j) i :=
b.smul_repr c x (i, j)

@[simp] theorem basis.smul_apply {ι : Type v₁} {ι' : Type w₁}
  (b : basis ι R S) (c : basis ι' S A) (ij) :
  (b.smul c) ij = b ij.1 • c ij.2 :=
begin
  obtain ⟨i, j⟩ := ij,
  rw basis.apply_eq_iff,
  ext ⟨i', j'⟩,
  rw [basis.smul_repr, linear_equiv.map_smul, basis.repr_self, finsupp.smul_apply,
      finsupp.single_apply],
  dsimp only,
  split_ifs with hi,
  { simp [hi, finsupp.single_apply] },
  { simp [hi] },
end

end semiring

section ring

variables {R S}
variables [comm_ring R] [ring S] [algebra R S]

lemma basis.algebra_map_injective {ι : Type*} [no_zero_divisors R] [nontrivial S]
  (b : basis ι R S) :
  function.injective (algebra_map R S) :=
have no_zero_smul_divisors R S := b.no_zero_smul_divisors,
by exactI no_zero_smul_divisors.algebra_map_injective R S

end ring

section alg_hom_tower

variables {A} {C D : Type*} [comm_semiring A] [comm_semiring C] [comm_semiring D]
  [algebra A C] [algebra A D]

variables (f : C →ₐ[A] D) (B) [comm_semiring B] [algebra A B] [algebra B C] [is_scalar_tower A B C]

/-- Restrict the domain of an `alg_hom`. -/
def alg_hom.restrict_domain : B →ₐ[A] D := f.comp (is_scalar_tower.to_alg_hom A B C)

/-- Extend the scalars of an `alg_hom`. -/
def alg_hom.extend_scalars : @alg_hom B C D _ _ _ _ (f.restrict_domain B).to_ring_hom.to_algebra :=
{ commutes' := λ _, rfl .. f }

variables {B}

/-- `alg_hom`s from the top of a tower are equivalent to a pair of `alg_hom`s. -/
def alg_hom_equiv_sigma :
  (C →ₐ[A] D) ≃ Σ (f : B →ₐ[A] D), @alg_hom B C D _ _ _ _ f.to_ring_hom.to_algebra :=
{ to_fun := λ f, ⟨f.restrict_domain B, f.extend_scalars B⟩,
  inv_fun := λ fg,
    let alg := fg.1.to_ring_hom.to_algebra in by exactI fg.2.restrict_scalars A,
  left_inv := λ f, by { dsimp only, ext, refl },
  right_inv :=
  begin
    rintros ⟨⟨f, _, _, _, _, _⟩, g, _, _, _, _, hg⟩,
    obtain rfl : f = λ x, g (algebra_map B C x) := by { ext, exact (hg x).symm },
    refl,
  end }

end alg_hom_tower
