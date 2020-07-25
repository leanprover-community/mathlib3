/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import ring_theory.adjoin

/-!
# Towers of algebras

We set up the basic theory of algebra towers.
The typeclass `is_algebra_tower R S A` expresses that `A` is an `S`-algebra,
and both `S` and `A` are `R`-algebras, with the compatibility condition
`(r • s) • a = r • (s • a)`.

In `field_theory/tower.lean` we use this to prove the tower law for finite extensions,
that if `R` and `S` are both fields, then `[A:R] = [A:S] [S:A]`.

In this file we prepare the main lemma:
if `{bi | i ∈ I}` is an `R`-basis of `S` and `{cj | j ∈ J}` is a `S`-basis
of `A`, then `{bi cj | i ∈ I, j ∈ J}` is an `R`-basis of `A`. This statement does not require the
base rings to be a field, so we also generalize the lemma to rings in this file.
-/

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

theorem aeval_apply (x : B) (p : polynomial R) : polynomial.aeval x p =
  polynomial.aeval x (polynomial.map (algebra_map R A) p) :=
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

section semiring

variables {R S A}
variables [comm_semiring R] [comm_semiring S] [semiring A]
variables [algebra R S] [algebra S A] [algebra R A] [is_algebra_tower R S A]

namespace submodule

open is_algebra_tower

theorem smul_mem_span_smul_of_mem {s : set S} {t : set A} {k : S} (hks : k ∈ span R s)
  {x : A} (hx : x ∈ t) : k • x ∈ span R (s • t) :=
span_induction hks (λ c hc, subset_span $ set.mem_smul.2 ⟨c, x, hc, hx, rfl⟩)
  (by { rw zero_smul, exact zero_mem _ })
  (λ c₁ c₂ ih₁ ih₂, by { rw add_smul, exact add_mem _ ih₁ ih₂ })
  (λ b c hc, by { rw is_algebra_tower.smul_assoc, exact smul_mem _ _ hc })

theorem smul_mem_span_smul {s : set S} (hs : span R s = ⊤) {t : set A} {k : S}
  {x : A} (hx : x ∈ span R t) :
  k • x ∈ span R (s • t) :=
span_induction hx (λ x hx, smul_mem_span_smul_of_mem (hs.symm ▸ mem_top) hx)
  (by { rw smul_zero, exact zero_mem _ })
  (λ x y ihx ihy, by { rw smul_add, exact add_mem _ ihx ihy })
  (λ c x hx, smul_left_comm c k x ▸ smul_mem _ _ hx)

theorem smul_mem_span_smul' {s : set S} (hs : span R s = ⊤) {t : set A} {k : S}
  {x : A} (hx : x ∈ span R (s • t)) :
  k • x ∈ span R (s • t) :=
span_induction hx (λ x hx, let ⟨p, q, hp, hq, hpq⟩ := set.mem_smul.1 hx in
    by { rw [← hpq, smul_smul], exact smul_mem_span_smul_of_mem (hs.symm ▸ mem_top) hq })
  (by { rw smul_zero, exact zero_mem _ })
  (λ x y ihx ihy, by { rw smul_add, exact add_mem _ ihx ihy })
  (λ c x hx, smul_left_comm c k x ▸ smul_mem _ _ hx)

theorem span_smul {s : set S} (hs : span R s = ⊤) (t : set A) :
  span R (s • t) = (span S t).restrict_scalars' R :=
le_antisymm (span_le.2 $ λ x hx, let ⟨p, q, hps, hqt, hpqx⟩ := set.mem_smul.1 hx in
  hpqx ▸ (span S t).smul_mem p (subset_span hqt)) $
λ p hp, span_induction hp (λ x hx, one_smul S x ▸ smul_mem_span_smul hs (subset_span hx))
  (zero_mem _)
  (λ _ _, add_mem _)
  (λ k x hx, smul_mem_span_smul' hs hx)

end submodule

end semiring


section ring

open_locale big_operators classical
universes v₁ w₁

variables {R S A}
variables [comm_ring R] [comm_ring S] [ring A]
variables [algebra R S] [algebra S A] [algebra R A] [is_algebra_tower R S A]

theorem linear_independent_smul {ι : Type v₁} {b : ι → S} {κ : Type w₁} {c : κ → A}
  (hb : linear_independent R b) (hc : linear_independent S c) :
  linear_independent R (λ p : ι × κ, b p.1 • c p.2) :=
begin
  rw linear_independent_iff' at hb hc, rw linear_independent_iff'', rintros s g hg hsg ⟨i, k⟩,
  by_cases hik : (i, k) ∈ s,
  { have h1 : ∑ i in (s.image prod.fst).product (s.image prod.snd), g i • b i.1 • c i.2 = 0,
    { rw ← hsg, exact (finset.sum_subset finset.subset_product $ λ p _ hp,
        show g p • b p.1 • c p.2 = 0, by rw [hg p hp, zero_smul]).symm },
    rw [finset.sum_product, finset.sum_comm] at h1,
    simp_rw [← is_algebra_tower.smul_assoc, ← finset.sum_smul] at h1,
    exact hb _ _ (hc _ _ h1 k (finset.mem_image_of_mem _ hik)) i (finset.mem_image_of_mem _ hik) },
  exact hg _ hik
end

theorem is_basis.smul {ι : Type v₁} {b : ι → S} {κ : Type w₁} {c : κ → A}
  (hb : is_basis R b) (hc : is_basis S c) : is_basis R (λ p : ι × κ, b p.1 • c p.2) :=
⟨linear_independent_smul hb.1 hc.1,
by rw [← set.range_smul_range, submodule.span_smul hb.2, ← submodule.restrict_scalars'_top R S A,
    submodule.restrict_scalars'_inj, hc.2]⟩

end ring
