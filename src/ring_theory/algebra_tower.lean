/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import ring_theory.adjoin

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

universes u v w u₁

variables (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

namespace is_scalar_tower

section semimodule

variables [comm_semiring R] [semiring S] [add_comm_monoid A] [add_comm_monoid B]
variables [algebra R S] [semimodule S A] [semimodule R A] [semimodule S B] [semimodule R B]
variables [is_scalar_tower R S A] [is_scalar_tower R S B]

variables {R} (S) {A}
theorem algebra_map_smul (r : R) (x : A) : algebra_map R S r • x = r • x :=
by rw [algebra.algebra_map_eq_smul_one, smul_assoc, one_smul]

variables {R S A}
theorem smul_left_comm (r : R) (s : S) (x : A) : r • s • x = s • r • x :=
by rw [← smul_assoc, algebra.smul_def r s, algebra.commutes, mul_smul, algebra_map_smul]

end semimodule

section semiring
variables [comm_semiring R] [comm_semiring S] [semiring A] [semiring B]
variables [algebra R S] [algebra S A] [algebra S B]

variables {R S A}
theorem of_algebra_map_eq [algebra R A]
  (h : ∀ x, algebra_map R A x = algebra_map S A (algebra_map R S x)) :
  is_scalar_tower R S A :=
⟨λ x y z, by simp_rw [algebra.smul_def, ring_hom.map_mul, mul_assoc, h]⟩

variables (R S A)

instance subalgebra (S₀ : subalgebra R S) : is_scalar_tower S₀ S A :=
of_algebra_map_eq $ λ x, rfl

variables [algebra R A] [algebra R B]
variables [is_scalar_tower R S A] [is_scalar_tower R S B]

theorem algebra_map_eq :
  algebra_map R A = (algebra_map S A).comp (algebra_map R S) :=
ring_hom.ext $ λ x, by simp_rw [ring_hom.comp_apply, algebra.algebra_map_eq_smul_one,
    smul_assoc, one_smul]

theorem algebra_map_apply (x : R) : algebra_map R A x = algebra_map S A (algebra_map R S x) :=
by rw [algebra_map_eq R S A, ring_hom.comp_apply]

instance subalgebra' (S₀ : subalgebra R S) : is_scalar_tower R S₀ A :=
@is_scalar_tower.of_algebra_map_eq R S₀ A _ _ _ _ _ _ $ λ _,
(is_scalar_tower.algebra_map_apply R S A _ : _)

@[ext] lemma algebra.ext {S : Type u} {A : Type v} [comm_semiring S] [semiring A]
  (h1 h2 : algebra S A) (h : ∀ {r : S} {x : A}, (by haveI := h1; exact r • x) = r • x) : h1 = h2 :=
begin
  unfreezingI { cases h1 with f1 g1 h11 h12, cases h2 with f2 g2 h21 h22,
  cases f1, cases f2, congr', { ext r x, exact h },
  ext r, erw [← mul_one (g1 r), ← h12, ← mul_one (g2 r), ← h22, h], refl }
end

variables (R S A)
theorem algebra_comap_eq : algebra.comap.algebra R S A = ‹_› :=
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

instance right : is_scalar_tower R S S :=
of_algebra_map_eq $ λ x, rfl

instance nat : is_scalar_tower ℕ S A :=
of_algebra_map_eq $ λ x, ((algebra_map S A).map_nat_cast x).symm

instance comap {R S A : Type*} [comm_semiring R] [comm_semiring S] [semiring A]
  [algebra R S] [algebra S A] : is_scalar_tower R S (algebra.comap R S A) :=
of_algebra_map_eq $ λ x, rfl

-- conflicts with is_scalar_tower.subalgebra
@[priority 999] instance subsemiring (U : subsemiring S) : is_scalar_tower U S A :=
of_algebra_map_eq $ λ x, rfl

-- conflicts with is_scalar_tower.subalgebra
@[priority 999] instance subring {S A : Type*} [comm_ring S] [ring A] [algebra S A]
  (U : set S) [is_subring U] : is_scalar_tower U S A :=
of_algebra_map_eq $ λ x, rfl

@[nolint instance_priority]
instance of_ring_hom {R A B : Type*} [comm_semiring R] [comm_semiring A] [comm_semiring B]
  [algebra R A] [algebra R B] (f : A →ₐ[R] B) :
  @is_scalar_tower R A B _ (f.to_ring_hom.to_algebra.to_has_scalar) _ :=
by { letI := (f : A →+* B).to_algebra, exact of_algebra_map_eq (λ x, (f.commutes x).symm) }

instance polynomial : is_scalar_tower R S (polynomial A) :=
of_algebra_map_eq $ λ x, congr_arg polynomial.C $ algebra_map_apply R S A x

variables (R S A)
theorem aeval_apply (x : A) (p : polynomial R) : polynomial.aeval x p =
  polynomial.aeval x (polynomial.map (algebra_map R S) p) :=
by rw [polynomial.aeval_def, polynomial.aeval_def, polynomial.eval₂_map, algebra_map_eq R S A]

end semiring

section comm_semiring
variables [comm_semiring R] [comm_semiring A] [comm_semiring B]
variables [algebra R A] [algebra A B] [algebra R B] [is_scalar_tower R A B]

lemma algebra_map_aeval (x : A) (p : polynomial R) :
  algebra_map A B (polynomial.aeval x p) = polynomial.aeval (algebra_map A B x) p :=
by rw [polynomial.aeval_def, polynomial.aeval_def, polynomial.hom_eval₂,
  ←is_scalar_tower.algebra_map_eq]

lemma aeval_eq_zero_of_aeval_algebra_map_eq_zero {x : A} {p : polynomial R}
  (h : function.injective (algebra_map A B)) (hp : polynomial.aeval (algebra_map A B x) p = 0) :
  polynomial.aeval x p = 0 :=
begin
  rw [← algebra_map_aeval, ← (algebra_map A B).map_zero] at hp,
  exact h hp,
end

lemma aeval_eq_zero_of_aeval_algebra_map_eq_zero_field {R A B : Type*} [comm_semiring R] [field A]
  [comm_semiring B] [nontrivial B] [algebra R A] [algebra R B] [algebra A B] [is_scalar_tower R A B]
  {x : A} {p : polynomial R} (h : polynomial.aeval (algebra_map A B x) p = 0) :
  polynomial.aeval x p = 0 :=
aeval_eq_zero_of_aeval_algebra_map_eq_zero R A B (algebra_map A B).injective h

instance linear_map (R : Type u) (A : Type v) (V : Type w)
  [comm_semiring R] [comm_semiring A] [add_comm_monoid V]
  [semimodule R V] [algebra R A] : is_scalar_tower R A (V →ₗ[R] A) :=
⟨λ x y f, linear_map.ext $ λ v, algebra.smul_mul_assoc x y (f v)⟩

end comm_semiring

section comm_ring
variables [comm_ring R] [comm_ring S] [comm_ring A] [algebra R S] [algebra S A] [algebra R A]
variables [is_scalar_tower R S A]

instance int : is_scalar_tower ℤ S A :=
of_algebra_map_eq $ λ x, ((algebra_map S A).map_int_cast x).symm

end comm_ring

section division_ring
variables [field R] [division_ring S] [algebra R S] [char_zero R] [char_zero S]

instance rat : is_scalar_tower ℚ R S :=
of_algebra_map_eq $ λ x, ((algebra_map R S).map_rat_cast x).symm

end division_ring

end is_scalar_tower

namespace algebra

theorem adjoin_algebra_map' {R : Type u} {S : Type v} {A : Type w}
  [comm_ring R] [comm_ring S] [comm_ring A] [algebra R S] [algebra S A] (s : set S) :
  adjoin R (algebra_map S (comap R S A) '' s) = subalgebra.map (adjoin R s) (to_comap R S A) :=
le_antisymm (adjoin_le $ set.image_subset_iff.2 $ λ y hy, ⟨y, subset_adjoin hy, rfl⟩)
  (subalgebra.map_le.2 $ adjoin_le $ λ y hy, subset_adjoin ⟨y, hy, rfl⟩)

theorem adjoin_algebra_map (R : Type u) (S : Type v) (A : Type w)
  [comm_ring R] [comm_ring S] [comm_ring A] [algebra R S] [algebra S A] [algebra R A]
  [is_scalar_tower R S A] (s : set S) :
  adjoin R (algebra_map S A '' s) = subalgebra.map (adjoin R s) (is_scalar_tower.to_alg_hom R S A) :=
le_antisymm (adjoin_le $ set.image_subset_iff.2 $ λ y hy, ⟨y, subset_adjoin hy, rfl⟩)
  (subalgebra.map_le.2 $ adjoin_le $ λ y hy, subset_adjoin ⟨y, hy, rfl⟩)

end algebra

namespace subalgebra

open is_scalar_tower

variables (R) {S A} [comm_semiring R] [comm_semiring S] [semiring A]
variables [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A]

/-- If A/S/R is a tower of algebras then the `res`triction of a S-subalgebra of A is an R-subalgebra of A. -/
def res (U : subalgebra S A) : subalgebra R A :=
{ algebra_map_mem' := λ x, by { rw algebra_map_apply R S A, exact U.algebra_map_mem _ },
  .. U }

@[simp] lemma res_top : res R (⊤ : subalgebra S A) = ⊤ :=
algebra.eq_top_iff.2 $ λ _, show _ ∈ (⊤ : subalgebra S A), from algebra.mem_top

@[simp] lemma mem_res {U : subalgebra S A} {x : A} : x ∈ res R U ↔ x ∈ U := iff.rfl

lemma res_inj {U V : subalgebra S A} (H : res R U = res R V) : U = V :=
ext $ λ x, by rw [← mem_res R, H, mem_res]

/-- Produces a map from `subalgebra.under`. -/
def of_under {R A B : Type*} [comm_semiring R] [comm_semiring A] [semiring B]
  [algebra R A] [algebra R B] (S : subalgebra R A) (U : subalgebra S A)
  [algebra S B] [is_scalar_tower R S B] (f : U →ₐ[S] B) : S.under U →ₐ[R] B :=
{ commutes' := λ r, (f.commutes (algebra_map R S r)).trans (algebra_map_apply R S B r).symm,
  .. f }

end subalgebra

namespace is_scalar_tower

open subalgebra

variables [comm_semiring R] [comm_semiring S] [comm_semiring A]
variables [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A]

theorem range_under_adjoin (t : set A) :
  (to_alg_hom R S A).range.under (algebra.adjoin _ t) = res R (algebra.adjoin S t) :=
subalgebra.ext $ λ z,
show z ∈ subsemiring.closure (set.range (algebra_map (to_alg_hom R S A).range A) ∪ t : set A) ↔
  z ∈ subsemiring.closure (set.range (algebra_map S A) ∪ t : set A),
from suffices set.range (algebra_map (to_alg_hom R S A).range A) = set.range (algebra_map S A),
  by rw this,
by { ext z, exact ⟨λ ⟨⟨x, y, _, h1⟩, h2⟩, ⟨y, h2 ▸ h1⟩, λ ⟨y, hy⟩, ⟨⟨z, y, set.mem_univ _, hy⟩, rfl⟩⟩ }

end is_scalar_tower

section
open_locale classical
lemma algebra.fg_trans' {R S A : Type*} [comm_ring R] [comm_ring S] [comm_ring A]
  [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A]
  (hRS : (⊤ : subalgebra R S).fg) (hSA : (⊤ : subalgebra S A).fg) :
  (⊤ : subalgebra R A).fg :=
let ⟨s, hs⟩ := hRS, ⟨t, ht⟩ := hSA in ⟨s.image (algebra_map S A) ∪ t,
by rw [finset.coe_union, finset.coe_image, algebra.adjoin_union, algebra.adjoin_algebra_map, hs,
    algebra.map_top, is_scalar_tower.range_under_adjoin, ht, subalgebra.res_top]⟩
end

namespace submodule

open is_scalar_tower

variables [comm_semiring R] [semiring S] [add_comm_monoid A]
variables [algebra R S] [semimodule S A] [semimodule R A] [is_scalar_tower R S A]

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
variables [comm_semiring R] [semiring S] [add_comm_monoid A]
variables [algebra R S] [semimodule S A] [semimodule R A] [is_scalar_tower R S A]

namespace submodule

open is_scalar_tower

theorem smul_mem_span_smul_of_mem {s : set S} {t : set A} {k : S} (hks : k ∈ span R s)
  {x : A} (hx : x ∈ t) : k • x ∈ span R (s • t) :=
span_induction hks (λ c hc, subset_span $ set.mem_smul.2 ⟨c, x, hc, hx, rfl⟩)
  (by { rw zero_smul, exact zero_mem _ })
  (λ c₁ c₂ ih₁ ih₂, by { rw add_smul, exact add_mem _ ih₁ ih₂ })
  (λ b c hc, by { rw is_scalar_tower.smul_assoc, exact smul_mem _ _ hc })

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

open finsupp
open_locale big_operators classical
universes v₁ w₁

variables {R S A}
variables [comm_ring R] [ring S] [add_comm_group A]
variables [algebra R S] [module S A] [module R A] [is_scalar_tower R S A]

theorem linear_independent_smul {ι : Type v₁} {b : ι → S} {ι' : Type w₁} {c : ι' → A}
  (hb : linear_independent R b) (hc : linear_independent S c) :
  linear_independent R (λ p : ι × ι', b p.1 • c p.2) :=
begin
  rw linear_independent_iff' at hb hc, rw linear_independent_iff'', rintros s g hg hsg ⟨i, k⟩,
  by_cases hik : (i, k) ∈ s,
  { have h1 : ∑ i in (s.image prod.fst).product (s.image prod.snd), g i • b i.1 • c i.2 = 0,
    { rw ← hsg, exact (finset.sum_subset finset.subset_product $ λ p _ hp,
        show g p • b p.1 • c p.2 = 0, by rw [hg p hp, zero_smul]).symm },
    rw [finset.sum_product, finset.sum_comm] at h1,
    simp_rw [← smul_assoc, ← finset.sum_smul] at h1,
    exact hb _ _ (hc _ _ h1 k (finset.mem_image_of_mem _ hik)) i (finset.mem_image_of_mem _ hik) },
  exact hg _ hik
end

theorem is_basis.smul {ι : Type v₁} {b : ι → S} {ι' : Type w₁} {c : ι' → A}
  (hb : is_basis R b) (hc : is_basis S c) : is_basis R (λ p : ι × ι', b p.1 • c p.2) :=
⟨linear_independent_smul hb.1 hc.1,
by rw [← set.range_smul_range, submodule.span_smul hb.2, ← submodule.restrict_scalars'_top R S A,
    submodule.restrict_scalars'_inj, hc.2]⟩

theorem is_basis.smul_repr
  {ι ι' : Type*} {b : ι → S} {c : ι' → A}
  (hb : is_basis R b) (hc : is_basis S c) (x : A) (ij : ι × ι') :
  (hb.smul hc).repr x ij = hb.repr (hc.repr x ij.2) ij.1 :=
begin
  apply (hb.smul hc).repr_apply_eq,
  { intros x y, ext, simp only [linear_map.map_add, add_apply, pi.add_apply] },
  { intros c x, ext,
    simp only [← is_scalar_tower.algebra_map_smul S c x, linear_map.map_smul, smul_eq_mul,
               ← algebra.smul_def, smul_apply, pi.smul_apply] },
  rintros ij,
  ext ij',
  rw single_apply,
  split_ifs with hij,
  { simp [hij] },
  rw [linear_map.map_smul, smul_apply, hc.repr_self_apply],
  split_ifs with hj,
  { simp [hj, show ¬ (ij.1 = ij'.1), from λ hi, hij (prod.ext hi hj)] },
  simp
end

theorem is_basis.smul_repr_mk
  {ι ι' : Type*} {b : ι → S} {c : ι' → A}
  (hb : is_basis R b) (hc : is_basis S c) (x : A) (i : ι) (j : ι') :
  (hb.smul hc).repr x (i, j) = hb.repr (hc.repr x j) i :=
by simp [is_basis.smul_repr]

end ring

section artin_tate

variables (C : Type*)
variables [comm_ring A] [comm_ring B] [comm_ring C]
variables [algebra A B] [algebra B C] [algebra A C] [is_scalar_tower A B C]

open finset submodule
open_locale classical

lemma exists_subalgebra_of_fg (hAC : (⊤ : subalgebra A C).fg) (hBC : (⊤ : submodule B C).fg) :
  ∃ B₀ : subalgebra A B, B₀.fg ∧ (⊤ : submodule B₀ C).fg :=
begin
  cases hAC with x hx,
  cases hBC with y hy, have := hy,
  simp_rw [eq_top_iff', mem_span_finset] at this, choose f hf,
  let s : finset B := (finset.product (x ∪ (y * y)) y).image (function.uncurry f),
  have hsx : ∀ (xi ∈ x) (yj ∈ y), f xi yj ∈ s := λ xi hxi yj hyj,
    show function.uncurry f (xi, yj) ∈ s,
    from mem_image_of_mem _ $ mem_product.2 ⟨mem_union_left _ hxi, hyj⟩,
  have hsy : ∀ (yi yj yk ∈ y), f (yi * yj) yk ∈ s := λ yi yj yk hyi hyj hyk,
    show function.uncurry f (yi * yj, yk) ∈ s,
    from mem_image_of_mem _ $ mem_product.2 ⟨mem_union_right _ $ finset.mul_mem_mul hyi hyj, hyk⟩,
  have hxy : ∀ xi ∈ x, xi ∈ span (algebra.adjoin A (↑s : set B)) (↑(insert 1 y : finset C) : set C) :=
    λ xi hxi, hf xi ▸ sum_mem _ (λ yj hyj, smul_mem
      (span (algebra.adjoin A (↑s : set B)) (↑(insert 1 y : finset C) : set C))
      ⟨f xi yj, algebra.subset_adjoin $ hsx xi hxi yj hyj⟩
      (subset_span $ mem_insert_of_mem hyj)),
  have hyy : span (algebra.adjoin A (↑s : set B)) (↑(insert 1 y : finset C) : set C) *
      span (algebra.adjoin A (↑s : set B)) (↑(insert 1 y : finset C) : set C) ≤
    span (algebra.adjoin A (↑s : set B)) (↑(insert 1 y : finset C) : set C),
  { rw [span_mul_span, span_le, coe_insert], rintros _ ⟨yi, yj, rfl | hyi, rfl | hyj, rfl⟩,
    { rw mul_one, exact subset_span (set.mem_insert _ _) },
    { rw one_mul, exact subset_span (set.mem_insert_of_mem _ hyj) },
    { rw mul_one, exact subset_span (set.mem_insert_of_mem _ hyi) },
    { rw ← hf (yi * yj), exact (submodule.mem_coe _).2 (sum_mem _ $ λ yk hyk, smul_mem
        (span (algebra.adjoin A (↑s : set B)) (insert 1 ↑y : set C))
        ⟨f (yi * yj) yk, algebra.subset_adjoin $ hsy yi yj yk hyi hyj hyk⟩
        (subset_span $ set.mem_insert_of_mem _ hyk : yk ∈ _)) } },
  refine ⟨algebra.adjoin A (↑s : set B), subalgebra.fg_adjoin_finset _, insert 1 y, _⟩,
  refine restrict_scalars'_injective _ _ (_ : restrict_scalars' A _ = _),
  rw [restrict_scalars'_top, eq_top_iff, ← algebra.coe_top, ← hx, algebra.adjoin_eq_span, span_le],
  refine λ r hr, monoid.in_closure.rec_on hr hxy (subset_span $ mem_insert_self _ _)
      (λ p q _ _ hp hq, hyy $ submodule.mul_mem_mul hp hq)
end

/-- Artin--Tate lemma: if A ⊆ B ⊆ C is a chain of subrings of commutative rings, and
A is noetherian, and C is algebra-finite over A, and C is module-finite over B,
then B is algebra-finite over A.

References: Atiyah--Macdonald Proposition 7.8; Stacks 00IS; Altman--Kleiman 16.17. -/
theorem fg_of_fg_of_fg [is_noetherian_ring A]
  (hAC : (⊤ : subalgebra A C).fg) (hBC : (⊤ : submodule B C).fg)
  (hBCi : function.injective (algebra_map B C)) :
  (⊤ : subalgebra A B).fg :=
let ⟨B₀, hAB₀, hB₀C⟩ := exists_subalgebra_of_fg A B C hAC hBC in
algebra.fg_trans' (B₀.fg_top.2 hAB₀) $ subalgebra.fg_of_submodule_fg $
have is_noetherian_ring B₀, from is_noetherian_ring_of_fg hAB₀,
have is_noetherian B₀ C, by exactI is_noetherian_of_fg_of_noetherian' hB₀C,
by exactI fg_of_injective (is_scalar_tower.to_alg_hom B₀ B C).to_linear_map
  (linear_map.ker_eq_bot.2 hBCi)

end artin_tate
