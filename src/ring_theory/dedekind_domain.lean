/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import ring_theory.discrete_valuation_ring
import ring_theory.fractional_ideal
import ring_theory.ideal.over
import logic.function.basic
import field_theory.minimal_polynomial
import ring_theory.adjoin_root

/-!
# Dedekind domains

This file defines the notion of a Dedekind domain (or Dedekind ring),
giving three equivalent definitions (TODO: and shows that they are equivalent).

## Main definitions

 - `is_dedekind_domain` defines a Dedekind domain as a commutative ring that is not a field,
   Noetherian, integrally closed in its field of fractions and has Krull dimension exactly one.
   `is_dedekind_domain_iff` shows that this does not depend on the choice of field of fractions.
 - `is_dedekind_domain_dvr` alternatively defines a Dedekind domain as an integral domain that is not a field,
   Noetherian, and the localization at every nonzero prime ideal is a discrete valuation ring.
 - `is_dedekind_domain_inv` alternatively defines a Dedekind domain as an integral domain that is not a field,
   and every nonzero fractional ideal is invertible.
 - `is_dedekind_domain_inv_iff` shows that this does note depend on the choice of field of fractions.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags

dedekind domain, dedekind ring
-/

variables (R A K : Type*) [comm_ring R] [integral_domain A] [field K]

/-- A ring `R` has Krull dimension at most one if all nonzero prime ideals are maximal. -/
def ring.dimension_le_one : Prop :=
∀ p ≠ (⊥ : ideal R), p.is_prime → p.is_maximal

open ideal ring

namespace ring

lemma dimension_le_one.principal_ideal_ring
  [is_principal_ideal_ring A] : dimension_le_one A :=
λ p nonzero prime, by { haveI := prime, exact is_prime.to_maximal_ideal nonzero }

lemma dimension_le_one.integral_closure [nontrivial R] [algebra R A]
  (h : dimension_le_one R) : dimension_le_one (integral_closure R A) :=
begin
  intros p ne_bot prime,
  haveI := prime,
  refine integral_closure.is_maximal_of_is_maximal_comap p
    (h _ (integral_closure.comap_ne_bot ne_bot) _),
  apply is_prime.comap
end
end ring

/--
A Dedekind domain is an integral domain that is Noetherian, integrally closed, and
has Krull dimension exactly one (`not_is_field` and `dimension_le_one`).

The integral closure condition is independent of the choice of field of fractions:
use `is_dedekind_domain_iff` to prove `is_dedekind_domain` for a given `fraction_map`.

This is the default implementation, but there are equivalent definitions,
`is_dedekind_domain_dvr` and `is_dedekind_domain_inv`.
TODO: Prove that these are actually equivalent definitions.
-/
class is_dedekind_domain : Prop :=
(not_is_field : ¬ is_field A)
(is_noetherian_ring : is_noetherian_ring A)
(dimension_le_one : dimension_le_one A)
(is_integrally_closed : integral_closure A (fraction_ring A) = ⊥)

/-- An integral domain is a Dedekind domain iff and only if it is not a field, is Noetherian, has dimension ≤ 1,
and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
lemma is_dedekind_domain_iff (f : fraction_map A K) :
  is_dedekind_domain A ↔
    (¬ is_field A) ∧ is_noetherian_ring A ∧ dimension_le_one A ∧
    integral_closure A f.codomain = ⊥ :=
⟨λ ⟨hf, hr, hd, hi⟩, ⟨hf, hr, hd,
  by rw [←integral_closure_map_alg_equiv (fraction_ring.alg_equiv_of_quotient f),
         hi, algebra.map_bot]⟩,
 λ ⟨hf, hr, hd, hi⟩, ⟨hf, hr, hd,
  by rw [←integral_closure_map_alg_equiv (fraction_ring.alg_equiv_of_quotient f).symm,
         hi, algebra.map_bot]⟩⟩

/--
A Dedekind domain is an integral domain that is not a field, is Noetherian, and the localization at
every nonzero prime is a discrete valuation ring.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure is_dedekind_domain_dvr : Prop :=
(not_is_field : ¬ is_field A)
(is_noetherian_ring : is_noetherian_ring A)
(is_dvr_at_nonzero_prime : ∀ P ≠ (⊥ : ideal A), P.is_prime →
  discrete_valuation_ring (localization.at_prime P))

/--
A Dedekind domain is an integral domain that is not a field such that every fractional ideal has an inverse.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure is_dedekind_domain_inv : Prop :=
(not_is_field : ¬ is_field A)
(mul_inv_cancel : ∀ I ≠ (⊥ : fractional_ideal (fraction_ring.of A)), I * I⁻¹ = 1)

section

open ring.fractional_ideal

lemma is_dedekind_domain_inv_iff (f : fraction_map A K) :
  is_dedekind_domain_inv A ↔
    (¬ is_field A) ∧ (∀ I ≠ (⊥ : fractional_ideal f), I * I⁻¹ = 1) :=
begin
  split; rintros ⟨hf, hi⟩; use hf; intros I hI,
  { have := hi (map (fraction_ring.alg_equiv_of_quotient f).symm.to_alg_hom I) (map_ne_zero _ hI),
    erw [← map_inv, ← fractional_ideal.map_mul] at this,
    convert congr_arg (map (fraction_ring.alg_equiv_of_quotient f).to_alg_hom) this;
      simp only [alg_equiv.to_alg_hom_eq_coe, map_symm_map, map_one] },
  { have := hi (map (fraction_ring.alg_equiv_of_quotient f).to_alg_hom I) (map_ne_zero _ hI),
    erw [← map_inv, ← fractional_ideal.map_mul] at this,
    convert congr_arg (map (fraction_ring.alg_equiv_of_quotient f).symm.to_alg_hom) this;
      simp only [alg_equiv.to_alg_hom_eq_coe, map_map_symm, map_one] }
end

lemma coe_ne_bot (I :ideal A) : I ≠ ⊥ ↔ (I : fractional_ideal (fraction_ring.of A)) ≠ ⊥ :=
begin
  split,
  {
    rw ring.fractional_ideal.bot_eq_zero,
    contrapose,
    simp only [not_not],
    rw eq_zero_iff,
    rintros h,
    apply ideal.ext,
    rintros x,
    rw ideal.mem_bot,
    simp at h,
    let y:= (localization_map.to_map (fraction_ring.of A)) x,
    specialize h y x,
    split,
    {
      rintros hx,
      have f := h hx,
      simp at f,
      rw localization_map.to_map_eq_zero_iff at f,
      exact f,
      unfold has_le.le,
      simp,
    },
    {
      rintros f,
      rw f,
      simp,
    },
  },
  contrapose, simp, rintros h,
  rw h,
  finish,
end

lemma max_ideal_ne_bot (M : ideal A) (max : M.is_maximal) (not_field : ¬ is_field A) : M ≠ ⊥ :=
begin
  rintros h,
  rw h at max,
  cases max with h1 h2,
  rw not_is_field_iff_exists_ideal_bot_lt_and_lt_top at not_field,
  rcases not_field with ⟨I, hIbot, hItop⟩,
  specialize h2 I hIbot,
  rw h2 at hItop,
  simp at hItop,
  assumption,
end

--lemma blah (I : ideal A) : (I : fractional_ideal (fraction_ring.of A)) = localization_map.to_map (fraction_ring.of A) I
--lemma frac_prime_ideal_is_prime (I : ideal A) (hI : I.is_prime) : is_prime (I : fractional_ideal (fraction_ring.of A)) :=

lemma frac_ideal_le_ideal (I J : ideal A) (h : ∃ x : A, x ∈ I ∧ x ∉ J) (hJ : J.is_prime) (B : fractional_ideal (fraction_ring.of A) ) (g : (I : fractional_ideal (fraction_ring.of A)) * B = (J : fractional_ideal (fraction_ring.of A))) : B ≤ (J : fractional_ideal (fraction_ring.of A)) :=
begin
  rcases h with ⟨x, hI, hJ⟩,
  rw le_iff,
  rintros y hy,
  have f : ((localization_map.to_map (fraction_ring.of A)) x)*y ∈ (J : fractional_ideal (fraction_ring.of A)),
  {
    rw <-g,
    have k : ((localization_map.to_map (fraction_ring.of A)) x) ∈ (I : fractional_ideal (fraction_ring.of A)),
    sorry,
    apply submodule.mul_mem_mul k hy,
  },
  simp at f,
  rcases f with ⟨z, hz1, hz⟩,
  sorry,
end

lemma mul_val (I J : fractional_ideal (fraction_ring.of A)) : (I*J).val = I.val*J.val :=
begin
  simp only [val_eq_coe, coe_mul],
end

lemma ext' (I J : fractional_ideal (fraction_ring.of A)) : I = J ↔ ∀ (x : localization_map.codomain (fraction_ring.of A)), (x ∈ I ↔ x ∈ J) :=
begin
  split,
  {
    rintros,
    rw a,
  },
  rintros,
  apply ring.fractional_ideal.ext,
  apply submodule.ext,
  assumption,
end

lemma one_mem : (1 : localization_map.codomain (fraction_ring.of A)) ∈ ((1 : ideal A) : fractional_ideal (fraction_ring.of A)) :=
begin
  apply one_mem_one,
end

lemma local_one : (localization_map.to_map (fraction_ring.of A)) 1 = 1 :=
begin
  simp,
end

/- lemma fraction_ring_fractional_ideal (x : (fraction_ring A)) (hx : is_integral A x) : is_fractional (fraction_ring.of A) ((adjoin_root (minimal_polynomial hx)) :  submodule A (localization_map.codomain (fraction_ring.of A))) :=
begin
  sorry,
end -/

theorem tp : is_dedekind_domain_inv A <-> is_dedekind_domain A :=
begin
  split,
  {
    rintros h,
    rcases h with ⟨h1, h2⟩,
    split,
    {
      apply h1,
    },
    {
      unfold is_noetherian_ring,
      fconstructor,
      change ∀ (I : ideal A), I.fg,
      rintros I,
   --   fconstructor,
      sorry,
    },
    {
      unfold dimension_le_one,
      rintros p nz hp,
      have hpinv := h2 p,
      have hpmax := exists_le_maximal p hp.1,
      rcases hpmax with ⟨M, hM1, hM2⟩,
      specialize h2 M,
      specialize hpinv ((coe_ne_bot A p).1 nz),
      specialize h2 ( (coe_ne_bot A M).1 (max_ideal_ne_bot A M hM1 h1)),
      set I := (M : fractional_ideal (fraction_ring.of A))⁻¹ * (p : fractional_ideal (fraction_ring.of A)) with hI,
      have f : (M : fractional_ideal (fraction_ring.of A)) * I = (p : fractional_ideal (fraction_ring.of A)),
      {
        change ↑M * ((↑M)⁻¹ * ↑p) = ↑p,
        assoc_rw h2,
        simp,
      },
      by_cases p = M,
      {
        rw h,
        assumption,
      },
      exfalso,
      have g : I ≤ (p : fractional_ideal (fraction_ring.of A)),
      {
        apply frac_ideal_le_ideal A M,
        {
          classical,
          by_contradiction,
          simp at a,
          change M ≤ p at a,
          apply h,
          rw <-has_le.le.le_iff_eq a,
          assumption,
        },
        assumption,
        assumption,
      },
      rw <-subtype.coe_le_coe at g,
      rw hI at g,
      norm_cast at g,
      change ((↑M)⁻¹ * ↑p) ≤ ↑p at g,
      have hM := le_refl (M : fractional_ideal (fraction_ring.of A)),
      have g' := submodule.mul_le_mul g hM,
      rw mul_comm at g',
      simp only [val_eq_coe, <-coe_mul] at g',
      norm_cast at g',
      assoc_rw h2 at g',
      rw one_mul at g',
      set q := (p : fractional_ideal (fraction_ring.of A))⁻¹ with hq,
      have g'' := submodule.mul_le_mul g' (le_refl q),
      simp only [val_eq_coe, <-coe_mul] at g'',
      norm_cast at g'',
      rw hpinv at g'',
      rw mul_comm at g'',
      rw mul_comm at hpinv,
      assoc_rw hpinv at g'',
      rw one_mul at g'',
      have ginv : (M : fractional_ideal (fraction_ring.of A)) ≤ 1,
      {
        change (M : fractional_ideal (fraction_ring.of A)) ≤ ((1 : ideal A) : fractional_ideal (fraction_ring.of A)),
        apply submodule.map_mono,
        simp,
      },
      have k := (has_le.le.le_iff_eq ginv).1 g'',
      cases hM1 with hM11 hM12,
      apply hM11,
      unfold has_one.one at k,
      simp at k,
      change ((1 : ideal A) : fractional_ideal (fraction_ring.of A)) = (M : fractional_ideal (fraction_ring.of A)) at k,
      rw ideal.eq_top_iff_one,
      rw ext' at k,
      specialize k 1,
      have k' := k.1 (one_mem A),
      rw mem_coe at k',
      cases k' with x k',
      cases k' with hx k',
      suffices f' : x = 1,
      rw f' at hx,
      assumption,
      rw <-(local_one A) at k',
      apply fraction_map.injective (fraction_ring.of A),
      assumption,
    },
    {
      ext1,
      split,
      {
        rintros hx,
        cases hx with p hp,
        sorry,
      },
      rintros hx,
      rw mem_integral_closure_iff_mem_fg,
      use ⊥,
      split,
      unfold submodule.fg,
      use {0},
      simp,
--      rw submodule.fg_bot,
      sorry,
      assumption,
    },
  },
  {
    rintros h,
    split,
    {
      apply h.1,
    },
    {
      rintros I hI,
      sorry,
    },
  },
end

end
