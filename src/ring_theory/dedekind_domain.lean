/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import field_theory.minimal_polynomial
import linear_algebra.finite_dimensional
import logic.function.basic
import order.zorn
import ring_theory.adjoin_root
import ring_theory.discrete_valuation_ring
import ring_theory.fractional_ideal
import ring_theory.ideal.over
import ring_theory.polynomial.rational_root
import ring_theory.trace
import set_theory.cardinal
import tactic

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
 - `is_dedekind_domain_inv_iff` shows that this does not depend on the choice of field of fractions.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]

## Tags

dedekind domain, dedekind ring
-/

variables (A K : Type*) [integral_domain A] [field K]

/-- A ring `R` has Krull dimension at most one if all nonzero prime ideals are maximal. -/
def ring.dimension_le_one (R : Type*) [comm_ring R] : Prop :=
∀ p ≠ (⊥ : ideal R), p.is_prime → p.is_maximal

open ideal ring

namespace ring

lemma dimension_le_one.principal_ideal_ring
  [is_principal_ideal_ring A] : dimension_le_one A :=
λ p nonzero prime, by { haveI := prime, exact is_prime.to_maximal_ideal nonzero }

lemma dimension_le_one.integral_closure (R : Type*) [comm_ring R] [nontrivial R] [algebra R A]
  (h : dimension_le_one R) : dimension_le_one (integral_closure R A) :=
begin
  intros p ne_bot prime,
  haveI := prime,
  refine integral_closure.is_maximal_of_is_maximal_comap p
  (h _ (integral_closure.comap_ne_bot ne_bot) _),
  apply is_prime.comap
end
end ring

open ring

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

lemma mul_val (I J : fractional_ideal (fraction_ring.of A)) : (I*J).val = I.val*J.val :=
begin
  simp only [val_eq_coe, coe_mul],
end

lemma ext' (I J : fractional_ideal (fraction_ring.of A)) : I = J ↔ ∀ (x : localization_map.codomain (fraction_ring.of A)), (x ∈ I ↔ x ∈ J) :=
begin
  split,
  { rintros h x,
    rw h },
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

-- TODO: times out
lemma ideal_le_iff_frac_ideal_le (I J : ideal A) : I ≤ J ↔ (I : fractional_ideal (fraction_ring.of A)) ≤ (J : fractional_ideal (fraction_ring.of A)) :=
begin
  split,
  {
    rintros h,
    tidy,
  },
  rintros h,
  rw le_iff at h,
  change (∀ (x : A), x ∈ I → x ∈ J),
  rintros x hI,
  specialize h ((localization_map.to_map (fraction_ring.of A)) x),
  rw mem_coe at h,
  simp at h,
  specialize h x hI rfl,
  rcases h with ⟨y, hJ, h⟩,
  have f : y = x,
  apply fraction_map.injective (fraction_ring.of A),
  assumption,
  rw f at hJ,
  assumption,
end

open_locale classical -- to deal with union of two finsets!

universes u v

variables (B : Type u) [semiring B]
variables (M : Type v) [add_comm_monoid M] [semimodule B M]

open submodule

lemma submodule.mem_span_finite_of_mem_span (S : set M) (x : M) (hx : x ∈ span B S) :
  ∃ T : set M, T ⊆ S ∧ T.finite ∧ x ∈ span B T :=
begin
  use {x},
  split,
  {
    sorry,
  },
  sorry,
end

lemma noeth : is_dedekind_domain_inv A -> is_noetherian_ring A :=
begin
  rintros h,
  rcases h with ⟨h1, h2⟩,
  split,
  rintros s,
  specialize h2 s,
  by_cases s = ⊥,
  {
    rw h,
    apply submodule.fg_bot,
  },
  let p : ideal A := s,
  change p ≠ ⊥ at h,
  rw coe_ne_bot A at h,
  have h' := h2 h,
  have g : (1 : ideal A).fg,
  {
    unfold submodule.fg,
    use {1},
    rw submodule.one_eq_span,
    simp,
  },
  rw ext' at h',
  specialize h' 1,
  have h'' := h'.2 one_mem_one,
  unfold has_mul.mul at h'',
  revert h'',
  -- TODO: this step doesn't work any more.
  apply submodule.mem_supr_of_mem,
  have f' := submodule.exists_finset_of_mem_supr h',
  have g' : s ≤ 1,
  {
    sorry,
  },
  --have f' : comap _ ((s : fractional_ideal(fraction_ring.of A)) * (s : fractional_ideal(fraction_ring.of A))⁻¹) = comap _ (1 : fractional_ideal(fraction_ring.of A)),
  rw subtype.ext_iff at h',
  have f' := submodule.fg_map g,
  swap 5,
  refine localization_map.lin_coe f,
  rw coe_one at h',
  rw <-h' at f',
  simp at h',
--  have f' := submodule.fg_map 1 f,
 -- rw submodule.fg_map _ 1 at f,
  --rw subtype.ext_iff at h',
  rw coe_mul at h',

  rw <-h' at f,

  sorry,
end

lemma fg_is_frac_ideal (I : submodule A (localization_map.codomain (fraction_ring.of A))) : I.fg -> is_fractional (fraction_ring.of A) I :=
fractional_of_fg

lemma fraction_ring_fractional_ideal (x : (fraction_ring A)) (hx : is_integral A x) : is_fractional (fraction_ring.of A) ((algebra.adjoin A {x}).to_submodule : submodule A (localization_map.codomain (fraction_ring.of A))) :=
fractional_of_fg (fg_adjoin_singleton_of_integral x hx)

lemma mem_adjoin (x : fraction_ring A) : x ∈ ((algebra.adjoin A {x}) : subalgebra A (localization_map.codomain (fraction_ring.of A))) :=
begin
  apply subsemiring.subset_closure,
  simp,
end

lemma int_close : is_dedekind_domain_inv A -> integral_closure A (fraction_ring A) = ⊥ :=
begin
  rintros h,
  ext,
  split,
  {
    rintros hx,
    cases h with h1 h2,
    let S : subalgebra A (localization_map.codomain (fraction_ring.of A)) := algebra.adjoin A {x},
    have f' : is_fractional _ (S.to_submodule),
    {
      apply fraction_ring_fractional_ideal,
      rcases hx with ⟨p, hp1, hp2⟩,
      split,
      rotate,
      use p,
      split,
      assumption,
      assumption,
    },
    let M : fractional_ideal (fraction_ring.of A) := ⟨S.to_submodule, f'⟩,
    by_cases x = 0,
    rw h,
    apply subalgebra.zero_mem ⊥,
    have f : M = 1,
    {
      specialize h2 M,
      rw <-mul_one M,
      have g : M ≠ ⊥,
      {
        classical,
        by_contradiction a,
        simp at a,
        rw subtype.ext_iff_val at a,
        simp at a,
        rw submodule.eq_bot_iff S.to_submodule at a,
        specialize a x,
        apply h,
        apply a,
        change x ∈ (S : submodule A (localization_map.codomain (fraction_ring.of A))),
        rw subalgebra.mem_to_submodule,
        apply mem_adjoin,
      },
      have hM := h2 g,
      suffices hM' : M * (M * M⁻¹) = 1,
      rw hM at hM',
      assumption,
      suffices hM' : M * M = M,
      assoc_rw hM',
      assumption,
      rw subtype.ext_iff_val,
      simp,
      change (S : submodule A (localization_map.codomain (fraction_ring.of A))) * (S : submodule A (localization_map.codomain (fraction_ring.of A))) = (S : submodule A (localization_map.codomain (fraction_ring.of A))),
      ext,
      split,
      {
        rintros hx2,
        have hmul : (S : submodule A (localization_map.codomain (fraction_ring.of A))) * (S : submodule A (localization_map.codomain (fraction_ring.of A))) ≤ (S : submodule A (localization_map.codomain (fraction_ring.of A))),
        {
          rw submodule.mul_le,
          rintros y hy z hz,
          rw subalgebra.mem_to_submodule at hy,
          rw subalgebra.mem_to_submodule at hz,
          rw subalgebra.mem_to_submodule,
          apply (subalgebra.mul_mem S hy hz),
        },
        change (∀ x ∈ (S : submodule A (localization_map.codomain (fraction_ring.of A))) * (S : submodule A (localization_map.codomain (fraction_ring.of A))), x ∈ (S : submodule A (localization_map.codomain (fraction_ring.of A)))) at hmul,
        exact hmul x_1 hx2,
      },
      rintros hx1,
      have h1 := subalgebra.one_mem S,
      rw <-subalgebra.mem_to_submodule at h1,
      have hx2 := submodule.mul_mem_mul hx1 h1,
      simpa using hx2,
    },
    have fx : x ∈ M,
    change x ∈ (S : submodule A (localization_map.codomain (fraction_ring.of A))),
    rw subalgebra.mem_to_submodule,
    apply mem_adjoin,
    suffices h' : x ∈ ((⊥ : subalgebra A (localization_map.codomain (fraction_ring.of A))) : submodule A (localization_map.codomain (fraction_ring.of A))),
    rw subalgebra.mem_to_submodule at h',
    assumption,
    rw algebra.to_submodule_bot,
    rw ext' at f,
    specialize f x,
    have g' := f.1 fx,
    rw <-coe_span_singleton 1,
    rw ring.fractional_ideal.span_singleton_one,
    apply iff.rfl.1 g',
  },
  rintros hx,
  rw mem_integral_closure_iff_mem_fg,
  use ⊥,
  split,
  unfold submodule.fg,
  use {1},
  rw algebra.to_submodule_bot,
  simp,
  assumption,
end

lemma dim_le_one : is_dedekind_domain_inv A -> dimension_le_one A :=
begin
  rintros h,
  rcases h with ⟨h1, h2⟩,
  rintros p nz hp,
  have hpinv := h2 p,
  have hpmax := exists_le_maximal p hp.1,
  rcases hpmax with ⟨M, hM1, hM2⟩,
  specialize h2 M,
  specialize hpinv ((coe_ne_bot A p).1 nz),
  specialize h2 ( (coe_ne_bot A M).1 (max_ideal_ne_bot A M hM1 h1)),
  set I := (M : fractional_ideal (fraction_ring.of A))⁻¹ * (p : fractional_ideal (fraction_ring.of A)) with hI,
  have f' : I ≤ 1,
  {
    set N := (M : fractional_ideal (fraction_ring.of A))⁻¹ with hN,
    rw ideal_le_iff_frac_ideal_le at hM2,
    have g'' := submodule.mul_le_mul hM2 (le_refl N),
    simp only [val_eq_coe, <-coe_mul] at g'',
    norm_cast at g'',
    rw h2 at g'',
    rw mul_comm at g'',
    exact g'',
  },
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
    rw le_iff,
    rintros x hxI,
    have hpM :  ∃ (x : A), x ∈ M ∧ x ∉ p,
    {
      classical,
      by_contradiction a,
      simp at a,
      change M ≤ p at a,
      apply h,
      rw <-has_le.le.le_iff_eq a,
      assumption,
    },
    rcases hpM with ⟨z, hz, hpz⟩,
    rw le_iff at f',
    specialize f' x hxI,
    change x ∈ ((1 : ideal A) : fractional_ideal (fraction_ring.of A)) at f',
    rw fractional_ideal.mem_coe_ideal at f',
    rcases f' with ⟨y, hy, f'⟩,
    change x ∈ (p : fractional_ideal(fraction_ring.of A)).val,
    rw <-f',
    have f'' : y*z ∈ p,
    {
      suffices g : x * (localization_map.to_map (fraction_ring.of A) z) ∈ (p : fractional_ideal (fraction_ring.of A)),
      {
        rw <-f' at g,
        rw <-ring_hom.map_mul at g,
        rw fractional_ideal.mem_coe_ideal at g,
        rcases g with ⟨x', Hx, g⟩,
        suffices g'' : x' = (y*z),
        rw g'' at Hx,
        assumption,
        revert g,
        apply fraction_map.injective (fraction_ring.of A),
      },
      rw <-f,
      rw mul_comm,
      apply submodule.mul_mem_mul,
      let z' := (localization_map.to_map (fraction_ring.of A)) z,
      change z' ∈ (M : fractional_ideal (fraction_ring.of A)),
      rw mem_coe,
      use z,
      split, assumption, refl,
      assumption,
    },
    unfold is_prime at hp,
    have hp' := hp.right f'',
    cases hp',
    {
      let z' := (localization_map.to_map (fraction_ring.of A)) y,
      change z' ∈ (p : fractional_ideal (fraction_ring.of A)),
      rw mem_coe,
      use y,
      split, assumption, refl,
    },
    finish,
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
end

theorem tp : is_dedekind_domain_inv A <-> is_dedekind_domain A :=
begin
  split,
  {
    rintros h,
    split,
    {
      apply h.1,
    },
    {
      apply noeth,
      assumption,
    },
    {
      apply dim_le_one,
      assumption,
    },
    {
      apply int_close,
      assumption,
    },
  },
  sorry,
end

end

lemma integrally_closed_iff_integral_implies_integer {R : Type*}
  [comm_ring R] [comm_ring K] {f : fraction_map R K} :
  integral_closure R f.codomain = ⊥ ↔ ∀ x : f.codomain, is_integral R x → f.is_integer x :=
subalgebra.ext_iff.trans
  ⟨ λ h x hx, algebra.mem_bot.mp ((h x).mp hx),
    λ h x, iff.trans
      ⟨λ hx, h x hx, λ ⟨y, hy⟩, hy ▸ is_integral_algebra_map⟩
      (@algebra.mem_bot R f.codomain _ _ _ _).symm⟩

instance principal_ideal_ring.to_dedekind_domain [is_principal_ideal_ring A]
  [field K] (f : fraction_map A K) (not_field : ¬ is_field A) :
  is_dedekind_domain A :=
(is_dedekind_domain_iff A K f).mpr
⟨not_field, principal_ideal_ring.is_noetherian_ring, dimension_le_one.principal_ideal_ring _,
  @unique_factorization_monoid.integrally_closed A _ _
    (principal_ideal_ring.to_unique_factorization_monoid) _ _⟩

namespace dedekind_domain

variables {R S : Type*} [integral_domain R] [integral_domain S] [algebra R S]
variables {L : Type*} [field L] {f : fraction_map R K}

open finsupp polynomial

variables {M : ideal R} [is_maximal M]

lemma if_inv_then_int { I : ideal R } (hR : is_dedekind_domain R) (x : f.codomain) (h_nzI : I ≠ 0)
  (h_prod : (↑I : fractional_ideal f) * (1 / ↑I : fractional_ideal f) = ↑I) :
  x ∈ (1/↑I : fractional_ideal f) → (f.to_map).is_integral_elem x :=
begin
  intro hx,
  let h_RalgK := ring_hom.to_algebra f.to_map,
  have h_prod_mem : ∀ a ∈ I, ∀ t ∈ (1 / ↑I : fractional_ideal f), f.to_map a * t ∈ (↑I : fractional_ideal f),
  { intros a ha t ht,
    rw ← h_prod,
    have hfa : f.to_map a ∈ (↑I : fractional_ideal f),
    apply fractional_ideal.mem_coe_ideal.mpr,
    use a,
    apply and.intro ha rfl,
    apply fractional_ideal.mul_mem_mul hfa ht },
  have h_Samuel : ∀ n : ℕ, ∀ y ∈ I, f.to_map y * x ^ n ∈ (↑I : fractional_ideal f).val,
  { intro n,
    induction n with n hn,
    { intros y hy,
      ring,
      apply (fractional_ideal.mem_coe_ideal).mpr,
      use y,
      apply and.intro hy rfl },
    { intros y hy,
      obtain ⟨z, ⟨hz₁, hz₂⟩ ⟩ : ∃ z ∈ I, f.to_map z = f.to_map y * x,
      { apply (fractional_ideal.mem_coe_ideal).mp,
        apply h_prod_mem, exact hy,
        exact hx },
      rw [pow_succ, ← mul_assoc (f.to_map y) x (x^n), ← hz₂],
      specialize hn z hz₁,
      exact hn } },
  let φ := @aeval R K _ _ h_RalgK x,
  let A := @alg_hom.range R (polynomial R) f.codomain _ _ _  _ h_RalgK φ,
  have h_xA : x ∈ A,
  { suffices hp : ∃ (p : polynomial R), φ p = x,
    simpa,
    use X,
    apply aeval_X },
  have h_fracA : is_fractional f A,
  { obtain ⟨y, ⟨h_Iy, h_nzy⟩⟩ : ∃ y ∈ I, y ≠ (0 : R),
    { apply (submodule.ne_bot_iff I).mp,
      exact h_nzI },
    use y,
    split,
    { apply mem_non_zero_divisors_iff_ne_zero.mpr h_nzy },
    { suffices h_intmon : ∀ (n : ℕ), f.is_integer (f.to_map y * x ^ n),
      { have h_intpol : ∀ (p : polynomial R), f.is_integer (f.to_map y * eval₂ f.to_map x p),
        { intro p,
          apply polynomial.induction_on' p,
          { intros q₁ q₂,
            rw [eval₂_add, left_distrib],
            apply localization_map.is_integer_add },
            { intros n a,
              rw [monomial_eq_smul_X, eval₂_smul, algebra.mul_smul_comm],
              apply localization_map.is_integer_smul,
              rw eval₂_X_pow,
              specialize h_intmon n,
              exact h_intmon }, },
        intros b hb,
        obtain ⟨polb, h_polb⟩ : ∃ (p : polynomial R), eval₂ f.to_map x p = b,
        { cases hb with pb h_pb,
          use pb,
          rw ← h_pb.right,
          apply aeval_def x pb },
        rw ← h_polb,
        specialize h_intpol polb,
        exact h_intpol },
      { intro n,
        specialize h_Samuel n y h_Iy,
        obtain ⟨z, ⟨ - , hz⟩⟩ :  ∃ (x' ∈ I), f.to_map x' = (f.to_map y) * x ^ n,
        { apply (fractional_ideal.mem_coe_ideal).mp,
        exact h_Samuel },
        use [z, hz] } } },
  let IA : fractional_ideal f := ⟨A, h_fracA⟩,
  have h_noethA : is_noetherian R A,
  { apply fractional_ideal.fg_of_noetherian hR.2 IA },
  obtain ⟨px, h_px , h_int_x⟩ : is_integral R x,
  { apply @is_integral_of_submodule_noetherian R K _ _ h_RalgK A h_noethA x h_xA },
  use px,
  apply and.intro h_px h_int_x,
end

local attribute [instance] classical.prop_decidable

lemma inv_of_maximal_not_top (hR : is_dedekind_domain R) (hM : ideal.is_maximal M) :
  (1 / ↑M : fractional_ideal f) ≠ (1 : fractional_ideal f) :=
begin sorry,
end

lemma maximal_ideal_inv_of_dedekind (hR : is_dedekind_domain R) (hM : ideal.is_maximal M) :
  is_unit (M : fractional_ideal f) :=
begin
  have hnz_M : M ≠ 0, apply (lt_iff_le_and_ne.mp (ideal.bot_lt_of_maximal M hR.1) ).2.symm,
  have hnz_Mf : (↑M : fractional_ideal f) ≠ (⊥ : fractional_ideal f),
  apply (fractional_ideal.coe_nonzero_of_nonzero _).mp hnz_M, tauto,
  have h_MfinR : (↑M : fractional_ideal f) ≤ (1 : fractional_ideal f),
  apply fractional_ideal.coe_ideal_le_one,
  have hM_inclMinv : (↑M : fractional_ideal f) ≤ (↑M : fractional_ideal f) * (1 / (↑M : fractional_ideal f)),
  from fractional_ideal.le_self_mul_one_div h_MfinR,
  have h_self : (↑M : fractional_ideal f) ≤ (1 : fractional_ideal f) * ↑M,
  ring, exact le_refl ↑M,
  have hMMinv_inclR : ↑M * (1 / ↑M) ≤ (1 : fractional_ideal f),
    from fractional_ideal.mul_one_div_le_one,
  suffices hprod : ↑M * ((1: fractional_ideal f) / ↑M) = (1 : fractional_ideal f),
  apply is_unit_of_mul_eq_one ↑M ((1 : fractional_ideal f) / ↑M) hprod,
  obtain ⟨I, hI⟩ : ∃ (I : ideal R), ↑I = ↑M * ((1 : fractional_ideal f) / ↑M),
  ring, apply (fractional_ideal.le_one_iff_exists_coe_ideal.mp hMMinv_inclR),
  have h_Iincl : M ≤ I,
  { suffices h_Iincl_f : (↑M : fractional_ideal f) ≤ (↑I : fractional_ideal f),
    { intros x hx,
      let y := f.to_map x,
      have defy : f.to_map x = y, refl,
      have hy : y ∈  (↑M : fractional_ideal f),
      { simp only [exists_prop, fractional_ideal.mem_coe_ideal], use x, exact ⟨hx, defy⟩ },
      replace hy : y ∈ (↑I : fractional_ideal f),
      apply fractional_ideal.le_iff_mem.mp h_Iincl_f, assumption,
      obtain ⟨a, ⟨ ha, hfa ⟩ ⟩ : ∃ (x' ∈ I), f.to_map x' = y,
      apply fractional_ideal.mem_coe_ideal.mp hy,
      have hax : a = x,
      { suffices haxf : f.to_map a = f.to_map x,
        apply fraction_map.injective f haxf, rw hfa },
      subst hax, assumption },
    { rw hI, assumption },
  },
  have h_top : I= ⊤,
  { by_contradiction h_abs,
    have h_IM : I = M, apply (is_maximal.eq_of_le hM h_abs h_Iincl).symm,
    have h_inveqR : 1 / ↑M = (1 : fractional_ideal f),
    { have h_MMinvI : ↑M * (1 / ↑M : fractional_ideal f) = ↑M, rw [← hI, h_IM],
      suffices h_invR_dbl : 1 / ↑M ≤ (1 : fractional_ideal f) ∧ (1 : fractional_ideal f) ≤ 1 / ↑M,
      apply (has_le.le.le_iff_eq h_invR_dbl.right).mp (h_invR_dbl.left),
      split,
      { intros x hx,
         have h_integralfx : (f.to_map).is_integral_elem x,
         apply if_inv_then_int _ hR x hnz_M h_MMinvI hx,
         have h_intxR : x ∈ (integral_closure R f.codomain), apply h_integralfx,
         have h_xint : x ∈ ((⊥  : subalgebra R f.codomain) : submodule R f.codomain),
         { rw ← ((is_dedekind_domain_iff _ _ f).mp hR).right.right.right, exact h_intxR },
        rw [algebra.to_submodule_bot, ← (fractional_ideal.coe_span_singleton 1)] at h_xint,
        rw [← fractional_ideal.span_singleton_one,
          (fractional_ideal.val_eq_coe (fractional_ideal.span_singleton 1))],
        exact h_xint },
      { apply (fractional_ideal.le_div_iff_mul_le hnz_Mf).mpr,
        ring, exact h_MfinR } },
    apply inv_of_maximal_not_top K hR hM,
    assumption },
  have h_okfI : ↑I = (1 : fractional_ideal f), apply fractional_ideal.ext_iff.mp,
  intros x, split, repeat {intro hx},
  { replace hx : ∃ (x' ∈  (I : ideal R)), f.to_map x' = x,
    apply fractional_ideal.mem_coe_ideal.mp hx,
    apply fractional_ideal.mem_one_iff.mpr,
    rcases hx with ⟨a, ⟨ha, hfa⟩⟩,
    use a, exact hfa },
  { replace hx : ∃ x' ∈ (1 : ideal R),  f.to_map x' = x,
    apply fractional_ideal.mem_coe_ideal.mp hx,
    rw h_top, simp only [submodule.mem_top, fractional_ideal.mem_coe_ideal, exists_prop_of_true],
    rcases hx with ⟨a, ⟨ha,hfa⟩⟩,
    use a, exact hfa },
  rw ← hI, exact h_okfI,
end


lemma fractional_ideal_invertible_of_dedekind (h : is_dedekind_domain R) (I : fractional_ideal f) :
  I * I⁻¹ = 1 :=
begin
  sorry
end

instance subalgebra.algebra_left {R A B : Type*} [comm_semiring R] [comm_semiring A]
  [semiring B] [algebra R A] [algebra A B] (S : subalgebra A B) : algebra R S := sorry

instance intermediate_field.algebra_left {R A B : Type*} [comm_semiring R] [field A]
  [field B] [algebra R A] [algebra A B] (S : intermediate_field A B) : algebra R S := sorry

lemma integral_closure_le_adjoin [algebra f.codomain L] [algebra R L] [is_scalar_tower R f.codomain L]
  (s : finset L) :
  integral_closure R (intermediate_field.adjoin f.codomain (↑s : set L)) ≤
    algebra.adjoin R (sorry '' (↑s : set L)) := sorry

/- If L is a finite extension of K, the integral closure of R in L is a Dedekind domain. -/
def closure_in_field_extension [algebra f.codomain L] [algebra R L] [is_scalar_tower R f.codomain L]
  [finite_dimensional f.codomain L] (h : is_dedekind_domain R) :
  is_dedekind_domain (integral_closure R L) :=
(is_dedekind_domain_iff _ _ (integral_closure.fraction_map_of_finite_extension L f)).mpr
⟨sorry,
 is_noetherian_ring_of_is_noetherian_coe_submodule _ _
   (is_noetherian_of_submodule_of_noetherian _ _ _ sorry),
 h.dimension_le_one.integral_closure _ _,
 integral_closure_idem⟩

end dedekind_domain
