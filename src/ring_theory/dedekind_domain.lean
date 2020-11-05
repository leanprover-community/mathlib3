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
  apply mem_supr_of_mem,
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
        by_contradiction,
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
      simp at hx2,
      assumption,
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
      by_contradiction,
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
    rw mem_coe at f',
    rcases f' with ⟨y, hy, f'⟩,
    change x ∈ (p : fractional_ideal(fraction_ring.of A)).val,
    rw <-f',
    have f'' : y*z ∈ p,
    {
      suffices g : x * (localization_map.to_map (fraction_ring.of A) z) ∈ (p : fractional_ideal (fraction_ring.of A)),
      {
        rw <-f' at g,
        rw <-ring_hom.map_mul at g,
        rw mem_coe at g,
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
