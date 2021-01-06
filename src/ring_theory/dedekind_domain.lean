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
import linear_algebra.basic
import algebra.algebra.operations

/-!
# Dedekind domains

This file defines the notion of a Dedekind domain (or Dedekind ring),
giving three equivalent definitions (TODO: and shows that they are equivalent).
We have now shown one side of the equivalence two of these definitions.

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

end

section

open ring.fractional_ideal

variables {A}

open_locale classical

variables {B : Type*} [semiring B]
variables {M : Type*} [add_comm_monoid M] [semimodule B M]

open submodule

lemma submodule.mem_span_mul_finite_of_mem_span_mul {B M : Type*} [comm_semiring B] [semiring M]
  [algebra B M] {S : set M} {S' : set M} {x : M} (hx : x ∈ span B (S * S')) :
  ∃ (T T' : finset M), ↑T ⊆ S ∧ ↑T' ⊆ S' ∧ x ∈ span B (T * T' : set M) :=
begin
  apply span_induction hx,
  { rintros x hx,
    obtain ⟨y, z, hy, hz, h'⟩ := set.mem_mul.mp hx,
    have hy' := submodule.subset_span hy,
    have hz' := submodule.subset_span hz,
    obtain ⟨T, hT, fy⟩ := submodule.mem_span_finite_of_mem_span hy',
    obtain ⟨T', hT', fz⟩ := submodule.mem_span_finite_of_mem_span hz',
    use [T, T', hT, hT'],
    rw [←h', ←submodule.span_mul_span],
    apply mul_mem_mul fy fz, },
  { use [∅, ∅], simp, },
  { rintros x y ⟨T, T', hT, hT', h1⟩ ⟨U, U', hU, hU', h2⟩,
    use [T ∪ U, T' ∪ U'],
    simp only [finset.coe_union],
    use [set.union_subset hT hU, set.union_subset hT' hU'],
    suffices f : x + y ∈ span B ((T * T') ∪ (U * U') : set M),
    { have f' : ((T * T') ∪ (U * U') : set M) ⊆ ((T ∪ U) * (T' ∪ U') : set M),
      { convert set.subset_union_left (T * T' ∪ U * U' : set M) (T * U' ∪ U * T'),
        simp only [set.mul_union, set.union_mul, set.union_mul],
        ac_refl },
      apply span_mono f' f, },
    rw [span_union, mem_sup],
    exact ⟨x, h1, y, h2, rfl⟩ },
  rintros a x ⟨T, T', hT, hT', h⟩,
  exact ⟨T, T', hT, hT', smul_mem _ _ h⟩,
end

lemma submodule.mem_span_mul_finite_of_mem_mul {B M : Type*} [comm_semiring B] [semiring M]
  [algebra B M] {P Q : submodule B M} {x : M} (hx : x ∈ P * Q) :
  ∃ (T T' : finset M), (T : set M) ⊆ P ∧ (T' : set M) ⊆ Q ∧ x ∈ span B (T * T' : set M) :=
submodule.mem_span_mul_finite_of_mem_span_mul
  (by rwa [← submodule.span_eq P, ← submodule.span_eq Q, submodule.span_mul_span] at hx)

variables {K} {f : fraction_map A K}

@[simp, norm_cast]
lemma coe_ideal_le_coe_ideal {I J : ideal A} :
  (I : fractional_ideal f) ≤ (J : fractional_ideal f) ↔ I ≤ J :=
begin
  split,
  { intros h x hI,
    rw le_iff_mem at h,
    specialize h (f.to_map x),
    simp only [exists_prop, mem_coe_ideal, exists_mem_to_map_eq] at h,
    exact h hI },
  { rintros h x hx,
    simp only [val_eq_coe, coe_coe_ideal, localization_map.mem_coe_submodule] at hx ⊢,
    obtain ⟨y, hy, y_eq⟩ := hx,
    exact ⟨y, h hy, y_eq⟩ },
end

lemma mem_coe' {S : submonoid R} {P : Type*} [comm_ring P]
  (f : localization_map S P) (I : fractional_ideal f) (x : f.codomain) :
  x ∈ (I : submodule R f.codomain) ↔ x ∈ I := iff.rfl

lemma fg_of_one_mem_span_mul (s : ideal A) (h2 : (s * (1 / s) : fractional_ideal f) = 1)
  (T T' : finset f.codomain)
  (hT : (T : set f.codomain) ⊆ (s : fractional_ideal f))
  (hT' : (T' : set f.codomain) ⊆ ↑(1 / (s : fractional_ideal f)))
  (one_mem : (1 : f.codomain) ∈ span A (T * T' : set f.codomain)) :
  s.fg :=
begin
  apply fg_of_fg_map f.lin_coe (linear_map.ker_eq_bot.mpr f.injective),
  refine ⟨T, _⟩,
  apply le_antisymm,
  { intros x gx,
    simp only [localization_map.lin_coe_apply, submodule.mem_map],
    exact submodule.span_le.mpr hT gx },
  intros x gx,
  suffices f2 : span A ({x} * T' : set f.codomain) ≤ 1,
  { convert submodule.mul_le_mul_left f2 _,
    { exact (one_mul _).symm },
    rw [submodule.span_mul_span, mul_assoc, ← mul_one x, ← submodule.span_mul_span,
        mul_comm (T' : set f.codomain)]
      { occs := occurrences.pos [1] },
    exact submodule.mul_mem_mul (mem_span_singleton_self x) one_mem, },
  rw [← fractional_ideal.coe_one, ← h2, fractional_ideal.coe_mul, ← submodule.span_mul_span],
  apply submodule.mul_le_mul,
  { rwa [submodule.span_le, set.singleton_subset_iff] },
  { rwa submodule.span_le },
end

lemma is_noetherian_of_is_dedekind_domain_inv : is_dedekind_domain_inv A → is_noetherian_ring A :=
begin
  rintros ⟨h1, h2⟩,
  refine ⟨λ s, _⟩,
  by_cases h : s = ⊥,
  { rw h, apply submodule.fg_bot },

  have : (1 : fraction_ring A) ∈ (1 : fractional_ideal (fraction_ring.of A)) := one_mem_one,
  have h := (coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr h,
  rw [← h2 _ h, ← mem_coe', fractional_ideal.coe_mul] at this,
  obtain ⟨T, T', hT, hT', one_mem⟩ := submodule.mem_span_mul_finite_of_mem_mul this,
  exact fg_of_one_mem_span_mul s (h2 _ h) T T' hT hT' one_mem,
end

/-- `A[x]` is a fractional ideal for every `x` in the codomain of the fraction map `f`. -/
lemma is_fractional_adjoin_integral (x : f.codomain) (hx : is_integral A x) :
  is_fractional f (↑(algebra.adjoin A ({x} : set f.codomain)) : submodule A f.codomain) :=
is_fractional_of_fg (fg_adjoin_singleton_of_integral x hx)

lemma mem_adjoin_self (x : f.codomain) :
  x ∈ ((algebra.adjoin A {x}) : subalgebra A f.codomain) :=
algebra.subset_adjoin (set.mem_singleton x)

lemma int_closed_of_is_dedekind_domain_inv :
  is_dedekind_domain_inv A → integral_closure A (fraction_ring A) = ⊥ :=
begin
  rintros ⟨h1, h2⟩,
  rw eq_bot_iff,
  rintros x hx,
  set M : fractional_ideal (fraction_ring.of A) := ⟨_, is_fractional_adjoin_integral _ hx⟩ with h1M,
  have fx : x ∈ M := mem_adjoin_self x,
  by_cases h : x = 0,
  { rw h, apply subalgebra.zero_mem _ },
  have mul_self : M * M = M,
  { rw subtype.ext_iff_val,
    simp },
  have eq_one : M = 1,
  { have g : M ≠ ⊥,
    { intro a,
      rw [fractional_ideal.bot_eq_zero, ← fractional_ideal.ext_iff] at a,
      exact h (mem_zero_iff.mp ((a x).mp fx)) },
    have h2 : M * (1 / M) = 1 := h2 _ g,
    convert congr_arg (* (1 / M)) mul_self;
      simp only [mul_assoc, h2, mul_one] },
  show x ∈ ((⊥ : subalgebra A (localization_map.codomain (fraction_ring.of A))) :
    submodule A (localization_map.codomain (fraction_ring.of A))),
  rwa [algebra.to_submodule_bot, ← coe_span_singleton 1, fractional_ideal.span_singleton_one,
       ← eq_one],
end

lemma dim_le_one_of_is_dedekind_domain_inv : is_dedekind_domain_inv A → dimension_le_one A :=
begin
  have coe_ne_bot : ∀ {I : ideal A}, I ≠ ⊥ → (I : fractional_ideal (fraction_ring.of A)) ≠ 0 :=
  λ I, (coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr,
  rintros h,
  rcases h with ⟨h1, h2⟩,
  rintros p hpz hp,
  set p' : fractional_ideal (fraction_ring.of A) := p with p'_eq,
  have hpinv := h2 p' (coe_ne_bot hpz),

  -- We're going to show that `p` is maximal because any maximal ideal `M`
  -- that is strictly larger would be `⊤`.
  obtain ⟨M, hM1, hM2⟩ := exists_le_maximal p hp.1,
  set M' : fractional_ideal (fraction_ring.of A) := M with M'_eq,
  have M'_ne := coe_ne_bot (ne_bot_of_is_maximal_of_not_is_field hM1 h1),
  have hMinv := h2 M' M'_ne,
  convert hM1,
  by_contra h,
  apply hM1.1,
  rw [eq_top_iff, ← @coe_ideal_le_coe_ideal _ _ _ _ (fraction_ring.of A), ← ideal.one_eq_top],
  show 1 ≤ M',
  suffices g : M'⁻¹ * p' ≤ p',
  { have : M' * ((M'⁻¹ * p') * p'⁻¹) ≤ M' * (p' * p'⁻¹) :=
      mul_left_mono M' (mul_right_mono p'⁻¹ g),
    rwa [mul_assoc, hpinv, mul_one, hMinv, mul_one] at this },

  -- Suppose we have `x ∈ M'⁻¹ * p'`, then in fact `x = fraction_ring.of A y` for some `y`.
  rintros x hx,
  have le_one : M'⁻¹ * p ≤ 1,
  { have g'' := fractional_ideal.mul_right_mono M'⁻¹ (coe_ideal_le_coe_ideal.mpr hM2),
    simpa only [val_eq_coe, ← coe_mul, hMinv, mul_comm M'⁻¹ p'] using g'' },
  obtain ⟨y, hy, rfl⟩ := mem_coe_ideal.mp (le_one hx),

  -- Since `M` is maximal and not equal to `p`, let `z ∈ M \ p`.
  obtain ⟨z, hzM, hzp⟩ := exists_of_lt (lt_of_le_of_ne hM2 h),
  -- If `z * y ∈ p` (or `fraction_ring.of A (z * y) ∈ p'`) we are done,
  -- since `p` is prime and `z ∉ p`.
  suffices zy_mem : (fraction_ring.of A).to_map (z * y) ∈ p',
  { obtain ⟨zy, hzy, zy_eq⟩ := mem_coe_ideal.mp zy_mem,
    rw (fraction_ring.of A).injective zy_eq at hzy,
    exact mem_coe_ideal.mpr ⟨_, or.resolve_left (hp.2 hzy) hzp, rfl⟩ },

  -- But `p' = M * M⁻¹ * p`, so `z ∈ M` and `y ∈ M⁻¹ * p` and we get our conclusion.
    rw [ring_hom.map_mul],
    convert fractional_ideal.mul_mem_mul
      (show (fraction_ring.of A).to_map z ∈ M', from mem_coe_ideal.mpr ⟨_, hzM, rfl⟩)
      hx,
    rw [← mul_assoc, hMinv, one_mul]
end

/-- Showing one side of the equivalence between the definitions
`is_dedekind_domain_inv` and `is_dedekind_domain` of Dedekind domains. -/
theorem is_dedekind_domain_of_is_dedekind_domain_inv :
  is_dedekind_domain_inv A → is_dedekind_domain A :=
λ h,
  ⟨ h.1,
  is_noetherian_of_is_dedekind_domain_inv h,
  dim_le_one_of_is_dedekind_domain_inv h,
  int_closed_of_is_dedekind_domain_inv h⟩

end
