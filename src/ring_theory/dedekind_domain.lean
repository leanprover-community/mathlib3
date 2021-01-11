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
import ring_theory.power_basis
import ring_theory.trace
import set_theory.cardinal
import tactic

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

section

variables {A K}

lemma fraction_map.is_algebraic_iff {R L : Type*} [integral_domain R] [field L]
  (f : fraction_map R K) [algebra f.codomain L] [algebra R L] [is_scalar_tower R f.codomain L]
  {x : L} : is_algebraic f.codomain x ↔ is_algebraic R x :=
begin
  split,
  { rintro ⟨p, p_ne, p_eq⟩,
    exact ⟨f.integer_normalization p,
           mt f.integer_normalization_eq_zero_iff.mp p_ne,
           localization_map.integer_normalization_aeval_eq_zero p p_eq⟩ },
  { rintro ⟨p, p_ne, p_eq⟩,
    refine ⟨p.map f.to_map, _, _⟩,
    { simpa only [ne.def, polynomial.ext_iff, polynomial.coeff_zero, polynomial.coeff_map,
                  f.to_map_eq_zero_iff]
        using p_ne },
    { simpa only [polynomial.aeval_def, polynomial.eval₂_map, ← f.algebra_map_eq,
                  is_scalar_tower.algebra_map_eq R f.codomain L]
        using p_eq } },
end

end

open ring

/--
A Dedekind domain is an integral domain that is Noetherian, integrally closed, and
has Krull dimension at most one.

The integral closure condition is independent of the choice of field of fractions:
use `is_dedekind_domain_iff` to prove `is_dedekind_domain` for a given `fraction_map`.

This is the default implementation, but there are equivalent definitions,
`is_dedekind_domain_dvr` and `is_dedekind_domain_inv`.
TODO: Prove that these are actually equivalent definitions.
-/
class is_dedekind_domain : Prop :=
(to_is_noetherian_ring : is_noetherian_ring A)
(dimension_le_one : dimension_le_one A)
(is_integrally_closed : integral_closure A (fraction_ring A) = ⊥)

attribute [instance, priority 100] is_dedekind_domain.to_is_noetherian_ring -- see Note [lower instance priority]

/-- An integral domain is a Dedekind domain iff and only if it is not a field, is Noetherian, has dimension ≤ 1,
and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
lemma is_dedekind_domain_iff (f : fraction_map A K) :
  is_dedekind_domain A ↔
    is_noetherian_ring A ∧ dimension_le_one A ∧
    integral_closure A f.codomain = ⊥ :=
⟨λ ⟨hr, hd, hi⟩, ⟨hr, hd,
  by rw [←integral_closure_map_alg_equiv (fraction_ring.alg_equiv_of_quotient f),
         hi, algebra.map_bot]⟩,
 λ ⟨hr, hd, hi⟩, ⟨hr, hd,
  by rw [←integral_closure_map_alg_equiv (fraction_ring.alg_equiv_of_quotient f).symm,
         hi, algebra.map_bot]⟩⟩

/--
A Dedekind domain is an integral domain that is not a field, is Noetherian, and the localization at
every nonzero prime is a discrete valuation ring.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure is_dedekind_domain_dvr : Prop :=
(to_is_noetherian_ring : is_noetherian_ring A)
(is_dvr_at_nonzero_prime : ∀ P ≠ (⊥ : ideal A), P.is_prime →
  discrete_valuation_ring (localization.at_prime P))

section inverse

open_locale classical

variables {R₁ : Type*} [integral_domain R₁] {g : fraction_map R₁ K}


variables {I J : fractional_ideal g}

noncomputable instance : has_inv (fractional_ideal g) := ⟨λ I, 1 / I⟩

lemma inv_eq : I⁻¹ = 1 / I := rfl

lemma inv_zero' : (0 : fractional_ideal g)⁻¹ = 0 := fractional_ideal.div_zero

lemma inv_nonzero {J : fractional_ideal g} (h : J ≠ 0) :
J⁻¹ = ⟨(1 : fractional_ideal g) / J, fractional_ideal.fractional_div_of_nonzero h⟩ :=
fractional_ideal.div_nonzero _

lemma coe_inv_of_nonzero {J : fractional_ideal g} (h : J ≠ 0) :
  (↑J⁻¹ : submodule R₁ g.codomain) = g.coe_submodule 1 / J :=
by { rwa inv_nonzero _, refl, assumption}

/-- `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
theorem right_inverse_eq (I J : fractional_ideal g) (h : I * J = 1) :
  J = I⁻¹ :=
begin
  have hI : I ≠ 0 := fractional_ideal.ne_zero_of_mul_eq_one I J h,
  suffices h' : I * (1 / I) = 1,
  { exact (congr_arg units.inv $
      @units.ext _ _ (units.mk_of_mul_eq_one _ _ h) (units.mk_of_mul_eq_one _ _ h') rfl) },
  apply le_antisymm,
  { apply fractional_ideal.mul_le.mpr _,
    intros x hx y hy,
    rw mul_comm,
    exact (fractional_ideal.mem_div_iff_of_nonzero hI).mp hy x hx },
  rw ← h,
  apply fractional_ideal.mul_left_mono I,
  apply (fractional_ideal.le_div_iff_of_nonzero hI).mpr _,
  intros y hy x hx,
  rw mul_comm,
  exact fractional_ideal.mul_mem_mul hx hy
end

theorem mul_inv_cancel_iff {I : fractional_ideal g} :
  I * I⁻¹ = 1 ↔ ∃ J, I * J = 1 :=
⟨λ h, ⟨I⁻¹, h⟩, λ ⟨J, hJ⟩, by rwa [← @right_inverse_eq _ _ _ _ _ I J hJ]⟩

variables {K' : Type*} [field K'] {g' : fraction_map R₁ K'}

@[simp] lemma map_inv (I : fractional_ideal g) (h : g.codomain ≃ₐ[R₁] g'.codomain) :
  (I⁻¹).map (h : g.codomain →ₐ[R₁] g'.codomain) = (I.map h)⁻¹ :=
by rw [inv_eq, fractional_ideal.map_div, fractional_ideal.map_one, inv_eq]

open_locale classical

open submodule submodule.is_principal

@[simp] lemma span_singleton_inv (x : g.codomain) :
  (fractional_ideal.span_singleton x)⁻¹ = fractional_ideal.span_singleton (x⁻¹) :=
fractional_ideal.one_div_span_singleton x

local attribute [semireducible] fractional_ideal.span_singleton

lemma mul_generator_self_inv (I : fractional_ideal g)
  [submodule.is_principal (I : submodule R₁ g.codomain)] (h : I ≠ 0) :
  I * fractional_ideal.span_singleton (generator (I : submodule R₁ g.codomain))⁻¹ = 1 :=
begin
  -- Rewrite only the `I` that appears alone.
  conv_lhs { congr, rw fractional_ideal.eq_span_singleton_of_principal I },
  rw [fractional_ideal.span_singleton_mul_span_singleton, mul_inv_cancel,
    fractional_ideal.span_singleton_one],
  intro generator_I_eq_zero,
  apply h,
  rw [fractional_ideal.eq_span_singleton_of_principal I, generator_I_eq_zero,
    fractional_ideal.span_singleton_zero]
end

lemma invertible_of_principal (I : fractional_ideal g)
  [submodule.is_principal (I : submodule R₁ g.codomain)] (h : I ≠ 0) :
  I * I⁻¹ = 1 :=
(fractional_ideal.mul_div_self_cancel_iff).mpr
  ⟨fractional_ideal.span_singleton (generator (I : submodule R₁ g.codomain))⁻¹,
    @mul_generator_self_inv _ _ _ _ _ I _ h⟩

lemma invertible_iff_generator_nonzero (I : fractional_ideal g)
  [submodule.is_principal (I : submodule R₁ g.codomain)] :
  I * I⁻¹ = 1 ↔ generator (I : submodule R₁ g.codomain) ≠ 0 :=
begin
  split,
  { intros hI hg,
    apply fractional_ideal.ne_zero_of_mul_eq_one _ _ hI,
    rw [fractional_ideal.eq_span_singleton_of_principal I, hg,
        fractional_ideal.span_singleton_zero] },
  { intro hg,
    apply invertible_of_principal,
    rw [fractional_ideal.eq_span_singleton_of_principal I],
    intro hI,
    have := fractional_ideal.mem_span_singleton_self (generator (I : submodule R₁ g.codomain)),
    rw [hI, fractional_ideal.mem_zero_iff] at this,
    contradiction }
end

lemma is_principal_inv (I : fractional_ideal g)
  [submodule.is_principal (I : submodule R₁ g.codomain)] (h : I ≠ 0) :
  submodule.is_principal (I⁻¹).1 :=
begin
  rw [fractional_ideal.val_eq_coe, fractional_ideal.is_principal_iff],
  use (generator (I : submodule R₁ g.codomain))⁻¹,
  have hI : I  * fractional_ideal.span_singleton ((generator (I : submodule R₁ g.codomain))⁻¹)  = 1,
  apply @mul_generator_self_inv _ _ _ _ _ I _ h,
  apply (@right_inverse_eq _ _ _ _ _ I (fractional_ideal.span_singleton ((generator (I : submodule R₁ g.codomain))⁻¹)) hI).symm,
end

/--
A Dedekind domain is an integral domain that is not a field such that every fractional ideal has an inverse.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
def is_dedekind_domain_inv : Prop :=
∀ I ≠ (⊥ : fractional_ideal (fraction_ring.of A)), I * (1 / I) = 1

open ring.fractional_ideal

lemma is_dedekind_domain_inv_iff (f : fraction_map A K) :
  is_dedekind_domain_inv A ↔
    (∀ I ≠ (⊥ : fractional_ideal f), I * I⁻¹ = 1) :=
begin
  set h : (fraction_ring.of A).codomain ≃ₐ[A] f.codomain := fraction_ring.alg_equiv_of_quotient f,
  split; intro hi; intros I hI,
  { have := hi (map ↑h.symm I) (map_ne_zero _ hI),
    convert congr_arg (map (h : (fraction_ring.of A).codomain →ₐ[A] f.codomain)) this;
      simp only [map_symm_map, map_one, fractional_ideal.map_mul, fractional_ideal.map_div,
                 inv_eq] },
  { have := hi (map ↑h I) (map_ne_zero _ hI),
    convert congr_arg (map (h.symm : f.codomain →ₐ[A] (fraction_ring.of A).codomain)) this;
      simp only [map_map_symm, map_one, fractional_ideal.map_mul, fractional_ideal.map_div,
                 inv_eq] },
end
end inverse

section equivalence

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

lemma mem_coe' {R : Type*} [comm_ring R] {S : submonoid R} {P : Type*} [comm_ring P]
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
  intro h2,
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
  intro h2,
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

lemma is_field.is_principal_ideal_ring (h : is_field A) : is_principal_ideal_ring A :=
@euclidean_domain.to_principal_ideal_domain A (@field.to_euclidean_domain A (h.to_field A))

lemma dim_le_one_of_is_dedekind_domain_inv : is_dedekind_domain_inv A → dimension_le_one A :=
begin
  have coe_ne_bot : ∀ {I : ideal A}, I ≠ ⊥ → (I : fractional_ideal (fraction_ring.of A)) ≠ 0 :=
  λ I, (coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr,

  rintros h2,

  -- If A is a field, we're done.
  by_cases h1 : is_field A,
  { haveI : is_principal_ideal_ring A := is_field.is_principal_ideal_ring h1,
    apply dimension_le_one.principal_ideal_ring },

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
  suffices g : (1 / M') * p' ≤ p',
  { have : M' * (((1 / M') * p') * (1 / p')) ≤ M' * (p' * (1 / p')) :=
      mul_left_mono M' (mul_right_mono p'⁻¹ g),
    rwa [mul_assoc, hpinv, mul_one, hMinv, mul_one] at this },

  -- Suppose we have `x ∈ M'⁻¹ * p'`, then in fact `x = fraction_ring.of A y` for some `y`.
  rintros x hx,
  have le_one : (1 / M') * p ≤ 1,
  { have g'' := fractional_ideal.mul_right_mono (1 / M') (coe_ideal_le_coe_ideal.mpr hM2),
    simpa only [val_eq_coe, ← coe_mul, hMinv, mul_comm (1 / M') p'] using g'' },
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
  ⟨is_noetherian_of_is_dedekind_domain_inv h,
  dim_le_one_of_is_dedekind_domain_inv h,
  int_closed_of_is_dedekind_domain_inv h⟩

end

lemma integrally_closed_iff_integral_implies_integer {R K : Type*}
  [comm_ring R] [comm_ring K] {f : fraction_map R K} :
  integral_closure R f.codomain = ⊥ ↔ ∀ x : f.codomain, is_integral R x → f.is_integer x :=
subalgebra.ext_iff.trans
  ⟨ λ h x hx, algebra.mem_bot.mp ((h x).mp hx),
    λ h x, iff.trans
      ⟨λ hx, h x hx, λ ⟨y, hy⟩, hy ▸ is_integral_algebra_map⟩
      (@algebra.mem_bot R f.codomain _ _ _ _).symm⟩

@[priority 100] -- see Note [lower instance priority]
instance principal_ideal_ring.to_dedekind_domain [is_principal_ideal_ring A] : is_dedekind_domain A :=
⟨principal_ideal_ring.is_noetherian_ring, dimension_le_one.principal_ideal_ring _,
  @unique_factorization_monoid.integrally_closed A _ _
    (principal_ideal_ring.to_unique_factorization_monoid) _ (fraction_ring.of A)⟩

namespace is_dedekind_domain

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
  { haveI : is_noetherian_ring R := hR.1,
    apply fractional_ideal.is_noetherian IA },
  obtain ⟨px, h_px , h_int_x⟩ : is_integral R x,
  { apply @is_integral_of_submodule_noetherian R K _ _ h_RalgK A h_noethA x h_xA },
  use px,
  apply and.intro h_px h_int_x,
end

local attribute [instance] classical.prop_decidable

lemma inv_of_maximal_not_top (hR : is_dedekind_domain R) (hNF : ¬ is_field R)
  (hM : ideal.is_maximal M) : (1 / ↑M : fractional_ideal f) ≠ (1 : fractional_ideal f) :=
begin
  obtain ⟨a, h_nza⟩ : ∃ a : M, a ≠ 0,
  { have h_nzM : M ≠ ⊥,
    apply ne_bot_of_is_maximal_of_not_is_field hM hNF,
    apply submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr h_nzM) },
  let J : (ideal R) := ideal.span {a},
  have J_nz : J ≠ ⊥ ∧ J ≤ M,
  simp only [*, span_singleton_eq_bot, ne.def, not_false_iff, submodule.coe_eq_zero, span_le,
    submodule.mem_coe, submodule.coe_mem, set.singleton_subset_iff, and_self],
  obtain ⟨Z, h_ZJ,h_nzJ⟩ : ∃ (Z : multiset (prime_spectrum R)), multiset.prod (Z.map (coe : subtype _ → ideal R)) ≤ J ∧
    multiset.prod (Z.map (coe : subtype _ → ideal R)) ≠ ⊥,
  apply exists_prime_spectrum_prod_le_and_ne_bot_of_domain hNF J_nz.left,
  obtain ⟨P, h_ZP, h_JP⟩ : ∃ P : (prime_spectrum R), P ∈ Z ∧ P.1 ≤ J, sorry,
  replace h_JP : P.1 ≤ M, sorry,--facile, J_nz dà J ≤ M e abbiamo P.1 ≤ J,
  replace h_JP : P.1 = M, sorry,
  -- apply is_maximal.eq_of_le,
  obtain ⟨Z', h_Z'Z, h_Z'P⟩ : ∃ Z' ≤ Z, Z = P ::ₘ Z', sorry,
  let J' : ideal R := multiset.prod (Z'.map (coe : subtype _ → ideal R)),
  have h_MJJ' : M * J' ≤ J, sorry,
  have h_JJ' : ¬ J' ≤ J, sorry,
  obtain ⟨b, h_bJ', h_bJ⟩ : ∃ b : R, b ∈ J' ∧ b ∉ J, sorry,
  have h_fin : (M : fractional_ideal f) * (fractional_ideal.span_singleton (f.to_map a)⁻¹) *
    (fractional_ideal.span_singleton (f.to_map b)) ≤ (1 : fractional_ideal f), sorry,
  replace h_fin : (f.to_map b) * (f.to_map a)⁻¹ ∈ (1 / ↑M : fractional_ideal f), sorry,
  have h_ab : (f.to_map b) * (f.to_map a)⁻¹ ∉ (1 : fractional_ideal f), sorry,
  sorry,
end

lemma maximal_ideal_inv_of_dedekind (hR : is_dedekind_domain R) (hNF : ¬ is_field R)
  (hM : ideal.is_maximal M) :
  is_unit (M : fractional_ideal f) :=
begin
  have hnz_M : M ≠ 0, apply (lt_iff_le_and_ne.mp (ideal.bot_lt_of_maximal M hNF) ).2.symm,
  have hnz_Mf : (↑M : fractional_ideal f) ≠ (⊥ : fractional_ideal f),
  { exact (fractional_ideal.coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors R))).mpr hnz_M },
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
         { rw ← ((is_dedekind_domain_iff _ _ f).mp hR).right.right, exact h_intxR },
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
  I * (1 / I) = 1 :=
begin
  sorry
end

lemma mul_one_div (h : is_dedekind_domain R) {I J : fractional_ideal f} : I * (1 / J) = I / J :=
sorry

noncomputable instance [h : is_dedekind_domain R] : comm_group_with_zero (fractional_ideal f) :=
{ inv := λ I, 1 / I,
  div := λ I J, I / J,
  div_eq_mul_inv := λ I J, by rw [inv_eq, mul_one_div _ h],
  inv_zero := fractional_ideal.div_zero,
  mul_inv_cancel := λ I hI, by rw [inv_eq, fractional_ideal_invertible_of_dedekind _ h I],
  .. fractional_ideal.nontrivial,
  .. fractional_ideal.comm_semiring }

open_locale big_operators

variables {K}

lemma integral_closure_le_span [algebra f.codomain L] [algebra R L] [is_scalar_tower R f.codomain L]
  [is_separable (localization_map.codomain f) L]
  {ι : Type*} [fintype ι] {b : ι → L} (hb : is_basis f.codomain b)
  (hb_int : ∀ i, is_integral R (b i)) (int_cl : integral_closure R f.codomain = ⊥) :
  (integral_closure R L : submodule R L) ≤ submodule.span R (set.range (dual_basis hb)) :=
begin
  rintros x (hx : is_integral R x),
  suffices : ∃ (c : ι → R), x = ∑ i, c i • dual_basis hb i,
  { obtain ⟨c, rfl⟩ := this,
    refine submodule.sum_mem _ (λ i _, submodule.smul_mem _ _ (submodule.subset_span _)),
    rw set.mem_range,
    exact ⟨i, rfl⟩ },
  suffices : ∃ (c : ι → f.codomain), ((∀ i, is_integral R (c i)) ∧ x = ∑ i, c i • dual_basis hb i),
  { obtain ⟨c, hc, hx⟩ := this,
    have hc' := λ i, (integrally_closed_iff_integral_implies_integer.mp int_cl (c i) (hc i)),
    use λ i, classical.some (hc' i),
    refine hx.trans (finset.sum_congr rfl (λ i _, _)),
    conv_lhs { rw [← classical.some_spec (hc' i)] },
    rw [← is_scalar_tower.algebra_map_smul f.codomain (classical.some (hc' i)) (dual_basis hb i),
        f.algebra_map_eq] },
  refine ⟨λ i, (is_basis_dual_basis hb).repr x i, (λ i, _), (sum_repr _ _).symm⟩,
  rw ← trace_gen_pow_mul,
  haveI : finite_dimensional f.codomain L := finite_dimensional.of_fintype_basis hb,
  exact is_integral_trace (is_integral_mul (hb_int i) hx)
end

lemma is_noetherian_of_le [algebra R L] {s t : submodule R L}
  (ht : is_noetherian R t) (h : s ≤ t):
  is_noetherian R s :=
is_noetherian_submodule.mpr (λ s' hs', is_noetherian_submodule.mp ht _ (le_trans hs' h))

lemma is_noetherian_adjoin_finset [is_noetherian_ring R] [algebra R L] (s : finset L)
  (hs : ∀ x ∈ s, is_integral R x) :
  is_noetherian R (algebra.adjoin R (↑s : set L)) :=
is_noetherian_of_fg_of_noetherian _ (fg_adjoin_of_finite s.finite_to_set hs)

/-- Send a set of `x`'es in a finite extension `L` of the fraction field of `R` to `(y : R) • x ∈ integral_closure R L`. -/
lemma exists_integral_multiples (f : fraction_map R K)
  [algebra f.codomain L] [algebra R L] [is_scalar_tower R f.codomain L]
  [finite_dimensional f.codomain L] (s : finset L) :
  ∃ (y ≠ (0 : R)), ∀ x ∈ s, is_integral R (y • x) :=
begin
  refine s.induction _ _,
  { use [1, one_ne_zero],
    rintros x ⟨⟩ },
  { rintros x s hx ⟨y, hy, hs⟩,
    obtain ⟨x', y', hy', hx'⟩ := exists_integral_multiple
      (f.is_algebraic_iff.mp (algebra.is_algebraic_of_finite x))
      _,
    use [y * y', mul_ne_zero hy hy'],
    intros x'' hx'',
    rcases finset.mem_insert.mp hx'' with (rfl | hx''),
    { rw [mul_smul, hx', algebra.smul_def],
      exact is_integral_mul is_integral_algebra_map x'.2 },
    { rw [mul_comm, mul_smul, algebra.smul_def],
      exact is_integral_mul is_integral_algebra_map (hs _ hx'') },
    { rw is_scalar_tower.algebra_map_eq R f.codomain L,
      apply (algebra_map f.codomain L).injective.comp,
      rw f.algebra_map_eq,
      exact f.injective } }
end

/-- If `x` in a field `L` is not zero, then multiplying in `L` by `x` is a linear equivalence. -/
def lsmul_equiv [algebra R L] {x : R} (hx : algebra_map R L x ≠ 0) : L ≃ₗ[R] L :=
{ inv_fun := λ y, (algebra_map R L x)⁻¹ * y,
  left_inv := λ y, by simp only [linear_map.to_fun_eq_coe, algebra.lmul_apply, ← mul_assoc, inv_mul_cancel hx, one_mul],
  right_inv := λ y, by simp only [linear_map.to_fun_eq_coe, algebra.lmul_apply, ← mul_assoc, mul_inv_cancel hx, one_mul],
  .. algebra.lmul R L (algebra_map R L x) }

@[simp] lemma lsmul_equiv_apply [algebra R L] {x : R} (hx : algebra_map R L x ≠ 0)  (y : L) :
  lsmul_equiv hx y = x • y := (algebra.smul_def x y).symm

section

variables {K} (f L)

lemma exists_is_basis_integral
  [algebra f.codomain L] [algebra R L] [is_scalar_tower R f.codomain L]
  [finite_dimensional f.codomain L] :
  ∃ (s : finset L) (b : (↑s : set L) → L),
    is_basis f.codomain b ∧
    (∀ x, is_integral R (b x)) :=
let ⟨s', hbs'⟩ := finite_dimensional.exists_is_basis_finset f.codomain L,
    ⟨y, hy, his'⟩ := exists_integral_multiples f s' in
have hy' : algebra_map f.codomain L (algebra_map R f.codomain y) ≠ 0 :=
  by {
    apply mt (λ h, _) hy,
    apply f.to_map.injective_iff.mp f.injective,
    apply (algebra_map f.codomain L).injective_iff.mp (algebra_map f.codomain L).injective,
    exact h },
⟨s',
  _,
  (lsmul_equiv hy').is_basis hbs',
 by { rintros ⟨x', hx'⟩, simp only [function.comp, lsmul_equiv_apply, is_scalar_tower.algebra_map_smul],
      exact his' x' hx' }⟩

end

lemma integral_closure.is_noetherian_ring [is_noetherian_ring R]
  [algebra f.codomain L] [algebra R L] [is_scalar_tower R f.codomain L]
  [finite_dimensional f.codomain L] [is_separable (localization_map.codomain f) L]
  (int_cl : integral_closure R f.codomain = ⊥) :
  is_noetherian_ring (integral_closure R L) :=
let ⟨s, b, hb, hb_int⟩ := exists_is_basis_integral L f in
is_noetherian_of_is_scalar_tower _ (is_noetherian_of_le
  (is_noetherian_span_of_finite _ (set.finite_range _))
  (integral_closure_le_span hb (λ x, hb_int x) int_cl))

variables (f)

/- If L is a finite extension of R's fraction field, the integral closure of R in L is a Dedekind domain. -/
protected lemma integral_closure [algebra f.codomain L] [algebra R L] [is_scalar_tower R f.codomain L]
  [finite_dimensional f.codomain L] [is_separable f.codomain L]
  (h : is_dedekind_domain R) :
  is_dedekind_domain (integral_closure R L) :=
(is_dedekind_domain_iff _ _ (integral_closure.fraction_map_of_finite_extension L f)).mpr
⟨integral_closure.is_noetherian_ring ((is_dedekind_domain_iff _ _ f).mp h).2.2,
 h.dimension_le_one.integral_closure _ _,
 integral_closure_idem⟩

instance [algebra (fraction_ring.of R).codomain L] [algebra R L] [is_scalar_tower R (fraction_ring.of R).codomain L]
  [finite_dimensional (fraction_ring.of R).codomain L] [is_separable (fraction_ring.of R).codomain L]
  [h : is_dedekind_domain R] :
  is_dedekind_domain (integral_closure R L) :=
is_dedekind_domain.integral_closure (fraction_ring.of R) h

end is_dedekind_domain

end equivalence
