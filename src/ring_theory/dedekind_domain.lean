/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import linear_algebra.finite_dimensional
import order.zorn
import ring_theory.discrete_valuation_ring
import ring_theory.fractional_ideal
import ring_theory.ideal.over
import ring_theory.fractional_ideal
import ring_theory.polynomial.rational_root
import ring_theory.ideal.over
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
variables {L : Type*} [field K] [field L] {f : fraction_map R K}

open finsupp polynomial

-- lemma smul_mul (a₁ a₂ : α) (b : β) : b • (a₁ * a₂) = b * a₁ * a₂ :=
-- by sorry,
--may be, use smul_eq_mul of modules/basic.lean?

lemma smul_mul (a₁ a₂ : f.codomain) (b : R) : b • (a₁ * a₂) = f.to_map b * a₁ * a₂ :=
begin
sorry,
end

variables {M : ideal R} [is_maximal M]

lemma if_inv_then_int {I : ideal R} (x : f.codomain) (h_I : I ≠ 0) (h : (1 / ↑I : fractional_ideal f) * ↑I = ↑I) :
x ∈ (1/↑I : fractional_ideal f).val → f.is_integer x :=
begin
  -- sorry,
have h_powx_M : ∀ (n : ℕ), (ring.fractional_ideal.span_singleton x^n ) • (↑I : fractional_ideal f) ≤ (↑I : fractional_ideal f),
intro, induction n with n hn,
  {have h_Id : ↑ I = ↑ I, triv,
  simp, apply eq.le h_Id,
  },
  {intros a ha,sorry,
  },
intro x,
end

local attribute [instance] classical.prop_decidable

lemma maximal_ideal_inv_of_dedekind
  (h : is_dedekind_domain R) (hM : ideal.is_maximal M)
  (hnz_M : M ≠ 0) -- this is now superfluous as by def'n DD are not fields
  : is_unit (M : fractional_ideal f) :=
begin
   have hnz_Mf : (↑ M : fractional_ideal f) ≠ (0 : fractional_ideal f),
    apply fractional_ideal.coe_nonzero_of_nonzero.mp hnz_M,
  have hnz_invMf : (1 : fractional_ideal f)/(↑ M : fractional_ideal f) ≠ (0 : fractional_ideal f),
    apply fractional_ideal.nonzero_inv_of_nonzero hnz_Mf,
  have hnz_invinvMf : (1 : fractional_ideal f)/((1 : fractional_ideal f)/(↑ M : fractional_ideal f)) ≠ (0 : fractional_ideal f),
    apply fractional_ideal.nonzero_inv_of_nonzero hnz_invMf,
  have h_MfinR : ↑M≤ (1:fractional_ideal f), apply fractional_ideal.coe_ideal_le_one,
  have hM_inclMinv : (↑ M : fractional_ideal f) ≤ (↑ M : fractional_ideal f)*(1/↑ M : fractional_ideal f),
  rw ← fractional_ideal.div_mul_inv,apply (fractional_ideal.le_div_iff_mul_le hnz_Mf).mpr (fractional_ideal.mul_self_le_self h_MfinR),exact hnz_Mf,
  have h_self : (↑ M : fractional_ideal f)≤ (1: fractional_ideal f)*↑ M,
  simp,exact le_refl ↑ M,
  have hMMinv_inclR : ↑ M * (1/↑ M) ≤ (1 : fractional_ideal f),
   rw ← fractional_ideal.inv_inv hnz_Mf at h_self {occs := occurrences.pos [2]},
   rw ← fractional_ideal.div_mul_inv at h_self,
   apply (@fractional_ideal.le_div_iff_mul_le _ _ _ _ _  ( ↑ M : fractional_ideal f) ( 1 : fractional_ideal f ) (( 1 : fractional_ideal f )/↑ M : fractional_ideal f) hnz_invMf).mp,
   exact h_self,  exact hnz_invMf,
  suffices hprod : ↑M*((1: fractional_ideal f)/↑M)=(1: fractional_ideal f),
  apply is_unit_of_mul_eq_one ↑M ((1: fractional_ideal f)/↑M) hprod,
      --now comes the 'hard' part: showing that M*(1/M)≤ 1 implies M*(1/M)=1 since M is max'l.
  have h_nonfrac : ∃ (I : ideal R), ↑ I=↑M*((1: fractional_ideal f)/↑M),
    ring,apply (fractional_ideal.le_one_iff_exists_coe_ideal.mp hMMinv_inclR),
    cases h_nonfrac with I hI,--could replace the above have and this cases by obtain?
  have h_Iincl : M ≤ I,
    {suffices h_Iincl_f : (↑M: fractional_ideal f) ≤ (↑I: fractional_ideal f),-- what follows is the proof that h_Iincl_f → h_Iincl
      intros x hx,
      let y := f.to_map x,
      have defy: f.to_map x =y,refl,
      have hy : y ∈  (↑ M : fractional_ideal f),simp,use x,exact ⟨hx,defy⟩,
      have hyI : y ∈  (↑ I : fractional_ideal f),
        apply fractional_ideal.le_iff.mp h_Iincl_f,exact hy,
      have hxyI : ∃ (x' ∈ I), f.to_map x' = y,
        apply fractional_ideal.mem_coe.mp hyI,
      rcases hxyI with ⟨a, ⟨ha, hfa⟩⟩,
      have hax : a=x,
        suffices haxf : f.to_map a=f.to_map x,apply fraction_map.injective f haxf,rw hfa,
      subst hax,exact ha,
      rw hI, exact hM_inclMinv,
    },
    have h_top : I= ⊤,
      {by_contradiction h_abs,
      have h_IM : M=I, apply is_maximal.eq_of_le hM h_abs h_Iincl,
      have h_inveqR : 1/↑ M = (1:fractional_ideal f),
        {suffices h_invR_dbl : 1/↑ M≤ (1:fractional_ideal f) ∧ (1:fractional_ideal f) ≤ 1/↑ M,
        apply (has_le.le.le_iff_eq h_invR_dbl.right).mp (h_invR_dbl.left),
        split,
          {intros x hx,--the proof that 1/M ≤ 1
          have h_MMinvI : (1 / ↑M : fractional_ideal f) * ↑M = ↑M),sorry,
          have h_intx : f.is_integer x, apply if_inv_then_int, exact hnz_M, exact h_MMinvI, exact hx,
          -- apply integrally_closed_iff_integral_implies_integer h.4,
          },
          {sorry,--the proof that 1≤ 1/M

          },
        },--end of the proof of h_inveqR

      },--end of the proof of h_top
    ----
    ----everything from here...
    ----
    -- have h_neqM : M ≠ I,--what Samuel does in his 2nd paragraph of Thm2 "mm'=m" is impossible
    -- {
    --   suffices h_invM_neqA : (1/↑ M) ≠ (1:fractional_ideal f),simp at ⊢,--what Samuel prives in his 3rd paragraph of Thm2
    --   by_contradiction ha,
    --   have h_invM_inclR : ∀ x ∈ (1/↑ M:fractional_ideal f), x ∈ (1:fractional_ideal f),
    --   intros x hx,
    --    {have h_xn : submodule.is_principal.span_singleton (x) * ↑M ≤ ↑ M,

    --    },
    -- },
    have h_Iincl_str : M < I, apply lt_of_le_of_ne h_Iincl h_neqM,
    have h_Itop : I=⊤, apply hM.right I h_Iincl_str,
  -- have h_Iincl_ss : ↑ M ⊆  I, apply submodule.span_le,
  --
  -- the following steps are
  -- 1) one_fI: 1 ∈ ↑I
  -- 2) one_I: 1 ∈ I
  -- 3) h_Itop: from 2)I=R
  --
  have one_fI : (1 : K) ∈ (↑I:fractional_ideal f),
    {have ex_nzM : ∃ y ∈ M, y ≠ (0 : R),sorry,
    rcases ex_nzM with ⟨ y , h_My , h_nzy ⟩,
    have h_invyinvM : (1/f.to_map y: K) ∈ (1:fractional_ideal f)/(↑ M:fractional_ideal f),sorry,
      -- rw hI,


    sorry},
  have one_I : (1 : R)∈ I,
   {have u1_I : ∃ (u ∈ (I: ideal R)), (f.to_map u) = (1: K),
    apply (fractional_ideal.mem_coe ).mp one_fI,
    rcases u1_I with ⟨v,hv,hfv⟩,
    have h_v1 : v=1,
    suffices h_v1f : f.to_map v=f.to_map 1, apply fraction_map.injective f h_v1f, rw hfv,
    apply (ring_hom.map_one f.to_ring_hom).symm,rw h_v1 at hv,exact hv,
   },
  have h_Itop' : I=⊤, --this (and its proof) should be replaced by h_Itop once that is OK
  apply (ideal.eq_top_iff_one I).mpr, exact one_I,
  ----
  ----up to here, must disappear...
  ----
  have h_okfI : ↑I=(1 : fractional_ideal f), apply fractional_ideal.ext_iff.mp,
    intros x,split,
      {intro hx,
      have h_x' : ∃ (x' ∈  (I : ideal R)), f.to_map x' = x,
      apply fractional_ideal.mem_coe.mp hx,
      apply fractional_ideal.mem_one_iff.mpr,simp * at *,
      },
      {intro hx,
      have h_x' : ∃ x' ∈ (1:ideal R),  f.to_map x' = x,
      apply fractional_ideal.mem_coe.mp hx,
      rw h_Itop',simp,
      rcases h_x' with ⟨a, ⟨ha,hfa⟩ ⟩,
            use a,exact hfa,
      },
    rw ← hI,exact h_okfI,
end


lemma fractional_ideal_invertible_of_dedekind (h : is_dedekind_domain R) (I : fractional_ideal f) :
  I * I⁻¹ = 1 :=
begin
  sorry
end

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
