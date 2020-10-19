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
import ring_theory.polynomial.rational_root
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
variables {L : Type*} [field L] {f : fraction_map R K}

#check fraction_ring R
#check Type u_3

open finsupp polynomial

-- lemma smul_mul (a₁ a₂ : α) (b : β) : b • (a₁ * a₂) = b * a₁ * a₂ :=
-- by sorry,
--may be, use smul_eq_mul of modules/basic.lean?

lemma smul_mul (a₁ a₂ : f.codomain) (b : R) : b • (a₁ * a₂) = f.to_map b * a₁ * a₂ :=
begin
sorry,
end

variables {M : ideal R} [is_maximal M]

theorem is_integral_of_noetherian' (B : Type*) [comm_ring B] [algebra R B] (A : subalgebra R B) (H : is_noetherian R A) (x : B) :
  (x ∈ A) → is_integral R x :=
  begin
sorry,
  end

lemma if_inv_then_int {I : ideal R} (x : f.codomain) (h_I : I ≠ 0) (h_prod : ↑I * (1 / ↑I : fractional_ideal f) = ↑I) :
x ∈ (1/↑I : fractional_ideal f).val → (f.to_map).is_integral_elem x :=
begin
let h_RalgK := (ring_hom.to_algebra f.to_map),
let φ := @aeval R K _ _ h_RalgK x,
let A := @alg_hom.range R (polynomial R) f.codomain _ _ _  _ h_RalgK φ,
have h_xA :  x ∈ A,--may be it is better to have hxn : ∀ (n : ℕ ), x^n ∈ A, (which is not much harder to prove)
  suffices hp : ∃ (p : polynomial R), φ p = x, simpa,
  use X, apply aeval_X,--if done for x^n rather than x, use aeval_X_pow rather than aeval_X
have h_fracA : is_fractional f A, sorry,
have h_A : is_noetherian R A, sorry,
obtain ⟨ _ , h_int_x ⟩ : is_integral R x,
apply @is_integral_of_noetherian' R _ K _ h_RalgK A h_A x h_xA,
cases h_int_x with px zero_px, intro h_xI,
end
/-
lemma if_inv_then_int {I : ideal R} (x : f.codomain) (h_I : I ≠ 0) (h : ↑I * (1 / ↑I : fractional_ideal f) = ↑I) :
x ∈ (1/↑I : fractional_ideal f).val → (f.to_map).is_integral_elem x :=
begin
have h_powx_M : ∀ (n : ℕ), (ring.fractional_ideal.span_singleton x^n ) • (↑I : fractional_ideal f) ≤ (↑I : fractional_ideal f),
intro, induction n with n hn,
  {have h_Id : ↑ I = ↑ I, triv,
   simp, apply eq.le h_Id,
  },
  {intros a ha,sorry,
  },
intro x,sorry,
end
-/


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
 rw ← fractional_ideal.div_mul_inv, apply (fractional_ideal.le_div_iff_mul_le hnz_Mf).mpr (fractional_ideal.mul_self_le_self h_MfinR),exact hnz_Mf,
have h_self : (↑ M : fractional_ideal f)≤ (1: fractional_ideal f)*↑ M,
 ring, exact le_refl ↑ M,
have hMMinv_inclR : ↑ M * (1/↑ M) ≤ (1 : fractional_ideal f),
  {rw ← fractional_ideal.inv_inv hnz_Mf at h_self {occs := occurrences.pos [2]},
   rw ← fractional_ideal.div_mul_inv at h_self,
   apply (@fractional_ideal.le_div_iff_mul_le _ _ _ _ _  ( ↑ M : fractional_ideal f) ( 1 : fractional_ideal f ) (( 1 : fractional_ideal f )/↑ M : fractional_ideal f) hnz_invMf).mp,
   exact h_self,  exact hnz_invMf,
  },
suffices hprod : ↑M*((1: fractional_ideal f)/↑M)=(1: fractional_ideal f),
 apply is_unit_of_mul_eq_one ↑M ((1: fractional_ideal f)/↑M) hprod,
obtain ⟨ I, hI ⟩ : ∃ (I : ideal R), ↑ I=↑M*((1: fractional_ideal f)/↑M),
 ring, apply (fractional_ideal.le_one_iff_exists_coe_ideal.mp hMMinv_inclR),
have h_Iincl : M ≤ I,
  {suffices h_Iincl_f : (↑M: fractional_ideal f) ≤ (↑I: fractional_ideal f),-- what follows is the proof that h_Iincl_f → h_Iincl
   intros x hx,
   let y := f.to_map x,
   have defy: f.to_map x = y, refl,
   have hy : y ∈  (↑ M : fractional_ideal f), simp, use x, exact ⟨hx,defy⟩,
   have hyI : y ∈  (↑ I : fractional_ideal f),
    apply fractional_ideal.le_iff.mp h_Iincl_f, exact hy,
   obtain ⟨a, ⟨ ha, hfa ⟩ ⟩ : ∃ (x' ∈ I), f.to_map x' = y,
    apply fractional_ideal.mem_coe.mp hyI,
   have hax : a=x,
   suffices haxf : f.to_map a=f.to_map x, apply fraction_map.injective f haxf,
    rw hfa, subst hax, exact ha, rw hI, exact hM_inclMinv,
  },
have h_top : I= ⊤,
  {by_contradiction h_abs,
    have h_IM : I = M, apply (is_maximal.eq_of_le hM h_abs h_Iincl).symm,
    have h_inveqR : 1/↑ M = (1:fractional_ideal f),
      {suffices h_invR_dbl : 1/↑ M≤ (1:fractional_ideal f) ∧ (1:fractional_ideal f) ≤ 1/↑ M,
       apply (has_le.le.le_iff_eq h_invR_dbl.right).mp (h_invR_dbl.left),
       split,
        {intros x hx,--the proof that 1/M ≤ 1
         have h_MMinvI : ↑ M * (1 / ↑M : fractional_ideal f) = ↑M, rw ← hI, rw h_IM,
         have h_integralfx : (f.to_map).is_integral_elem x, apply if_inv_then_int _ x hnz_M h_MMinvI hx,
         have h_intxR : x ∈ (integral_closure R f.codomain), apply h_integralfx,
         have h_xintegral : x ∈ (⊥  : subalgebra R f.codomain), rw ← ((is_dedekind_domain_iff _ _ f).mp h).right.right.right, exact h_intxR,
         have h_coe : ((⊥  : subalgebra R f.codomain) : submodule R f.codomain) = localization_map.coe_submodule f ⊤,
          --  have try : (⊥  : subalgebra R f.codomain) = (f.to_map).alg_hom.range, →  I believe that the localization map should be upbgraded to a algebra hom (see l. 91 of localization.lean)
         sorry,
         suffices h_final : x ∈ localization_map.coe_submodule f ⊤,
         simpa, rw ← h_coe, exact h_xintegral,
        },
        {sorry,--the proof that 1≤ 1/M
        --
        },
      },--end of the proof of h_inveqR (assuming h_abs)
    sorry, -- this sorry (showing that h_inveqR is absurd) must be replaced by the 3rd part in Samuel's proof, using his Lemma 3 on prime ideals
  },--end of the proof of h_top
have h_okfI : ↑I=(1 : fractional_ideal f), apply fractional_ideal.ext_iff.mp,
 intros x,split,
  {intro hx,
   have h_x' : ∃ (x' ∈  (I : ideal R)), f.to_map x' = x,
   apply fractional_ideal.mem_coe.mp hx,
   apply fractional_ideal.mem_one_iff.mpr, simp * at *,
  },
  {intro hx,
   have h_x' : ∃ x' ∈ (1:ideal R),  f.to_map x' = x,
   apply fractional_ideal.mem_coe.mp hx,
   rw h_top,simp,
   rcases h_x' with ⟨a, ⟨ha,hfa⟩ ⟩,
   use a,exact hfa,
  },
rw ← hI, exact h_okfI,
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
