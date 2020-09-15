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
  @unique_factorization_domain.integrally_closed A _ _
    (principal_ideal_ring.to_unique_factorization_domain) _ _⟩

namespace dedekind_domain

variables {R S : Type*} [integral_domain R] [integral_domain S] [algebra R S]
variables {L : Type*} [field K] [field L] {f : fraction_map R K}

open finsupp polynomial

-- lemma smul_mul (a₁ a₂ : α) (b : β) : b • (a₁ * a₂) = b * a₁ * a₂ :=
-- by sorry,

lemma smul_mul (a₁ a₂ : f.codomain) (b : R) : b • (a₁ * a₂) = f.to_map b * a₁ * a₂ :=
begin
sorry,
end

variables {M : ideal R} [is_maximal M]

/-
From Kevin:

lemma le_div_iff_mul_le {I J K : submodule R A} : I ≤ J / K ↔ I * K ≤ J :=
begin
  rw le_div_iff,
  rw mul_le,
end
-/

-- lemma le_div_iff_of_nonzero' {I J J' : fractional_ideal f} (hJ' : J'≠ 0) :  I ≤ J * (1/ J') ↔  J'*I ≤ J:= sorry
-- it is actually equal to algebra_operations.le_div_iff_mul_le added recently

-- lemma le_square {I : fractional_ideal f} (hI: I ≤ (1:fractional_ideal f)) : I*I ≤ I :=
-- begin apply fractional_ideal.mul_le.mpr,
-- end


-- lemma le_self {I : fractional_ideal f}: (I : fractional_ideal f)≤ (1: fractional_ideal f)*I :=
-- begin simp,exact le_refl I,
-- end


-- lemma coe_ideal_in_one {I : ideal R}: ↑ I ≤ (1 : fractional_ideal f):=
-- begin
--   intros x hx,
--   have ex_x' : ∃ (x' ∈ I), f.to_map x' = x,
--   apply fractional_ideal.mem_coe.mp hx,
--   apply fractional_ideal.mem_one_iff.mpr,simp * at *,
--   cases ex_x' with y hy,
--   use y,exact and.right hy,
-- end

-- lemma coe_ideal_iff_in_one {J : fractional_ideal f}:  (J ≤ (1 : fractional_ideal f)) ↔ ∃ (I : ideal R), ↑I=J:=
-- begin
--   split,
--     {intro hJ,rw fractional_ideal.le_iff at hJ,
--     let setI : (set R) := {x : R | f.to_map x ∈ J},
--     let I : (ideal R),
--         {use setI,
--         have f_zJ : (f.to_map (0 : R))=0,
--         rw f.to_map.map_zero,simp,sorry,
--         sorry,--proof that 0 ∈ J,
--         sorry,--proof that a,b ∈ I → a+b ∈ I,
--         sorry,--proof that a ∈  I → c*a ∈ I,},
--         },
--     use I,sorry,--proof that ↑ I = J,
--     -- replace hJ := fractional_ideal.mem_one_iff.mp hJ,
--     -- apply fractional_ideal.mem_one_iff.mp at hJ,
--     },
--   {intro ex_I,cases ex_I with I hI,
--   have hI: ↑ I≤ (1:fractional_ideal f),
--   apply coe_ideal_in_one,simp * at *},
-- end


lemma maximal_ideal_inv_of_dedekin
  (h : is_dedekind_domain R) {M : ideal R}
  (hM : ideal.is_maximal M) (hnz_M : M ≠ 0): is_unit (M : fractional_ideal f) :=
begin
  have hnz_Mf : (↑ M : fractional_ideal f) ≠ (0 : fractional_ideal f),
    sorry,--apply fractional_ideal.mkid_ne_zero_iff_nonzero.mpr hnz_M,
  have h_MfinR : ↑M≤ (1:fractional_ideal f), apply fractional_ideal.coe_ideal_le_one,
  have hM_inclMinv : (↑ M : fractional_ideal f) ≤ (↑ M : fractional_ideal f)*(1/↑ M : fractional_ideal f),sorry,
    -- apply (fractional_ideal.le_div_iff_mul_le hnz_Mf).mpr (le_square h_MfinR),
  have h_self : (↑ M : fractional_ideal f)≤ (1: fractional_ideal f)*↑ M,
  simp,exact le_refl ↑ M,
  have hMMinv_inclR : ↑ M * (1/↑ M) ≤ (1 : fractional_ideal f),
    apply (le_div_iff_of_nonzero' hnz_Mf).mp (fractional_ideal.mul_self_le_self h_self),
  suffices hprod : ↑M*((1: fractional_ideal f)/↑M)=(1: fractional_ideal f),
  apply is_unit_of_mul_eq_one ↑M ((1: fractional_ideal f)/↑M) hprod,
      --now comes the 'hard' part: showing that M*(1/M)≤ 1 implies M*(1/M)=1 since M is max'l.
  have h_nonfrac : ∃ (I : ideal R), ↑M*((1: fractional_ideal f)/↑M)=↑I,
     sorry,--this sorry replaces a proof that ↑ M*M1=↑ I and
           --should follow from hMMinv_inclR, checking coercion
  cases h_nonfrac with I hI,--could replace the above have and this cases by obtain?
  have h_Iincl : M ≤ I,
    {suffices h_Iincl_f : (↑M: fractional_ideal f) ≤ (↑I: fractional_ideal f),-- what follows it the proof that h_Iincl_f → h_Iincl
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
      rw ← hI,exact hM_inclMinv,
    },
  have h_Itop : I=⊤,apply and.elim_right hM I,sorry,--this second sorry replaces a proof that M < I
  have h_okI : ↑I=(1 : fractional_ideal f),apply fractional_ideal.ext_iff.mp,
    intros x,split,
      {intro hx,
      have h_x' : ∃ (x' ∈  (I : ideal R)), f.to_map x' = x,
      apply fractional_ideal.mem_coe.mp hx,
      apply fractional_ideal.mem_one_iff.mpr,simp * at *,
      },
      {intro hx,
      have h_x' : ∃ x' ∈ (1:ideal R),  f.to_map x' = x,
      apply fractional_ideal.mem_coe.mp hx,
      rw h_Itop,simp * at *,
      },
    rw hI,exact h_okI,
end



lemma maximal_ideal_invertible_of_dedekind (h : is_dedekind_domain R) {M : ideal R}
  (hM : ideal.is_maximal M) (hnonzeroM : M ≠ 0): is_unit (M : fractional_ideal f) :=
-- ⟨⟨M, M⁻¹, _, _⟩, rfl⟩
begin
let setM1 := {x : K | ∀ y ∈ M, f.is_integer (x * f.to_map y)},
let M1 : fractional_ideal f,
{use setM1,
  {intros y h,simp,use 0,simp,},
  {intros a b ha hb,intros y h,rw add_mul a b (f.to_map y),
  apply localization_map.is_integer_add,apply ha,exact h,apply hb,exact h,},
  -- {intros c x h y h,
  -- apply smul_mul c},
   { intros c x h1 y h,
    rw algebra.smul_mul_assoc,
    apply localization_map.is_integer_smul,
    exact h1 y h,},sorry,--this sorry is here because the "second component" of a fractional_ideal is
                          --a proof that ∃ a s.t. ∀ b blablabla; and this I still miss
},
-- have M1_one : (1 : K) ∈ M1,sorry,
have h_MinMM1 : ↑M ≤ ↑M*M1,sorry,
  -- {intros x hx,cases hx with a ha,
  -- },
have hprod : ↑M*M1=(1: fractional_ideal f),
suffices hincl: ↑M*M1≤ 1, --first we start with the proof that hincl → hprod
  have h_nonfrac : ∃ (I : ideal R), ↑M*M1=↑I,
  -- cases is_fractional f M1.2 with a ha,
  -- let setI := (↑ M : fractional_ideal f).val * (M1.val),
  sorry,--this sorry replaces a proof that ↑ M*M1=↑ I and
                                                    --should follow from hincl, checking coercion
  cases h_nonfrac with I hI,--could replace the above have and this cases by obtain?
  have h_Iincl : M ≤ I,
    {suffices h_Iincl_f : (↑M: fractional_ideal f) ≤ (↑I: fractional_ideal f),-- what follows it the proof that h_Iincl_f → h_Iincl
      intros x hx,
      let y := f.to_map x,
      have defy: f.to_map x =y,refl,
      have hy : y ∈  (↑ M : fractional_ideal f), use x,sorry,
      --apply fractional_ideal.mem_coe.mpr ↑ M,
      have hyI : y ∈  (↑ I : fractional_ideal f),
      apply fractional_ideal.le_iff.mp h_Iincl_f,exact hy,
      have hxyI : ∃ (x' ∈ I), f.to_map x' = y,
      apply fractional_ideal.mem_coe.mp hyI,
      rcases hxyI with ⟨a, ⟨ha, hfa⟩⟩,
      have hax : a=x,
        suffices haxf : f.to_map a=f.to_map x,apply fraction_map.injective f haxf,rw hfa,
      subst hax,exact ha,
      rw ← hI,exact h_MinMM1,
    },
  have h_Itop : I=⊤,apply and.elim_right hM I,sorry,--this second sorry "proves" that M < I
  have h_okI : ↑I = (1 : fractional_ideal f),sorry,--this shoud be an easy matter of coercion
  rw hI,exact h_okI,
  -- have h_unitI : (1 : R) ∈ I, apply (eq_top_iff_one I).mp,exact h_Itop,
  -- have h_IR : I= (1: ideal R),simp,exact h_Itop,

  sorry,--this sorry replaces a proof of hincl and fractional_ideal.mul_le could be useful
apply is_unit_of_mul_eq_one ↑M M1 hprod,
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
 h.dimension_le_one.integral_closure,
 integral_closure_idem⟩

end dedekind_domain
