/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import data.zmod.quotient
import number_theory.class_number.number_field

import algebraic_geometry.EllipticCurve.group
import algebraic_geometry.EllipticCurve.fractional_ideal

/-!
# Kummer theory lemmas
-/

noncomputable theory
open_locale big_operators classical non_zero_divisors number_field

universe u

variables {K : Type u} [field K]

----------------------------------------------------------------------------------------------------
/-! # Lemmas -/

private lemma is_localization.mk'_num_ne_zero_of_ne_zero {R : Type u} [comm_ring R] [algebra R K]
  {S : submonoid R} [is_localization S K] {z : K} {x : R} {y : S}
  (hxyz : z = is_localization.mk' K x y) (hz : z ≠ 0) : x ≠ 0 :=
by { intro hx, rw [hx, is_localization.mk'_zero] at hxyz, exact hz hxyz }

private lemma is_integrally_closed.exists_algebra_map_eq_of_pow_mem {R : Type*} [comm_ring R]
  [algebra R K] {S : subalgebra R K} [is_integrally_closed S] [is_fraction_ring S K] {x : K} {n : ℕ}
  (hn : 0 < n) (hx : x ^ n ∈ S) : ∃ y : S, algebra_map S K y = x :=
is_integrally_closed.is_integral_iff.mp ⟨polynomial.X ^ n - polynomial.C (⟨x ^ n, hx⟩ : S),
  ⟨polynomial.monic_X_pow_sub_C ⟨x ^ n, hx⟩ $ ne_zero_of_lt hn,
   by simpa only [polynomial.eval₂_sub, polynomial.eval₂_X_pow, polynomial.eval₂_C, sub_eq_zero]⟩⟩

@[simp] private lemma fractional_ideal.pow_eq_one_of_pow_mul_eq_one {R : Type u} [comm_ring R]
  [is_domain R] [is_dedekind_domain R] [algebra R K] [is_fraction_ring R K] {I : ideal R} {z : ℤ}
  {n : ℕ} (hn : 0 < n) (hI : (I : fractional_ideal R⁰ K) ^ (z * n) = 1) :
  (I : fractional_ideal R⁰ K) ^ z = 1 :=
begin
  cases nat.exists_eq_succ_of_ne_zero (ne_zero_of_lt hn) with m hm,
  rw [hm] at hI,
  induction z using int.induction_on with w _ w _,
  { rw [zero_mul] at hI,
    exact hI },
  all_goals { rw [zpow_mul₀'] at hI },
  any_goals { rw [← neg_add', zpow_neg₀, inv_eq_one₀] at hI ⊢ },
  all_goals { rw [zpow_coe_nat, ← fractional_ideal.coe_ideal_pow] at hI,
              rw [int.coe_nat_add_one_out, zpow_coe_nat, ← fractional_ideal.coe_ideal_pow,
                  fractional_ideal.coe_ideal_eq_one_iff, ideal.one_eq_top, ideal.eq_top_iff_one]
                at hI ⊢, rw [pow_succ I, mul_pow] at hI, exact ideal.mul_le_right hI }
end

private def fractional_ideal.units_of_factorization {R : Type u} [comm_ring R] [is_domain R]
  [is_dedekind_domain R] [algebra R K] [is_fraction_ring R K] (f : maximal_spectrum R → ℤ) :
  (fractional_ideal R⁰ K)ˣ :=
units.mk0 (∏ᶠ p : maximal_spectrum R, ↑p.val.val ^ f p)
begin
  rw [finprod_def],
  split_ifs,
  { exact finset.prod_ne_zero_iff.mpr
      (λ p _, zpow_ne_zero _ $ fractional_ideal.coe_ideal_ne_zero p.property) },
  { exact one_ne_zero }
end

@[simp] private lemma fractional_ideal.span_singleton_eq_span_singleton {R : Type u} [comm_ring R]
  [algebra R K] [no_zero_smul_divisors R K] (S : submonoid R) [is_localization S K] {x y : K}
  (hx : x ≠ 0) (hy : y ≠ 0) :
  fractional_ideal.span_singleton S x = fractional_ideal.span_singleton S y
    ↔ ∃ u : Rˣ, u • x = y :=
begin
  split,
  { intro hxy,
    cases (fractional_ideal.mem_span_singleton S).mp
      (by { rw [hxy], apply fractional_ideal.mem_span_singleton_self }) with v hv,
    cases (fractional_ideal.mem_span_singleton S).mp
      (by { rw [← hxy], apply fractional_ideal.mem_span_singleton_self }) with i hi,
    have vi : v * i = 1 :=
    begin
      rw [← one_smul R y, ← hi, smul_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero] at hv,
      cases hv,
      { exact sub_eq_zero.mp hv },
      { contradiction }
    end,
    have iv : i * v = 1 :=
    begin
      rw [← one_smul R x, ← hv, smul_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero] at hi,
      cases hi,
      { exact sub_eq_zero.mp hi },
      { contradiction }
    end,
    exact ⟨⟨v, i, vi, iv⟩, hv⟩ },
  { rintro ⟨⟨v, i, _, iv⟩, hxy : v • x = y⟩,
    ext,
    rw [fractional_ideal.mem_span_singleton, fractional_ideal.mem_span_singleton],
    exact ⟨λ ⟨z, hz⟩, ⟨z * i, by rw [← smul_smul, ← hxy, smul_smul i v, iv, one_smul, ← hz]⟩,
           λ ⟨z, hz⟩, ⟨z * v, by rw [← smul_smul, ← hz, ← hxy]⟩⟩ }
end

@[simp] private lemma fractional_ideal.span_singleton_pow {R : Type u} [comm_ring R] [algebra R K]
  (S : submonoid R) [is_localization S K] (x : K) (n : ℕ) :
  fractional_ideal.span_singleton S x ^ n = fractional_ideal.span_singleton S (x ^ n) :=
begin
  induction n with n hn,
  { rw [pow_zero, pow_zero, fractional_ideal.span_singleton_one] },
  { rw [pow_succ, pow_succ, hn, fractional_ideal.span_singleton_mul_span_singleton] }
end

private lemma function.mul_support_pow {α R : Type u} [comm_semiring R] {f : α → R}
  (hf : (function.mul_support f).finite) (n : ℕ) : (function.mul_support $ λ x, f x ^ n).finite :=
begin
  induction n with n hfn,
  { simp_rw [pow_zero],
    rw [function.mul_support_one],
    exact set.finite_empty },
  { simp_rw [pow_succ],
    exact set.finite.subset (set.finite.union hf hfn) (function.mul_support_mul f $ f ^ n) }
end

@[simp] private lemma finprod_pow {α R : Type u} [comm_semiring R] {f : α → R}
  (hf : (function.mul_support f).finite) (n : ℕ) : finprod f ^ n = ∏ᶠ x, f x ^ n :=
begin
  induction n with n hn,
  { simp_rw [pow_zero],
    exact finprod_one.symm },
  { simp_rw [pow_succ],
    rw [hn],
    exact (finprod_mul_distrib hf $ function.mul_support_pow hf n).symm }
end

----------------------------------------------------------------------------------------------------

namespace number_field

----------------------------------------------------------------------------------------------------
/-! ## Primes and valuations -/

section valuation

variables [number_field K] {n : ℕ}

/-- The multiplicative valuation of a non-zero element. -/
def val_of_ne_zero (p : maximal_spectrum $ 𝓞 K) : Kˣ →* multiplicative ℤ :=
group.with_zero_units.to_monoid_hom.comp $ units.map $ @maximal_spectrum.valuation _ _ _ _ K _ _ _ p

lemma associates.eq_val_of_ne_zero (p : maximal_spectrum $ 𝓞 K) (x : Kˣ) :
  ((associates.mk p.val.val).count $ associates.factors $ associates.mk $ ideal.span
    {(is_localization.mk'_surjective (𝓞 K)⁰ (x : K)).some} : ℤ)
    - ((associates.mk p.val.val).count $ associates.factors $ associates.mk $ ideal.span
        {((is_localization.mk'_surjective (𝓞 K)⁰ (x : K)).some_spec.some : 𝓞 K)} : ℤ)
  = -(val_of_ne_zero p x).to_add :=
begin
  change _ = -classical.some _,
  rw [← neg_neg_sub_neg, neg_inj, ← with_zero.coe_inj,
      (with_zero.ne_zero_iff_exists.mp (_ : (with_zero $ multiplicative ℤ)ˣ).ne_zero).some_spec],
  change _ = ite _ _ _ / ite _ _ _,
  simpa only [if_neg (is_localization.mk'_num_ne_zero_of_ne_zero
                      (is_localization.mk'_surjective _ x.val).some_spec.some_spec.symm x.ne_zero),
              if_neg (non_zero_divisors.coe_ne_zero (_ : (𝓞 K)⁰))]
end

lemma fractional_ideal.factorization_of_ne_zero (x : Kˣ) :
  ∏ᶠ p : maximal_spectrum $ 𝓞 K,
    (p.val.val : fractional_ideal (𝓞 K)⁰ K) ^ -(val_of_ne_zero p x).to_add
      = fractional_ideal.span_singleton (𝓞 K)⁰ x :=
begin
  simp_rw [← λ p : maximal_spectrum $ 𝓞 K, associates.eq_val_of_ne_zero p x],
  exact fractional_ideal.factorization_principal (fractional_ideal.span_singleton (𝓞 K)⁰ x)
    (fractional_ideal.span_singleton_ne_zero_iff.mpr x.ne_zero) x rfl
end

lemma val_of_ne_zero_support_finite (x : Kˣ) :
  (function.mul_support $ λ p : maximal_spectrum $ 𝓞 K,
    (p.val.val : fractional_ideal (𝓞 K)⁰ K) ^ -(val_of_ne_zero p x).to_add).finite :=
begin
  simp_rw [← associates.eq_val_of_ne_zero, λ p : maximal_spectrum $ 𝓞 K, zpow_sub₀
             (fractional_ideal.coe_ideal_ne_zero p.property : _ ≠ (0 : fractional_ideal (𝓞 K)⁰ K))],
  apply set.finite.subset (set.finite.union _ _) (function.mul_support_div _ _),
  all_goals { apply ideal.finite_mul_support_coe
                ((not_iff_not.mpr ideal.span_singleton_eq_bot).mpr _) },
  { exact is_localization.mk'_num_ne_zero_of_ne_zero
      (is_localization.mk'_surjective (𝓞 K)⁰ x.val).some_spec.some_spec.symm x.ne_zero },
  { exact non_zero_divisors.coe_ne_zero _ }
end

/-- The multiplicative valuation of a non-zero element modulo `n`-th powers. -/
def val_of_ne_zero_mod (p : maximal_spectrum $ 𝓞 K) : Kˣ ⧸ (n⬝Kˣ) →* multiplicative (zmod n) :=
(int.quotient_zmultiples_nat_equiv_zmod n).to_multiplicative.to_monoid_hom.comp $
  quotient_group.map (n⬝Kˣ) (add_subgroup.zmultiples (n : ℤ)).to_subgroup (val_of_ne_zero p) $
begin
  rintro x ⟨y, hy⟩,
  rw [← hy],
  exact ⟨val_of_ne_zero p y, by simpa only [zpow_group_hom_apply, map_zpow, int.to_add_zpow]⟩
end

end valuation

----------------------------------------------------------------------------------------------------
/-! ## Unit group lemmas -/

section unit

/-- The canonical inclusion `𝓞ˣ →* Kˣ`. -/
def ne_zero_of_unit : (𝓞 K)ˣ →* Kˣ :=
{ to_fun   := λ ⟨⟨v, _⟩, ⟨i, _⟩, vi, iv⟩, ⟨v, i, subtype.mk_eq_mk.mp vi, subtype.mk_eq_mk.mp iv⟩,
  map_one' := rfl,
  map_mul' := λ ⟨⟨_, _⟩, ⟨_, _⟩, _, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩, _, _⟩, rfl }

@[simp] lemma ne_zero_of_unit.map_one : ne_zero_of_unit 1 = (1 : Kˣ) := ne_zero_of_unit.map_one'

@[simp] lemma ne_zero_of_unit.map_mul (x y : (𝓞 K)ˣ) :
  ne_zero_of_unit (x * y) = ne_zero_of_unit x * ne_zero_of_unit y :=
ne_zero_of_unit.map_mul' x y

variables [number_field K] {n : ℕ}

@[simp] lemma val_of_unit (p : maximal_spectrum $ 𝓞 K) (x : (𝓞 K)ˣ) :
  val_of_ne_zero p (ne_zero_of_unit x) = 1 :=
begin
  rcases x with ⟨⟨v, hv⟩, ⟨i, hi⟩, vi, _⟩,
  rw [val_of_ne_zero, monoid_hom.comp_apply, mul_equiv.coe_to_monoid_hom, mul_equiv.map_eq_one_iff,
      units.map, monoid_hom.mk'_apply, units.ext_iff, eq_iff_le_not_lt],
  split,
  { exact p.valuation_le_one ⟨v, hv⟩ },
  { injection vi with hvi,
    apply_fun p.valuation at hvi,
    rw [map_one, map_mul] at hvi,
    change ¬p.valuation v < 1,
    rw [not_lt, ← hvi],
    nth_rewrite_rhs 0 [← mul_one $ p.valuation v],
    exact @with_zero.mul_le_mul_left _ _ _
      ⟨group.covariant_iff_contravariant.mpr contravariant_class.elim⟩ _ _
      (p.valuation_le_one ⟨i, hi⟩) _ }
end

@[simp] lemma val_of_unit_mod (p : maximal_spectrum $ 𝓞 K) (x : (𝓞 K)ˣ) :
  val_of_ne_zero_mod p (ne_zero_of_unit x) = (0 : zmod n) :=
by simpa only [val_of_ne_zero_mod, monoid_hom.comp_apply, quotient_group.map_coe, val_of_unit]

-- Input : finite generation of unit group or Dirichlet's unit theorem
/-- `𝓞ˣ` is finitely generated. -/
instance : group.fg (𝓞 K)ˣ := sorry

/-- `𝓞ˣ/(𝓞ˣ)ⁿ` is finite. -/
instance : fintype $ (𝓞 K)ˣ ⧸ (n⬝(𝓞 K)ˣ) :=
@quotient_group.fintype_of_fg _ _ (by apply @units.group.fg K _) n

end unit

----------------------------------------------------------------------------------------------------
/-! ## The subgroup `K(S, n)` -/

section K_S_n

variables [number_field K] {S S' : finset $ maximal_spectrum $ 𝓞 K} {n : ℕ}

/-- The subgroup `K(S, n) = {b(Kˣ)ⁿ ∈ Kˣ/(Kˣ)ⁿ | ∀ p ∉ S, ord_p(b) ≡ 0 mod n}`. -/
def K_S_n : subgroup (Kˣ ⧸ (n⬝Kˣ)) :=
{ carrier  := {b : Kˣ ⧸ (n⬝Kˣ) | ∀ p ∉ S, val_of_ne_zero_mod p b = 1},
  one_mem' := λ _ _, by rw [map_one],
  mul_mem' := λ _ _ hx hy p hp, by rw [map_mul, hx p hp, hy p hp, one_mul],
  inv_mem' := λ _ hx p hp, by rw [map_inv, hx p hp, one_inv] }

notation K⟮S, n⟯ := @K_S_n K _ _ S n

lemma K_S_n.one_mem : (1 : Kˣ ⧸ (n⬝Kˣ)) ∈ K⟮S, n⟯ := K_S_n.one_mem'

lemma K_S_n.mul_mem {x y : Kˣ ⧸ (n⬝Kˣ)} (hx : x ∈ K⟮S, n⟯) (hy : y ∈ K⟮S, n⟯) : x * y ∈ K⟮S, n⟯ :=
K_S_n.mul_mem' hx hy

lemma K_S_n.inv_mem {x : Kˣ ⧸ (n⬝Kˣ)} (hx : x ∈ K⟮S, n⟯) : x⁻¹ ∈ K⟮S, n⟯ := K_S_n.inv_mem' hx

lemma K_S_n.monotone (hS : S' ≤ S) : K⟮S', n⟯ ≤ K⟮S, n⟯ := λ _ hb p hp, hb p $ mt (@hS p) hp

/-- The multiplicative valuation on K_S_n. -/
def K_S_n.val : K⟮S, n⟯ →* S → multiplicative (zmod n) :=
{ to_fun   := λ b p, val_of_ne_zero_mod (p : maximal_spectrum $ 𝓞 K) (b : Kˣ ⧸ (n⬝Kˣ)),
  map_one' := funext $ λ p, map_one $ val_of_ne_zero_mod p,
  map_mul' := λ x y, funext $ λ p, map_mul (val_of_ne_zero_mod p) x y }

@[simp] lemma K_S_n.val.map_one : K_S_n.val (1 : K⟮S, n⟯) = 1 := K_S_n.val.map_one'

@[simp] lemma K_S_n.val.map_mul (x y : K⟮S, n⟯) : K_S_n.val (x * y) = K_S_n.val x * K_S_n.val y :=
K_S_n.val.map_mul' x y

lemma K_S_n.val_ker : K_S_n.val.ker = K⟮∅, n⟯.subgroup_of K⟮S, n⟯ :=
begin
  ext ⟨x, hx⟩,
  split,
  { intros hx' p _,
    by_cases hp : p ∈ S,
    { exact congr_fun hx' ⟨p, hp⟩ },
    { exact hx p hp } },
  { exact λ hx', funext $ λ p, hx' p $ finset.not_mem_empty p }
end

/-- A group homomorphism `𝓞ˣ → K(∅, n)`. -/
def K_0_n.from_unit : (𝓞 K)ˣ →* K⟮∅, n⟯ :=
{ to_fun   := λ x, ⟨quotient_group.mk $ ne_zero_of_unit x, λ p _, val_of_unit_mod p x⟩,
  map_one' := rfl,
  map_mul' := λ ⟨⟨_, _⟩, ⟨_, _⟩, _, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩, _, _⟩, rfl }

@[simp] lemma K_0_n.from_unit.map_one : K_0_n.from_unit 1 = (1 : K⟮∅, n⟯) :=
K_0_n.from_unit.map_one'

@[simp] lemma K_0_n.from_unit.map_mul (x y : (𝓞 K)ˣ) :
  (K_0_n.from_unit (x * y) : K⟮∅, n⟯) = K_0_n.from_unit x * K_0_n.from_unit y :=
K_0_n.from_unit.map_mul' x y

lemma K_0_n.from_unit_ker [fact $ 0 < n] : (@K_0_n.from_unit K _ _ n).ker = (n⬝(𝓞 K)ˣ) :=
begin
  ext ⟨⟨v, hv⟩, ⟨i, hi⟩, _, _⟩,
  split,
  { intro hx,
    cases (quotient_group.eq_one_iff _).mp (subtype.mk_eq_mk.mp hx) with x hx,
    have hv : ((x ^ (n : ℤ) : Kˣ) : K) = v := congr_arg units.val hx,
    have hi : (((x ^ (n : ℤ))⁻¹ : Kˣ) : K) = i := congr_arg units.inv hx,
    substs hv hi,
    rw [← inv_zpow] at hi,
    rw [zpow_coe_nat, units.coe_pow] at hv hi,
    cases is_integrally_closed.exists_algebra_map_eq_of_pow_mem _inst_3.elim hv with v' hv',
    cases is_integrally_closed.exists_algebra_map_eq_of_pow_mem _inst_3.elim hi with i' hi',
    existsi [(⟨v', i', _, _⟩ : (𝓞 K)ˣ)],
    { rw [units.ext_iff, subtype.ext_iff, zpow_group_hom_apply, zpow_coe_nat, units.coe_pow,
          subalgebra.coe_pow],
      simp_rw [units.coe_zpow₀, zpow_coe_nat],
      exact congr_arg (flip (^) n) hv' },
    all_goals { apply_fun (algebra_map (𝓞 K) K),
                any_goals { exact λ ⟨_, _⟩ ⟨_, _⟩, subtype.mk_eq_mk.mpr },
                rw [map_mul, hv', hi'] },
    { exact x.val_inv },
    { exact x.inv_val } },
  { rintro ⟨⟨⟨v', _⟩, ⟨i', _⟩, vi', iv'⟩, hx⟩,
    rw [units.ext_iff, subtype.ext_iff, zpow_group_hom_apply, zpow_coe_nat, units.coe_pow,
        subalgebra.coe_pow] at hx,
    exact subtype.mk_eq_mk.mpr ((quotient_group.eq_one_iff _).mpr
      ⟨⟨v', i', by injection vi', by injection iv'⟩,
       by simpa only [units.ext_iff, zpow_group_hom_apply, zpow_coe_nat, units.coe_pow] using hx⟩) }
end

lemma K_0_n.val_exists_of_mk (p : maximal_spectrum $ 𝓞 K) {x : Kˣ}
  (hx : quotient_group.mk x ∈ K⟮∅, n⟯) : ∃ z : ℤ, z * n = -(val_of_ne_zero p x).to_add :=
begin
  have hp : val_of_ne_zero_mod p x = 1 := hx p (finset.not_mem_empty p),
  rw [val_of_ne_zero_mod, monoid_hom.comp_apply, mul_equiv.coe_to_monoid_hom,
      mul_equiv.map_eq_one_iff, quotient_group.map_coe, quotient_group.eq_one_iff] at hp,
  cases hp with z hz,
  exact ⟨-z, by simpa only [neg_mul, neg_inj] using hz⟩
end

lemma K_0_n.val_support_finite [fact $ 0 < n] {x : Kˣ} (hx : quotient_group.mk x ∈ K⟮∅, n⟯) :
  (function.mul_support $ λ p : maximal_spectrum $ 𝓞 K,
    (p.val.val : fractional_ideal (𝓞 K)⁰ K) ^ (K_0_n.val_exists_of_mk p hx).some).finite :=
begin
  apply set.finite.subset (val_of_ne_zero_support_finite x),
  intros p hp,
  change (p.val.val : fractional_ideal (𝓞 K)⁰ K) ^ -(val_of_ne_zero p x).to_add ≠ 1,
  rw [← (K_0_n.val_exists_of_mk p hx).some_spec],
  exact not_imp_not.mpr (fractional_ideal.pow_eq_one_of_pow_mul_eq_one _inst_3.elim) hp
end

lemma K_0_n.val_exists (p : maximal_spectrum $ 𝓞 K) (x : K⟮∅, n⟯) :
  ∃ z : ℤ, z * n = -(val_of_ne_zero p x.val.out').to_add :=
K_0_n.val_exists_of_mk p $ by simpa only [quotient_group.out_eq'] using x.property

/-- A set function `K(∅, n) → Cl(K)`. -/
def K_0_n.to_class.to_fun (x : K⟮∅, n⟯) : class_group (𝓞 K) K :=
quotient_group.mk' (to_principal_ideal (𝓞 K) K).range $ fractional_ideal.units_of_factorization $
  λ p, (K_0_n.val_exists p x).some

variables [fact $ 0 < n]

@[simp] lemma K_0_n.to_class_of_mk {x : Kˣ} (hx : quotient_group.mk x ∈ K⟮∅, n⟯) :
  K_0_n.to_class.to_fun ⟨quotient_group.mk x, hx⟩
    = quotient_group.mk' (to_principal_ideal (𝓞 K) K).range
      (fractional_ideal.units_of_factorization $ λ p, (K_0_n.val_exists_of_mk p hx).some) :=
begin
  rcases quotient_group.mk_out'_eq_mul (n⬝Kˣ) x with ⟨⟨_, ⟨z, hz⟩⟩, hy⟩,
  have val : ∀ p : maximal_spectrum $ 𝓞 K,
    (p.val.val : fractional_ideal (𝓞 K)⁰ K) ^ (K_0_n.val_exists p ⟨quotient_group.mk x, hx⟩).some
      = p.val.val ^ (K_0_n.val_exists_of_mk p hx).some * p.val.val ^ -(val_of_ne_zero p z).to_add :=
  begin
    intro p,
    rw [← zpow_add₀
          (fractional_ideal.coe_ideal_ne_zero p.property : _ ≠ (0 : fractional_ideal (𝓞 K)⁰ K))],
    congr' 1,
    rw [← mul_left_inj' $ int.coe_nat_ne_zero_iff_pos.mpr _inst_3.elim,
        (K_0_n.val_exists p ⟨_, hx⟩).some_spec, subtype.val_eq_coe, subtype.coe_mk, hy, map_mul,
        to_add_mul, add_mul, (K_0_n.val_exists_of_mk p hx).some_spec, neg_mul, mul_comm _ (n : ℤ),
        ← neg_add, neg_inj, add_right_inj],
    simp_rw [← hz],
    exact map_zpow (val_of_ne_zero p) z n
  end,
  rw [K_0_n.to_class.to_fun],
  simp_rw [quotient_group.mk'_apply, fractional_ideal.units_of_factorization, val,
           finprod_mul_distrib (K_0_n.val_support_finite hx) (val_of_ne_zero_support_finite z),
           fractional_ideal.factorization_of_ne_zero],
  rw [units.mk0_mul, quotient_group.coe_mul],
  exact mul_right_eq_self.mpr ((quotient_group.eq_one_iff _).mpr
                               ⟨z, by simpa only [to_principal_ideal_eq_iff]⟩)
end

/-- A group homomorphism `K(∅, n) → Cl(K)`. -/
def K_0_n.to_class : K⟮∅, n⟯ →* class_group (𝓞 K) K :=
{ to_fun   := K_0_n.to_class.to_fun,
  map_one' :=
  begin
    have val_one : ∀ p : maximal_spectrum $ 𝓞 K,
      (p.val.val : fractional_ideal (𝓞 K)⁰ K) ^ (K_0_n.val_exists_of_mk p K⟮∅, n⟯.one_mem).some
        = 1 :=
    begin
      intro p,
      simp_rw [← zpow_zero (p.val.val : fractional_ideal (𝓞 K)⁰ K)],
      congr' 1,
      rw [← mul_left_inj' $ int.coe_nat_ne_zero_iff_pos.mpr _inst_3.elim,
          (K_0_n.val_exists_of_mk p K⟮∅, n⟯.one_mem).some_spec, map_one, zero_mul],
      refl
    end,
    change K_0_n.to_class.to_fun ⟨quotient_group.mk 1, _⟩ = 1,
    rw [K_0_n.to_class_of_mk, quotient_group.mk'_apply, quotient_group.eq_one_iff,
        fractional_ideal.units_of_factorization],
    exact ⟨1, by { rw [to_principal_ideal_eq_iff], simp_rw [val_one, finprod_one],
                   exact fractional_ideal.span_singleton_one }⟩
  end,
  map_mul' := λ ⟨x, hx⟩ ⟨y, hy⟩,
  begin
    have hx' : quotient_group.mk x.out' ∈ K⟮∅, n⟯ := by simpa only [quotient_group.out_eq'],
    have hy' : quotient_group.mk y.out' ∈ K⟮∅, n⟯ := by simpa only [quotient_group.out_eq'],
    have hxy : quotient_group.mk (x.out' * y.out') ∈ K⟮∅, n⟯ :=
    by { change quotient_group.mk x.out' * quotient_group.mk y.out' ∈ K⟮∅, n⟯,
         simpa only [quotient_group.out_eq'] using (⟨x, hx⟩ * ⟨y, hy⟩ : K⟮∅, n⟯).property },
    have x_rw : (⟨x, hx⟩ : K⟮∅, n⟯) = ⟨quotient_group.mk x.out', hx'⟩ :=
    by simp_rw [quotient_group.out_eq'],
    have y_rw : (⟨y, hy⟩ : K⟮∅, n⟯) = ⟨quotient_group.mk y.out', hy'⟩ :=
    by simp_rw [quotient_group.out_eq'],
    have xy_rw : (⟨x, hx⟩ * ⟨y, hy⟩ : K⟮∅, n⟯) = ⟨quotient_group.mk (x.out' * y.out'), hxy⟩ :=
    by { nth_rewrite_lhs 0 [x_rw], nth_rewrite_lhs 0 [y_rw], refl },
    have val_mul : ∀ p : maximal_spectrum $ 𝓞 K,
      (p.val.val : fractional_ideal (𝓞 K)⁰ K) ^ (K_0_n.val_exists_of_mk p hxy).some
        = p.val.val ^ (K_0_n.val_exists_of_mk p hx').some
          * p.val.val ^ (K_0_n.val_exists_of_mk p hy').some :=
    begin
      intro p,
      rw [← zpow_add₀
            (fractional_ideal.coe_ideal_ne_zero p.property : _ ≠ (0 : fractional_ideal (𝓞 K)⁰ K))],
      congr' 1,
      rw [← mul_left_inj' $ int.coe_nat_ne_zero_iff_pos.mpr _inst_3.elim,
          (K_0_n.val_exists_of_mk p hxy).some_spec, map_mul, to_add_mul, neg_add, add_mul,
          (K_0_n.val_exists_of_mk p hx').some_spec, (K_0_n.val_exists_of_mk p hy').some_spec],
    end,
    nth_rewrite_rhs 0 [x_rw],
    nth_rewrite_rhs 0 [y_rw],
    rw [xy_rw],
    simp_rw [K_0_n.to_class_of_mk, quotient_group.mk'_apply,
             fractional_ideal.units_of_factorization, val_mul,
             finprod_mul_distrib (K_0_n.val_support_finite hx') (K_0_n.val_support_finite hy')],
    rw [units.mk0_mul, quotient_group.coe_mul]
  end }

@[simp] lemma K_0_n.to_class.map_one : K_0_n.to_class (1 : K⟮∅, n⟯) = 1 := K_0_n.to_class.map_one'

@[simp] lemma K_0_n.to_class.map_mul (x y : K⟮∅, n⟯) :
  K_0_n.to_class (x * y) = K_0_n.to_class x * K_0_n.to_class y :=
K_0_n.to_class.map_mul' x y

lemma K_0_n.to_class_ker : (@K_0_n.to_class K _ _ n _).ker = K_0_n.from_unit.range :=
begin
  ext ⟨x, hx⟩,
  split,
  { rw [← quotient_group.out_eq' x] at hx,
    intro hx',
    cases (quotient_group.eq_one_iff _).mp hx' with y hy,
    rw [to_principal_ideal_eq_iff] at hy,
    apply_fun λ x, x ^ n at hy,
    rw [fractional_ideal.span_singleton_pow, fractional_ideal.units_of_factorization, units.coe_mk0,
        finprod_pow $ K_0_n.val_support_finite hx] at hy,
    simp_rw [← zpow_coe_nat, ← zpow_mul₀, (K_0_n.val_exists_of_mk _ hx).some_spec] at hy,
    rw [fractional_ideal.factorization_of_ne_zero, fractional_ideal.span_singleton_eq_span_singleton
          (𝓞 K)⁰ (zpow_ne_zero n y.ne_zero) x.out'.ne_zero] at hy,
    cases hy with y hy,
    existsi [y],
    rcases y with ⟨⟨v, hv⟩, ⟨i, hi⟩, vi, iv⟩,
    change (⟨quotient_group.mk' (n⬝Kˣ) (⟨v, i, _, _⟩ : Kˣ), _⟩ : K⟮∅, n⟯) = _,
    simp only,
    rw [← quotient_group.out_eq' x],
    exact quotient_group.mk'_eq_mk'.mpr
      ⟨y ^ (n : ℤ), ⟨y, rfl⟩, by simpa only [units.ext_iff, units.coe_mul, units.coe_zpow₀]⟩ },
  { rintro ⟨y, hy⟩,
    injection hy with hy,
    have hx' : quotient_group.mk (ne_zero_of_unit y) ∈ K⟮∅, n⟯ := by simpa only [hy],
    have x_rw : (⟨x, hx⟩ : K⟮∅, n⟯) = ⟨quotient_group.mk $ ne_zero_of_unit y, hx'⟩ :=
    by simp_rw [hy],
    have val_unit : ∀ p : maximal_spectrum $ 𝓞 K,
      (p.val.val : fractional_ideal (𝓞 K)⁰ K) ^ (K_0_n.val_exists_of_mk p hx').some = 1 :=
    begin
      intro p,
      simp_rw [← zpow_zero (p.val.val : fractional_ideal (𝓞 K)⁰ K)],
      congr' 1,
      rw [← mul_left_inj' $ int.coe_nat_ne_zero_iff_pos.mpr _inst_3.elim,
          (K_0_n.val_exists_of_mk p hx').some_spec, val_of_unit, zero_mul],
      refl
    end,
    rw [x_rw],
    change K_0_n.to_class.to_fun ⟨quotient_group.mk $ ne_zero_of_unit y, hx'⟩ = 1,
    rw [K_0_n.to_class_of_mk, fractional_ideal.units_of_factorization],
    simp_rw [val_unit, finprod_one],
    rw [units.mk0_one],
    refl }
end

/-- `K(∅, n)` is finite. -/
def K_0_n.fintype : fintype K⟮∅, n⟯ := group.fintype_of_ker_codom
begin
  rw [K_0_n.to_class_ker],
  apply fintype.of_equiv _ (quotient_group.quotient_ker_equiv_range K_0_n.from_unit).to_equiv,
  rw [K_0_n.from_unit_ker],
  exact has_quotient.quotient.fintype
end $ ring_of_integers.class_group.fintype K

/-- `K(S, n)` is finite. -/
instance : fintype K⟮S, n⟯ := group.fintype_of_ker_codom
begin
  rw [@K_S_n.val_ker K _ _ S n],
  exact @fintype.of_equiv _ K⟮∅, n⟯ K_0_n.fintype
    (subgroup.comap_subtype_equiv_of_le $ K_S_n.monotone $ finset.empty_subset S).symm.to_equiv
end $ by exact pi.fintype

notation K⟮S, n⟯`²` := (K⟮S, n⟯.prod K⟮S, n⟯).to_add_subgroup

/-- `K(S, n) × K(S, n)` is finite. -/
instance : fintype K⟮S, n⟯² := fintype.of_equiv _ (subgroup.prod_equiv _ _).symm.to_equiv

end K_S_n

----------------------------------------------------------------------------------------------------

end number_field
