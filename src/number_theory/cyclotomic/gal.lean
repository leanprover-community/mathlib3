/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/

import number_theory.cyclotomic.primitive_roots
import field_theory.polynomial_galois_group

/-!
# Galois group of cyclotomic extensions

In this file, we show the relationship between the Galois group of `K(ζₙ)` and `(zmod n)ˣ`;
it is always a subgroup, and if the `n`th cyclotomic polynomial is irreducible, they are isomorphic.

## Main results

* `is_primitive_root.aut_to_pow_injective`: `is_primitive_root.aut_to_pow` is injective
  in the case that it's considered over a cyclotomic field extension.
* `is_cyclotomic_extension.aut_equiv_pow`: If the `n`th cyclotomic polynomial is irreducible in `K`,
  then `is_primitive_root.aut_to_pow` is a `mul_equiv` (for example, in `ℚ` and certain `𝔽ₚ`).
* `gal_X_pow_equiv_units_zmod`, `gal_cyclotomic_equiv_units_zmod`: Repackage
  `is_cyclotomic_extension.aut_equiv_pow` in terms of `polynomial.gal`.
* `is_cyclotomic_extension.aut.comm_group`: Cyclotomic extensions are abelian.

## References

* https://kconrad.math.uconn.edu/blurbs/galoistheory/cyclotomic.pdf

## TODO

* We currently can get away with the fact that the power of a primitive root is a primitive root,
  but the correct long-term solution for computing other explicit Galois groups is creating
  `power_basis.map_conjugate`; but figuring out the exact correct assumptions + proof for this is
  mathematically nontrivial. (Current thoughts: the correct condition is that the annihilating
  ideal of both elements is equal. This may not hold in an ID, and definitely holds in an ICD.)

-/

variables {n : ℕ+} (K : Type*) [field K] {L : Type*} {μ : L}

open polynomial is_cyclotomic_extension

open_locale cyclotomic

namespace is_primitive_root

variables [comm_ring L] [is_domain L] (hμ : is_primitive_root μ n) [algebra K L]
          [is_cyclotomic_extension {n} K L]

/-- `is_primitive_root.aut_to_pow` is injective in the case that it's considered over a cyclotomic
field extension. -/
lemma aut_to_pow_injective : function.injective $ hμ.aut_to_pow K :=
begin
  intros f g hfg,
  apply_fun units.val at hfg,
  simp only [is_primitive_root.coe_aut_to_pow_apply, units.val_eq_coe] at hfg,
  generalize_proofs hf' hg' at hfg,
  have hf := hf'.some_spec,
  have hg := hg'.some_spec,
  generalize_proofs hζ at hf hg,
  suffices : f hμ.to_roots_of_unity = g hμ.to_roots_of_unity,
  { apply alg_equiv.coe_alg_hom_injective,
    apply (hμ.power_basis K).alg_hom_ext,
    exact this },
  rw zmod.eq_iff_modeq_nat at hfg,
  refine (hf.trans _).trans hg.symm,
  rw [←roots_of_unity.coe_pow _ hf'.some, ←roots_of_unity.coe_pow _ hg'.some],
  congr' 1,
  rw [pow_eq_pow_iff_modeq],
  convert hfg,
  rw [hμ.eq_order_of],
  rw [←hμ.coe_to_roots_of_unity_coe] {occs := occurrences.pos [2]},
  rw [order_of_units, order_of_subgroup]
end

end is_primitive_root

namespace is_cyclotomic_extension

variables [comm_ring L] [is_domain L] (hμ : is_primitive_root μ n) [algebra K L]
          [is_cyclotomic_extension {n} K L]

/-- Cyclotomic extensions are abelian. -/
noncomputable def aut.comm_group : comm_group (L ≃ₐ[K] L) :=
((zeta_spec n K L).aut_to_pow_injective K).comm_group _
  (map_one _) (map_mul _) (map_inv _) (map_div _) (map_pow _) (map_zpow _)

variables (h : irreducible (cyclotomic n K)) {K} (L)

include h

/-- The `mul_equiv` that takes an automorphism `f` to the element `k : (zmod n)ˣ` such that
  `f μ = μ ^ k` for any root of unity `μ`. A  strengthening of `is_primitive_root.aut_to_pow`. -/
@[simps] noncomputable def aut_equiv_pow : (L ≃ₐ[K] L) ≃* (zmod n)ˣ :=
let hζ := zeta_spec n K L,
    hμ := λ t, hζ.pow_of_coprime _ (zmod.val_coe_unit_coprime t) in
{ inv_fun := λ t, (hζ.power_basis K).equiv_of_minpoly ((hμ t).power_basis K)
  begin
    haveI := is_cyclotomic_extension.ne_zero' n K L,
    simp only [is_primitive_root.power_basis_gen],
    have hr := is_primitive_root.minpoly_eq_cyclotomic_of_irreducible
               ((zeta_spec n K L).pow_of_coprime _ (zmod.val_coe_unit_coprime t)) h,
    exact ((zeta_spec n K L).minpoly_eq_cyclotomic_of_irreducible h).symm.trans hr
  end,
  left_inv := λ f, begin
    simp only [monoid_hom.to_fun_eq_coe],
    apply alg_equiv.coe_alg_hom_injective,
    apply (hζ.power_basis K).alg_hom_ext,
    simp only [alg_equiv.coe_alg_hom, alg_equiv.map_pow],
    rw power_basis.equiv_of_minpoly_gen,
    simp only [is_primitive_root.power_basis_gen, is_primitive_root.aut_to_pow_spec],
  end,
  right_inv := λ x, begin
    simp only [monoid_hom.to_fun_eq_coe],
    generalize_proofs _ h,
    have key := hζ.aut_to_pow_spec K ((hζ.power_basis K).equiv_of_minpoly ((hμ x).power_basis K) h),
    have := (hζ.power_basis K).equiv_of_minpoly_gen ((hμ x).power_basis K) h,
    rw hζ.power_basis_gen K at this,
    rw [this, is_primitive_root.power_basis_gen] at key,
    rw ← hζ.coe_to_roots_of_unity_coe at key {occs := occurrences.pos [1, 5]},
    simp only [←coe_coe, ←roots_of_unity.coe_pow] at key,
    replace key := roots_of_unity.coe_injective key,
    rw [pow_eq_pow_iff_modeq, ←order_of_subgroup, ←order_of_units, hζ.coe_to_roots_of_unity_coe,
        ←(zeta_spec n K L).eq_order_of, ←zmod.eq_iff_modeq_nat] at key,
    simp only [zmod.nat_cast_val, zmod.cast_id', id.def] at key,
    exact units.ext key
  end,
  .. (zeta_spec n K L).aut_to_pow K }

include hμ

variables {L}

/-- Maps `μ` to the `alg_equiv` that sends `is_cyclotomic_extension.zeta` to `μ`. -/
noncomputable def from_zeta_aut : L ≃ₐ[K] L :=
let hζ := (zeta_spec n K L).eq_pow_of_pow_eq_one hμ.pow_eq_one n.pos in
(aut_equiv_pow L h).symm $ zmod.unit_of_coprime hζ.some $
((zeta_spec n K L).pow_iff_coprime n.pos hζ.some).mp $ hζ.some_spec.some_spec.symm ▸ hμ

lemma from_zeta_aut_spec : from_zeta_aut hμ h (zeta n K L) = μ :=
begin
  simp_rw [from_zeta_aut, aut_equiv_pow_symm_apply],
  generalize_proofs hζ h _ hμ _,
  rw [←hζ.power_basis_gen K] {occs := occurrences.pos [4]},
  rw [power_basis.equiv_of_minpoly_gen, hμ.power_basis_gen K],
  convert h.some_spec.some_spec,
  exact zmod.val_cast_of_lt h.some_spec.some
end

end is_cyclotomic_extension

section gal

variables [field L] (hμ : is_primitive_root μ n) [algebra K L]
          [is_cyclotomic_extension {n} K L] (h : irreducible (cyclotomic n K)) {K}

/-- `is_cyclotomic_extension.aut_equiv_pow` repackaged in terms of `gal`.
Asserts that the Galois group of `cyclotomic n K` is equivalent to `(zmod n)ˣ`
if `cyclotomic n K` is irreducible in the base field. -/
noncomputable def gal_cyclotomic_equiv_units_zmod :
  (cyclotomic n K).gal ≃* (zmod n)ˣ :=
(alg_equiv.aut_congr (is_splitting_field.alg_equiv _ _)).symm.trans
(is_cyclotomic_extension.aut_equiv_pow L h)

/-- `is_cyclotomic_extension.aut_equiv_pow` repackaged in terms of `gal`.
Asserts that the Galois group of `X ^ n - 1` is equivalent to `(zmod n)ˣ`
if `cyclotomic n K` is irreducible in the base field. -/
noncomputable def gal_X_pow_equiv_units_zmod :
  (X ^ (n : ℕ) - 1).gal ≃* (zmod n)ˣ :=
(alg_equiv.aut_congr (is_splitting_field.alg_equiv _ _)).symm.trans
(is_cyclotomic_extension.aut_equiv_pow L h)

end gal
