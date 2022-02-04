/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import number_theory.cyclotomic.zeta
import ring_theory.polynomial.cyclotomic.eval
import field_theory.polynomial_galois_group
/-!
# Galois group of cyclotomic extensions

In this file, we show the relationship between the Galois group of`K(ζₙ)` and `(zmod n)ˣ`;
it is always a subgroup, and if the `n`th cyclotomic polynomial is irreducible, they are isomorphic.

# Main results

* `is_cyclotomic_extension.aut_to_pow_injective`: `is_primitive_root.aut_to_pow` is injective
  in the case that it's considered over a cyclotomic field extension, where `n` does not divide
  the characteristic of K. As a corollary, $Gal(K(ζₙ)/K)$ is abelian.
* `is_cyclotomic_extension.aut_equiv_pow`: If, additionally, the `n`th cyclotomic polynomial is
  irreducible in K, then `aut_to_pow` is a `mul_equiv`.
* `gal_{X_pow/cyclotomic}_equiv_units_zmod`: Repackage `aut_to_pow` in terms of `polynomial.gal`.

# References

* https://kconrad.math.uconn.edu/blurbs/galoistheory/cyclotomic.pdf

# TODO

* `zeta_pow_power_basis` is not sufficiently general; the correct solution is some
  `power_basis.map_conjugate`, but figuring out the exact correct assumptions + proof for this is
  mathematically nontrivial. (Current thoughts: the ideal of polynomials with α as a root is equal
  to the ideal of polynomials with β as a root, which, in an integrally closed domain, reduces
  to the usual condition that they are the roots of each others' minimal polynomials.)

-/

local attribute [instance] pnat.fact_pos

variables {L : Type*} [field L] {μ : L} (n : ℕ+) (hμ : is_primitive_root μ n)
          (K : Type*) [field K] [algebra K L] [is_cyclotomic_extension {n} K L]

local notation `ζ` := is_cyclotomic_extension.zeta n K L

open polynomial ne_zero

namespace is_cyclotomic_extension

lemma aut_to_pow_injective [ne_zero ((n : ℕ) : K)] : function.injective $
    (@zeta_primitive_root n K L _ _ _ _ _ $ of_no_zero_smul_divisors K L n).aut_to_pow K :=
begin
  intros f g hfg,
  apply_fun units.val at hfg,
  simp only [is_primitive_root.coe_aut_to_pow_apply, units.val_eq_coe] at hfg,
  generalize_proofs hf' hg' at hfg,
  have hf := hf'.some_spec,
  have hg := hg'.some_spec,
  dsimp only [alg_equiv.to_ring_equiv_eq_coe, ring_equiv.to_ring_hom_eq_coe,
              ring_equiv.coe_to_ring_hom, alg_equiv.coe_ring_equiv] at hf hg,
  generalize_proofs hζ at hf hg,
  suffices : f hζ.to_roots_of_unity = g hζ.to_roots_of_unity,
  { apply alg_equiv.coe_alg_hom_injective,
    apply (zeta.power_basis n K L).alg_hom_ext,
    exact this },
  rw zmod.eq_iff_modeq_nat at hfg,
  refine (hf.trans _).trans hg.symm,
  rw [←roots_of_unity.coe_pow _ hf'.some, ←roots_of_unity.coe_pow _ hg'.some],
  congr' 1,
  rw [pow_eq_pow_iff_modeq],
  convert hfg,
  rw [hζ.eq_order_of],
  rw [←hζ.coe_to_roots_of_unity_coe] {occs := occurrences.pos [2]},
  rw [order_of_units, order_of_subgroup]
end

-- As a corollary, cyclotomic extensions are abelian extensions!
noncomputable instance [ne_zero ((n : ℕ) : K)] : comm_group (L ≃ₐ[K] L) :=
function.injective.comm_group _ (aut_to_pow_injective n K) (map_one _)
  (map_mul _) (map_inv _) (map_div _)

variables (L)

/-- The power basis given by `ζ ^ t`. -/
@[simps] noncomputable def zeta_pow_power_basis [ne_zero ((n : ℕ) : K)] (t : (zmod n)ˣ) :
  power_basis K L :=
begin
  haveI := of_no_zero_smul_divisors K L n,
  refine power_basis.map (algebra.adjoin.power_basis $ integral {n} K L $ ζ ^ (t : zmod n).val) _,
  refine (subalgebra.equiv_of_eq _ _ (adjoin_primitive_root_eq_top n _ _)).trans algebra.top_equiv,
  exact (zeta_primitive_root n K L).pow_of_coprime _ (zmod.val_coe_unit_coprime t),
end

variables (h : irreducible (cyclotomic n K))

include h

/-- The `mul_equiv` that takes an automorphism to the power of μ that μ gets mapped to under it.
    A stronger version of `is_primitive_root.aut_to_pow`. -/
@[simps {attrs := []}] noncomputable def aut_equiv_pow [ne_zero ((n : ℕ) : K)] :
  (L ≃ₐ[K] L) ≃* (zmod n)ˣ :=
let hn := of_no_zero_smul_divisors K L n in by exactI
{ inv_fun := λ x, (zeta.power_basis n K L).equiv_of_minpoly (zeta_pow_power_basis L n K x)
  begin
    simp only [zeta.power_basis_gen, zeta_pow_power_basis_gen],
    have hr := is_primitive_root.minpoly_eq_cyclotomic_of_irreducible
               ((zeta_primitive_root n K L).pow_of_coprime _ (zmod.val_coe_unit_coprime x)) h,
    exact ((zeta_primitive_root n K L).minpoly_eq_cyclotomic_of_irreducible h).symm.trans hr
  end,
  left_inv := λ f, begin
    simp only [monoid_hom.to_fun_eq_coe],
    apply alg_equiv.coe_alg_hom_injective,
    apply (zeta.power_basis n K L).alg_hom_ext,
    simp only [alg_equiv.coe_alg_hom, alg_equiv.map_pow],
    rw power_basis.equiv_of_minpoly_gen,
    simp only [zeta_pow_power_basis_gen, zeta.power_basis_gen, is_primitive_root.aut_to_pow_spec],
  end,
  right_inv := λ x, begin
    simp only [monoid_hom.to_fun_eq_coe],
    generalize_proofs _ hζ _ h,
    have key := hζ.aut_to_pow_spec K ((zeta.power_basis n K L).equiv_of_minpoly
                                      (zeta_pow_power_basis L n K x) h),
    have := (zeta.power_basis n K L).equiv_of_minpoly_gen,
    rw zeta.power_basis_gen at this {occs := occurrences.pos [2]},
    rw [this, zeta_pow_power_basis_gen] at key,
    rw ← hζ.coe_to_roots_of_unity_coe at key {occs := occurrences.pos [1, 3]},
    simp only [←coe_coe, ←roots_of_unity.coe_pow] at key,
    replace key := roots_of_unity.coe_injective key,
    rw [pow_eq_pow_iff_modeq, ←order_of_subgroup, ←order_of_units, hζ.coe_to_roots_of_unity_coe,
        ←(zeta_primitive_root n K L).eq_order_of, ←zmod.eq_iff_modeq_nat] at key,
    simp only [zmod.nat_cast_val, zmod.cast_id', id.def] at key,
    exact units.ext key
  end,
  .. (zeta_primitive_root n K L).aut_to_pow K }

end is_cyclotomic_extension

open is_cyclotomic_extension
.
namespace is_primitive_root

include hμ

/-- Takes a primitive root `μ` to the aut that sends `is_cyclotomic_extension.zeta` to `μ`. -/
noncomputable def from_zeta_aut (h : irreducible (cyclotomic n K)) [ne_zero ((n : ℕ) : K)] :
  L ≃ₐ[K] L :=
have _ := of_no_zero_smul_divisors K L n, by exactI
let hζ := (zeta_primitive_root n K L).eq_pow_of_pow_eq_one hμ.pow_eq_one n.pos in
(aut_equiv_pow L n K h).symm $ zmod.unit_of_coprime hζ.some $
((zeta_primitive_root n K L).pow_iff_coprime n.pos hζ.some).mp $ hζ.some_spec.some_spec.symm ▸ hμ

lemma from_zeta_aut_spec (h : irreducible (cyclotomic n K)) [ne_zero ((n : ℕ) : K)] :
  ((from_zeta_aut n hμ K h) ζ) = μ :=
begin
  simp only [from_zeta_aut, exists_prop, aut_equiv_pow_symm_apply, ←zeta.power_basis_gen,
             power_basis.equiv_of_minpoly_gen, zeta_pow_power_basis_gen, zmod.coe_unit_of_coprime],
  generalize_proofs hζ,
  convert hζ.some_spec.2,
  exact zmod.val_cast_of_lt hζ.some_spec.1
end

end is_primitive_root

section gal

local attribute [instance] splitting_field_X_pow_sub_one splitting_field_cyclotomic

/-- `is_cyclotomic_extension.aut_equiv_pow` repackaged in terms of `gal`. Asserts that the
Galois group of `cyclotomic n K` is equivalent to `(zmod n)ˣ` if `n` does not divide the
characteristic of `K`, and `cyclotomic n K` is irreducible in the base field. -/
noncomputable def gal_cyclotomic_equiv_units_zmod [ne_zero ((n : ℕ) : K)]
  (h : irreducible (cyclotomic n K)) : (cyclotomic n K).gal ≃* (zmod n)ˣ :=
(alg_equiv.aut_congr (is_splitting_field.alg_equiv _ _)).symm.trans
(is_cyclotomic_extension.aut_equiv_pow L n K h)

/-- `is_cyclotomic_extension.aut_equiv_pow` repackaged in terms of `gal`. Asserts that the
Galois group of `X ^ n - 1` is equivalent to `(zmod n)ˣ` if `n` does not divide the characteristic
of `K`, and `cyclotomic n K` is irreducible in the base field. -/
noncomputable def gal_X_pow_equiv_units_zmod [ne_zero ((n : ℕ) : K)]
  (h : irreducible (cyclotomic n K)) : (X ^ (n : ℕ) - 1).gal ≃* (zmod n)ˣ :=
(alg_equiv.aut_congr (is_splitting_field.alg_equiv _ _)).symm.trans
(is_cyclotomic_extension.aut_equiv_pow L n K h)

end gal
