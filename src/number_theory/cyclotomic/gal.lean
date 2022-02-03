import number_theory.cyclotomic.zeta
import ring_theory.polynomial.cyclotomic.eval
import field_theory.polynomial_galois_group
/-!
# Galois group of cyclotomic extensions

In this file, we show the relationship between the Galois group of`K(ζₙ)` and `(zmod n)ˣ`;
it is always a subgroup, and if the `n`th cyclotomic polynomial is irreducible, they are isomorphic.

# Main results

* `is_primitive_root.aut_to_pow`: the monoid hom that takes an automorphism of a ring to the power
  it sends that specific primitive root, as a member of `(zmod n)ˣ`.
* `is_cyclotomic_extension.aut_to_pow_injective`: `is_primitive_root.aut_to_pow` is injective
  in the case that it's considered over a cyclotomic field extension, where `n` does not divide
  the characteristic of K. As a corollary, $Gal(K(ζₙ)/K)$ is abelian.
* `is_cyclotomic_extension.aut_equiv_pow`: If, additionally, the `n`th cyclotomic polynomial is
  irreducible in K, then `aut_to_pow` is a `mul_equiv`.
* `gal_{X_pow/cyclotomic}_equiv_units_zmod`: Repackage `aut_to_pow` in terms of `polynomial.gal`.

# References

* https://kconrad.math.uconn.edu/blurbs/galoistheory/cyclotomic.pdf

-/

local attribute [instance] pnat.fact_pos
local attribute [simp] ring_equiv.to_ring_hom_eq_coe

section ring

variables {S : Type*} [comm_ring S] [is_domain S] {μ : S} {n : ℕ+} (hμ : is_primitive_root μ n)
          (R : Type*) [comm_ring R] [algebra R S]

/-- The `monoid_hom` that takes an automorphism to the power of μ that μ gets mapped to under it. -/
@[simps {attrs := []}] noncomputable def is_primitive_root.aut_to_pow  :
  (S ≃ₐ[R] S) →* (zmod n)ˣ :=
let μ' := hμ.to_roots_of_unity in
have ho : order_of μ' = n :=
  by rw [hμ.eq_order_of, ←hμ.coe_to_roots_of_unity_coe, order_of_units, order_of_subgroup],
monoid_hom.to_hom_units
{ to_fun := λ σ, (map_root_of_unity_eq_pow_self σ.to_alg_hom μ').some,
  map_one' := begin
    generalize_proofs h1,
    have h := h1.some_spec,
    dsimp only [alg_equiv.one_apply, alg_equiv.to_ring_equiv_eq_coe, ring_equiv.to_ring_hom_eq_coe,
                ring_equiv.coe_to_ring_hom, alg_equiv.coe_ring_equiv] at *,
    replace h : μ' = μ' ^ h1.some := roots_of_unity.coe_injective
                 (by simpa only [roots_of_unity.coe_pow] using h),
    rw ←pow_one μ' at h {occs := occurrences.pos [1]},
    rw [←@nat.cast_one $ zmod n, zmod.nat_coe_eq_nat_coe_iff, ←ho, ←pow_eq_pow_iff_modeq μ', h]
  end,
  map_mul' := begin
    generalize_proofs hxy' hx' hy',
    have hxy := hxy'.some_spec,
    have hx := hx'.some_spec,
    have hy := hy'.some_spec,
    dsimp only [alg_equiv.to_ring_equiv_eq_coe, ring_equiv.to_ring_hom_eq_coe,
                ring_equiv.coe_to_ring_hom, alg_equiv.coe_ring_equiv, alg_equiv.mul_apply] at *,
    replace hxy : x (↑μ' ^ hy'.some) = ↑μ' ^ hxy'.some := hy ▸ hxy,
    rw x.map_pow at hxy,
    replace hxy : ((μ' : S) ^ hx'.some) ^ hy'.some = μ' ^ hxy'.some := hx ▸ hxy,
    rw ←pow_mul at hxy,
    replace hxy : μ' ^ (hx'.some * hy'.some) = μ' ^ hxy'.some := roots_of_unity.coe_injective
                                           (by simpa only [roots_of_unity.coe_pow] using hxy),
    rw [←nat.cast_mul, zmod.nat_coe_eq_nat_coe_iff, ←ho, ←pow_eq_pow_iff_modeq μ', hxy]
  end }

@[simp] lemma is_primitive_root.aut_to_pow_spec (f : S ≃ₐ[R] S) :
  μ ^ (hμ.aut_to_pow R f : zmod n).val = f μ :=
begin
  rw is_primitive_root.coe_aut_to_pow_apply,
  generalize_proofs h,
  have := h.some_spec,
  dsimp only [alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom] at this,
  refine (_ : ↑hμ.to_roots_of_unity ^ _ = _).trans this.symm,
  rw [←roots_of_unity.coe_pow, ←roots_of_unity.coe_pow],
  congr' 1,
  rw [pow_eq_pow_iff_modeq, ←order_of_subgroup, ←order_of_units, hμ.coe_to_roots_of_unity_coe,
      ←hμ.eq_order_of, zmod.val_nat_cast],
  exact nat.mod_modeq _ _
end

end ring

section field

variables {L : Type*} [field L] {μ : L} {n : ℕ+} (hμ : is_primitive_root μ n)
          (K : Type*) [field K] [algebra K L]

local notation `ζ` := is_cyclotomic_extension.zeta n K L

variables (n) [is_cyclotomic_extension {n} K L]

open is_cyclotomic_extension ne_zero

lemma is_cyclotomic_extension.aut_to_pow_injective [ne_zero ((n : ℕ) : K)] : function.injective $
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
noncomputable example [ne_zero ((n : ℕ) : K)] : comm_group (L ≃ₐ[K] L) :=
function.injective.comm_group _ (is_cyclotomic_extension.aut_to_pow_injective n K) (map_one _)
  (map_mul _) (map_inv _) (map_div _)

variables (L)

-- TODO: do this properly with a `power_basis.map_conjugate`
/-- The power basis given by `ζ ^ t`. -/
@[simps] noncomputable def zeta_pow_power_basis [ne_zero ((n : ℕ) : K)] (t : (zmod n)ˣ) :
  power_basis K L :=
begin
  haveI := ne_zero.of_no_zero_smul_divisors K L n,
  refine power_basis.map (algebra.adjoin.power_basis $ integral {n} K L $ ζ ^ (t : zmod n).val) _,
  refine (subalgebra.equiv_of_eq _ _
      (is_cyclotomic_extension.adjoin_primitive_root_eq_top n _ $ _)).trans
      algebra.top_equiv,
  exact (zeta_primitive_root n K L).pow_of_coprime _ (zmod.val_coe_unit_coprime t),
end

open polynomial

/-- The `mul_equiv` that takes an automorphism to the power of μ that μ gets mapped to under it.
    A stronger version of `is_primitive_root.aut_to_pow`. -/
@[simps {attrs := []}] noncomputable def is_cyclotomic_extension.aut_equiv_pow
  [ne_zero ((n : ℕ) : K)] (h : irreducible (cyclotomic n K)) : (L ≃ₐ[K] L) ≃* (zmod n)ˣ :=
let hn := ne_zero.of_no_zero_smul_divisors K L n in by exactI
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

local attribute [instance] splitting_field_X_pow_sub_one splitting_field_cyclotomic

include L

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

end field
