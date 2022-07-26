/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import number_theory.legendre_symbol.add_character
import number_theory.legendre_symbol.zmod_char
import algebra.char_p.char_and_card

/-!
# Gauss sums

We define the Gauss sum associated to a multiplicative and an additive
character of a finite field and prove some results about them.

## Main definition

Let `R` be a finite commutative ring and let `R'` be another commutative ring.
If `χ` is a multiplicative character `R → R'` (type `mul_char R R'`) and `ψ`
is an additive character `R → R'` (type `add_char R R'`, which abbreviates
`(multiplicative R) →* R'`), then the *Gauss sum* of `χ` and `ψ` is `∑ a, χ a * ψ a`.

## Main results

Some important results are as follows.

* `char.gauss_sum_mul_gauss_sum_eq_card`: The product of the Gauss
  sums of `χ` and `ψ` and that of `χ⁻¹` and `ψ⁻¹` is the cardinality
  of the source ring `R` (if `χ` is nontrivial, `ψ` is primitive and `R` is a field).
* `char.gauss_sum_sq`: The square of the Gauss sum is `χ(-1)` times
  the cardinality of `R` if in addition `χ` is a quadratic character.
* `char.quad_gauss_sum_frob`: For a quadratic character `χ`, raising
  the Gauss sum to the `p`th power (where `p` is the characteristic of
  the target ring `R'`) multiplies it by `χ p`.
* `char.card_pow_card`: When `F` and `F'` are finite fields and `χ : F → F'`
  is a nontrivial quadratic character, then `(χ (-1) * #F)^(#F'/2) = χ (#F')`.
* `char.two_pow_card`: For every finite field `F` of odd characteristic,
  we have `2^(#F/2) = χ₈(#F)` in `F`.

This machinery can be used to derive (a generaliation of) the Law of
Quadratic Reciprocity.

## Tags

additive character, multiplicative character, Gauss sum
-/

namespace char

universes u v

open_locale big_operators

open add_char mul_char multiplicative

section gauss_sum_def

-- `R` is the domain of the characters
variables {R : Type u} [comm_ring R] [fintype R]
-- `R'` is the target of the characters
variables {R' : Type v} [comm_ring R']

/-!
### Definition and first properties
-/

/-- Definition of the Gauss sum associated to a multiplicative and an additive character. -/
def gauss_sum (χ : mul_char R R') (ψ : add_char R R') : R' := ∑ a, χ a * ψ (of_add a)

/-- Replacing `ψ` by `mul_shift ψ a` and multiplying the Gauss sum by `χ a` does not change it. -/
lemma gauss_sum_mul_shift (χ : mul_char R R') (ψ : add_char R R') (a : Rˣ) :
  χ a * gauss_sum χ (mul_shift ψ a) = gauss_sum χ ψ :=
begin
  simp only [gauss_sum, mul_shift, monoid_hom.coe_comp, function.comp_app, to_add_of_add,
             add_monoid_hom.to_multiplicative_apply_apply, add_monoid_hom.coe_mul_left],
  rw [finset.mul_sum],
  conv in (_ * (_ * _)) {rw [← mul_assoc, ← map_mul]},
  exact fintype.sum_bijective _ (units.mul_left_bijective a) _ _ (λ x, rfl),
end

end gauss_sum_def

/-!
### The product of two Gauss sums
-/

section gauss_sum_prod

-- In the following, we need `R` to be a finite field and `R'` to be a domain.
variables {R : Type u} [field R] [fintype R] {R' : Type v} [comm_ring R'] [is_domain R']

-- Two helper lemmas for `gauss_sum_mul_gauss_sum_eq_card` below
private
lemma gauss_sum_mul_aux₁ {χ : mul_char R R'} (hχ : is_nontrivial χ) (ψ : add_char R R') (b : R) :
  ∑ a, χ (a * b⁻¹) * ψ (of_add (a - b)) = ∑ c, χ c * ψ (of_add (b * (c - 1))) :=
begin
  cases eq_or_ne b 0 with hb hb,
  { -- case `b = 0`
    simp only [hb, inv_zero, mul_zero, mul_char.map_zero, zero_mul, finset.sum_const_zero,
               of_add_zero, monoid_hom.map_one, mul_one],
    exact hχ.sum_eq_zero.symm, },
  { -- case `b ≠ 0`
    symmetry,
    let lhs := λ c, χ c * ψ (of_add (b * (c - 1))),
    let rhs := λ a, χ (a * b⁻¹) * ψ (of_add (a - b)),
    have lr : ∀ x : R, lhs x = rhs (b * x) :=
    begin
      intro x,
      simp only [lhs, rhs],
      rw [mul_assoc, mul_comm x, ← mul_assoc, mul_inv_cancel hb, one_mul, mul_sub, mul_one],
    end,
    exact fintype.sum_bijective _ (mul_left_bijective₀ b hb) lhs rhs lr, },
end

private
lemma gauss_sum_mul_aux₂ [decidable_eq R] (ψ : add_char R R') (b : R) (hψ : is_primitive ψ) :
  ∑ (x : R), ψ (of_add (x * (b - 1))) = if b = 1 then fintype.card R else 0 :=
begin
  split_ifs,
  { -- case `b = 1`
    simp only [h, sub_self, mul_zero, of_add_zero, map_one, finset.sum_const, nat.smul_one_eq_coe],
    refl, },
  { -- case `b ≠ 1`
    conv in (_ * _) {rw mul_comm},
    exact sum_eq_zero_of_is_nontrivial (hψ (b - 1) (sub_ne_zero_of_ne h)), },
end

/-- We have `gauss_sum χ ψ * gauss_sum χ⁻¹ (mul_shift ψ (-1)) = fintype.card R`
when `χ` is nontrivial and `ψ` is primitive (and `R` is a field). -/
lemma gauss_sum_mul_gauss_sum_eq_card  {χ : mul_char R R'} (hχ : is_nontrivial χ)
  {ψ : add_char R R'} (hψ : is_primitive ψ) :
  gauss_sum χ ψ * gauss_sum χ⁻¹ (mul_shift ψ (-1)) = fintype.card R :=
begin
  simp only [gauss_sum, mul_shift, monoid_hom.coe_comp, function.comp_app,
             add_monoid_hom.to_multiplicative_apply_apply, finset.mul_sum,
             add_monoid_hom.coe_mul_left, neg_mul, one_mul, of_add_neg, of_add_to_add],
  simp_rw [finset.sum_mul],
  conv in (_ * _ * (_ * _)) { rw [mul_mul_mul_comm, inv_apply' χ, ← map_mul χ, ← map_mul ψ] },
  let lhs : R → R' := λ b, ∑ (a : R), χ (a * b⁻¹) * ψ (of_add (a - b)),
  let rhs : R → R' := λ b, ∑ (c : R), χ c * ψ (of_add (b * (c - 1))),
  have h : ∑ (x y : R), χ (y * x⁻¹) * ψ ((of_add y) * (of_add x)⁻¹) = ∑ x, lhs x :=
  by {simp_rw [lhs, sub_eq_add_neg], refl},
  rw [h, @finset.sum_congr R' R finset.univ finset.univ lhs rhs _ rfl
             (λ (b : R) (h : b ∈ finset.univ), (gauss_sum_mul_aux₁ hχ ψ) b)],
  simp only [rhs],
  rw [finset.sum_comm],
  classical, -- to get `[decidable_eq R]` for `gauss_sum_mul_aux₂`
  conv {to_lhs, congr, skip, funext, rw [← finset.mul_sum, gauss_sum_mul_aux₂ _ _ hψ]},
  simp only [mul_ite, mul_zero, finset.sum_ite_eq', finset.mem_univ, map_one, one_mul, if_true],
end

/-- When `χ` is a nontrivial quadratic character, then the square of `gauss_sum χ ψ`
is `χ (-1)` times the cardinality of `R`. -/
lemma gauss_sum_sq  {χ : mul_char R R'} (hχ₁ : is_nontrivial χ) (hχ₂ : is_quadratic χ)
  {ψ : add_char R R'} (hψ : is_primitive ψ) :
  (gauss_sum χ ψ) ^ 2 = χ (-1) * fintype.card R :=
begin
  rw [pow_two],
  nth_rewrite 1 ← gauss_sum_mul_shift _ _ (-1 : Rˣ),
  rw [(by norm_num : ((-1 : Rˣ) : R) = -1), ← mul_assoc, mul_comm _ (χ (-1)), mul_assoc],
  nth_rewrite 2 ← hχ₂.inv,
  rw [gauss_sum_mul_gauss_sum_eq_card hχ₁ hψ],
end

end gauss_sum_prod

/-!
### Gauss sums and Frobenius
-/

section gauss_sum_frob

variables {R : Type u} [comm_ring R] [fintype R] {R' : Type v} [comm_ring R']
-- We assume that the target ring `R'` has prime characteristic `p`.
variables (p : ℕ) [fp : fact p.prime] [hch : char_p R' p]
include fp hch

/-- When `R'` has prime characteristic `p`, then the `p`th power of the Gauss sum
of `χ` and `ψ` is the Gauss sum of `χ^p` and `mul_shift ψ p`. -/
lemma gauss_sum_frob (χ : mul_char R R') (ψ : add_char R R') :
   gauss_sum χ ψ ^ p = gauss_sum (χ ^ p) (mul_shift ψ p) :=
begin
  rw [← frobenius_def, gauss_sum, gauss_sum, map_sum],
  simp_rw [pow_apply' χ fp.1.pos, map_mul, frobenius_def, mul_shift_spec'],
end

/-- For a quadratic character `χ` and when the characteristic `p` of the target ring
is a unit in the source ring, the `p`th power of the Gauss sum of`χ` and `ψ` is
`χ p` times the original Gauss sum. -/
lemma quad_gauss_sum_frob (hp : is_unit (p : R)) {χ : mul_char R R'} (hχ : is_quadratic χ)
  (ψ : add_char R R') :
  gauss_sum χ ψ ^ p = χ p * gauss_sum χ ψ :=
begin
  letI := @char_p.nontrivial_of_char_ne_one R' _ _ fp.1.ne_one hch,
  have h : (1 : mul_char R R') p = 1 := by rw [← is_unit.unit_spec hp, one_apply_coe],
  rw [gauss_sum_frob, hχ.pow_char p, ← gauss_sum_mul_shift χ ψ hp.unit, ← mul_assoc,
      is_unit.unit_spec, ← pow_two, ← pow_apply' _ (by norm_num : 0 < 2), hχ.sq_eq_one,
      h, one_mul],
end

/-- Similar to the above, but with `p^n` in place of `p` -/
lemma quad_gauss_sum_frob_iter (n : ℕ) (hp : is_unit (p : R))
  {χ : mul_char R R'} (hχ : is_quadratic χ) (ψ : add_char R R') :
  gauss_sum χ ψ ^ (p ^ n) = χ (p ^ n) * gauss_sum χ ψ :=
begin
  induction n with n ih,
  { rw [pow_zero, pow_one, pow_zero, mul_char.map_one, one_mul], },
  { rw [pow_succ, mul_comm p, pow_mul, ih, mul_pow, quad_gauss_sum_frob _ hp hχ,
        ← mul_assoc, pow_succ, mul_comm (p : R), map_mul,
        ← pow_apply' χ fp.1.pos (p ^ n), hχ.pow_char p], },
end

end gauss_sum_frob

/-!
### Values of quadratic characters
-/

section gauss_sum_values

variables {R : Type u} [comm_ring R] [fintype R] {R' : Type v} [comm_ring R'] [is_domain R']

/-- If the square of the Gauss sum of a quadratic character is `χ (-1) * #R`,
then we get, for all `n : ℕ`, the relation `(χ(-1) * #R) ^ (p^n/2) = χ(p^n)`,
where `p` is the (odd) characteristic of the target ring `R'`.
This version can be used when `R` is not a field, e.g., `ℤ/8ℤ`. -/
lemma card_pow_char_pow {χ : mul_char R R'} (hχ : is_quadratic χ) (ψ : add_char R R') (p n : ℕ)
  [fp : fact p.prime] [hch : char_p R' p] (hp : is_unit (p : R)) (hp' : p ≠ 2)
  (hg : (gauss_sum χ ψ) ^ 2 = χ (-1) * fintype.card R) :
  (χ (-1) * fintype.card R) ^ (p ^ n / 2) = χ (p ^ n) :=
begin
  have h₀ : gauss_sum χ ψ ≠ 0 :=
  begin
    intro hf,
    simp [hf] at hg,
    have hh := or.resolve_left hg (is_unit.map χ is_unit_one.neg).ne_zero,
    rw [← show ((fintype.card R : ℤ) : R') = fintype.card R, by norm_cast] at hh,
    exact not_is_unit_prime_of_dvd_card p
            (int.coe_nat_dvd.mp ((char_p.int_cast_eq_zero_iff R' p (fintype.card R)).mp hh)) hp,
  end,
  have h₁ := quad_gauss_sum_frob_iter p n hp hχ ψ,
  have h₂ := nat.odd_iff.mp (odd.pow (or.resolve_left (nat.prime.eq_two_or_odd' fp.1) hp')),
  rw [← nat.div_add_mod (p ^ n) 2, h₂, pow_succ'] at h₁,
  rw [← mul_right_cancel₀ h₀ h₁, pow_mul, hg],
end

/-- When `F` and `F'` are finite fields and `χ : F → F'` is a nontrivial quadratic character,
then `(χ (-1) * #F)^(#F'/2) = χ (#F')`. -/
lemma card_pow_card {F : Type} [field F] [fintype F] {F' : Type} [field F'] [fintype F']
  {χ : mul_char F F'} (hχ₁ : is_nontrivial χ) (hχ₂ : is_quadratic χ)
  (hch₁ : ring_char F' ≠ ring_char F) (hch₂ : ring_char F' ≠ 2) :
  (χ (-1) * fintype.card F) ^ (fintype.card F' / 2) = χ (fintype.card F') :=
begin
  obtain ⟨n, hp, hc⟩ := finite_field.card F (ring_char F),
  obtain ⟨n', hp', hc'⟩ := finite_field.card F' (ring_char F'),
  let ψ := primitive_char_finite_field F F' hch₁,
  let FF' := cyclotomic_field ψ.n F',
  have hchar := -- `ring_char FF' = ring_char F'`
    ring_char.eq_iff.mpr ((algebra.char_p_iff F' FF' (ring_char F')).mp (ring_char.char_p F')),
  haveI : fact (ring_char FF').prime := by { rw ← hchar at hp', exact ⟨hp'⟩ },
  let χ' := χ.ring_hom_comp (algebra_map F' FF'),
  have hχ' : ∀ x : F, (algebra_map F' FF') (χ x) = χ' x := λ x, rfl,
  have hχ₁' := hχ₁.comp (algebra_map F' FF').injective,
  have hχ₂' := hχ₂.comp (algebra_map F' FF'),
  have hpu : is_unit (ring_char FF' : F) :=
  begin
    rw [hchar],
    haveI := invertible_of_ring_char_not_dvd
              (λ hf, hch₁ ((nat.prime_dvd_prime_iff_eq hp hp').mp hf).symm),
    exact is_unit_of_invertible (ring_char F' : F),
  end,
  apply_fun algebra_map F' FF' using (algebra_map F' FF').injective,
  rw [map_pow, map_mul, hχ', hχ', map_nat_cast, hc', ← hchar,
      card_pow_char_pow hχ₂' ψ.char (ring_char FF') n' hpu (ne_of_eq_of_ne hchar hch₂)
        (gauss_sum_sq hχ₁' hχ₂' ψ.prim),
      nat.cast_pow],
end

end gauss_sum_values

/-!
### The quadratic character of 2

This section proves the following result.

For every finite field `F` of odd characteristic, we have `2^(#F/2) = χ₈(#F)` in `F`.
This can be used to show that the quadratic character of `F` takes the value
`χ₈(#F)` at `2`.

The proof uses the Gauss sum of `χ₈` and a primitive additive character on `ℤ/8ℤ`;
in this way, the result is reduced to `card_pow_char_pow`.
-/

section gauss_sum_two

/-- Expand a sum over `ℤ/8ℤ` -/
private
lemma sum8 {R : Type*} [add_comm_monoid R] (f : (zmod 8) → R) :
  ∑ a, f a = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 :=
begin
  have h : ∀ (f : (fin 8) → R), ∑ a, f a = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 :=
  begin
    intro f',
    repeat {rw add_assoc},
    simp only [fin.sum_univ_succ, fintype.univ_of_subsingleton, fin.mk_eq_subtype_mk,
               fin.mk_zero, finset.sum_singleton],
    congr,
  end,
  exact h f,
end

open zmod

/-- For every finite field `F` of odd characteristic, we have `2^(#F/2) = χ₈(#F)` in `F`. -/
lemma two_pow_card {F : Type} [fintype F] [field F] (hF : ring_char F ≠ 2) :
  (2 : F) ^ (fintype.card F / 2) = χ₈ (fintype.card F) :=
begin
  have hp2 : ∀ (n : ℕ), (2 ^ n : F) ≠ 0 := λ n, pow_ne_zero n (ring.two_ne_zero hF),
  have h4nz : (4 : F) ≠ 0 :=
  by { have h := hp2 2, norm_num at h, },
  have h8nz : ((8 : ℕ) : F) ≠ 0 :=
  by { have h := hp2 3, norm_num at h, exact_mod_cast h, },
  obtain ⟨n, hp, hc⟩ := finite_field.card F (ring_char F),

  -- we work in `FF`, the eighth cyclotomic field extension of `F`
  haveI := h8nz,
  let FF := (polynomial.cyclotomic 8 F).splitting_field,
  letI  : polynomial.is_splitting_field F FF _ :=
    polynomial.is_splitting_field.splitting_field (polynomial.cyclotomic 8 F),
  haveI : finite_dimensional F FF :=
    polynomial.is_splitting_field.finite_dimensional FF (polynomial.cyclotomic 8 F),
  haveI : fintype FF := finite_dimensional.fintype_of_fintype F FF,
  have hchar := -- `ring_char FF = ring_char F`
    ring_char.eq_iff.mpr ((algebra.char_p_iff F FF (ring_char F)).mp (ring_char.char_p F)),
  have FFp : (ring_char FF).prime := by { rw hchar, exact hp },
  have hFF := ne_of_eq_of_ne hchar hF, -- `ring_char FF ≠ 2`
  have hu : is_unit (ring_char FF : zmod 8) :=
  by exact_mod_cast units.is_unit (unit_of_coprime _
       ((nat.prime.coprime_iff_not_dvd FFp).mpr $
          λ hf, hFF $ (nat.prime_dvd_prime_iff_eq FFp nat.prime_two).mp
                    $ nat.prime.dvd_of_dvd_pow FFp $ hf.trans (by norm_num : (8 ∣ 2 ^ 3)))),

  -- there is a primitive additive character `ℤ/8ℤ → FF`, sending `a + 8ℤ ↦ τ^a`
  -- with a primitive eighth root of unity `τ`
  let ψ₈ := primitive_zmod_char 8 F h8nz,
  let τ : FF := ψ₈.char (of_add 1),
  have τ_spec : τ ^ 4 = -1 :=
  begin
    change (zmod_char 8 _ (of_add 1)) ^ 4 = _,
    simp only [zmod_char, monoid_hom.coe_mk, to_add_of_add],
    haveI : ne_zero (((8 : pnat) : ℕ) : F) :=
    by { change ne_zero ((8 : ℕ) : F), exact ne_zero_iff.mpr h8nz },
    haveI : ne_zero (((8 : pnat) : ℕ) : FF) := ne_zero.of_no_zero_smul_divisors F _ 8,
    change (is_cyclotomic_extension.zeta 8 F (cyclotomic_field 8 F) ^ _) ^ 4 = _,
    haveI : fact (1 < 8) := ⟨by norm_num⟩,
    rw [zmod.val_one, pow_one],
    let hζ := is_cyclotomic_extension.zeta_spec 8 F (cyclotomic_field 8 F),
    set ζ := is_cyclotomic_extension.zeta 8 F (cyclotomic_field 8 F),
    have h8 : (ζ ^ 4) * (ζ ^ 4) = 1 := by { rw [← pow_add], exact hζ.pow_eq_one },
    have h4 : ζ ^ 4 ≠ 1 := by { intro hf, have hf' := hζ.dvd_of_pow_eq_one _ hf, norm_num at hf' },
    exact or.resolve_left (mul_self_eq_one_iff.mp h8) h4,
  end,
  have ψ₈_spec : ∀ (a : zmod 8), ψ₈.char (of_add a) = τ ^ a.val :=
  begin
    intro a,
    nth_rewrite 0 [← zmod.nat_cast_zmod_val a],
    rw [← nat.smul_one_eq_coe],
    change ψ₈.char ((of_add 1) ^ a.val) = _,
    rw [map_pow],
  end,

  -- we consider `χ₈` as a multiplicative character `ℤ/8ℤ → FF`
  let χ := χ₈.ring_hom_comp (algebra_map ℤ FF),
  have χ_spec : ∀ m : zmod 8, χ m = χ₈ m :=
    λ m, by rw [ring_hom_comp_apply, ring_hom.eq_int_cast],
  have hχ : χ (-1) = 1 :=
  by { rw [(dec_trivial : (-1 : zmod 8) = 7), χ_spec 7, χ₈_apply],
       simp only [matrix.cons_vec_bit1_eq_alt1, matrix.cons_append, matrix.cons_vec_alt1,
                  matrix.cons_val_one, matrix.head_cons, int.cast_one], },
  have hq : is_quadratic χ := is_quadratic.comp is_quadratic_χ₈ (algebra_map ℤ FF),

  -- we now show that the Gauss sum of `χ` and `ψ₈` has the relevant property
  have hg : gauss_sum χ ψ₈.char ^ 2 = χ (-1) * (fintype.card (zmod 8)) :=
  begin
    have hs := sum8 (λ (x : zmod 8), (χ₈ x : FF) * τ ^ x.val),
    simp only at hs,
    rw [hχ, one_mul, card, gauss_sum],
    simp_rw [χ_spec, ψ₈_spec],
    rw [hs],
    simp only [χ₈_apply, matrix.cons_val_zero, int.cast_zero, zero_mul, matrix.cons_val_one,
               matrix.head_cons, int.cast_one, one_mul, zero_add, matrix.cons_vec_bit0_eq_alt0,
               matrix.cons_append, matrix.cons_vec_alt0, add_zero, matrix.cons_vec_bit1_eq_alt1,
               matrix.cons_vec_alt1, int.cast_neg, neg_mul, ring_hom.eq_int_cast],
    calc (τ ^ 1 + (- τ ^ 3) + (- τ ^ 5) + τ ^ 7) ^ 2
          = 8 + (τ ^ 4 + 1) * (τ ^ 10 - 2 * τ ^ 8 - 2 * τ ^ 6 + 6 * τ ^ 4 + τ ^ 2 - 8) : by ring
      ... = 8 + (-1 + 1) * _  : by rw τ_spec
      ... = 8                 : by ring
      ... = (8 : ℕ)           : by norm_cast,
  end,

  -- this allows us to apply `card_pow_char_pow` to our situation
  haveI : fact _ := ⟨FFp⟩,
  have h := card_pow_char_pow hq ψ₈.char (ring_char FF) n hu hFF hg,
  rw [card, hchar, hχ, one_mul, ← hc, ← nat.cast_pow (ring_char F), ← hc, χ_spec] at h,

  -- finally, we change `2` to `8` on the left hand side
  have h28 : (2 : F) ^ (fintype.card F / 2) = 8 ^ (fintype.card F / 2) :=
  by rw [(by norm_num : (8 : F) = 4 * 2), mul_pow,
         (finite_field.is_square_iff hF h4nz).mp ⟨2, by norm_num⟩, one_mul],
  rw [h28],
  apply_fun algebra_map F FF using (algebra_map F FF).injective,
  simp only [map_pow, map_bit0, map_one, ring_hom.map_int_cast],
  exact_mod_cast h,
end

end gauss_sum_two

end char
