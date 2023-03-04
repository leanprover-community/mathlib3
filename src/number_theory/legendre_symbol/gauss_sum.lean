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

* `gauss_sum_mul_gauss_sum_eq_card`: The product of the Gauss
  sums of `χ` and `ψ` and that of `χ⁻¹` and `ψ⁻¹` is the cardinality
  of the source ring `R` (if `χ` is nontrivial, `ψ` is primitive and `R` is a field).
* `gauss_sum_sq`: The square of the Gauss sum is `χ(-1)` times
  the cardinality of `R` if in addition `χ` is a quadratic character.
* `quad_gauss_sum_frob`: For a quadratic character `χ`, raising
  the Gauss sum to the `p`th power (where `p` is the characteristic of
  the target ring `R'`) multiplies it by `χ p`.
* `char.card_pow_card`: When `F` and `F'` are finite fields and `χ : F → F'`
  is a nontrivial quadratic character, then `(χ (-1) * #F)^(#F'/2) = χ (#F')`.
* `finite_field.two_pow_card`: For every finite field `F` of odd characteristic,
  we have `2^(#F/2) = χ₈(#F)` in `F`.

This machinery can be used to derive (a generalization of) the Law of
Quadratic Reciprocity.

## Tags

additive character, multiplicative character, Gauss sum
-/

universes u v

open_locale big_operators

open add_char mul_char

section gauss_sum_def

-- `R` is the domain of the characters
variables {R : Type u} [comm_ring R] [fintype R]
-- `R'` is the target of the characters
variables {R' : Type v} [comm_ring R']

/-!
### Definition and first properties
-/

/-- Definition of the Gauss sum associated to a multiplicative and an additive character. -/
def gauss_sum (χ : mul_char R R') (ψ : add_char R R') : R' := ∑ a, χ a * ψ a

/-- Replacing `ψ` by `mul_shift ψ a` and multiplying the Gauss sum by `χ a` does not change it. -/
lemma gauss_sum_mul_shift (χ : mul_char R R') (ψ : add_char R R') (a : Rˣ) :
  χ a * gauss_sum χ (mul_shift ψ a) = gauss_sum χ ψ :=
begin
  simp only [gauss_sum, mul_shift_apply, finset.mul_sum],
  simp_rw [← mul_assoc, ← map_mul],
  exact fintype.sum_bijective _ a.mul_left_bijective _ _ (λ x, rfl),
end

end gauss_sum_def

/-!
### The product of two Gauss sums
-/

section gauss_sum_prod

-- In the following, we need `R` to be a finite field and `R'` to be a domain.
variables {R : Type u} [field R] [fintype R] {R' : Type v} [comm_ring R'] [is_domain R']

-- A helper lemma for `gauss_sum_mul_gauss_sum_eq_card` below
-- Is this useful enough in other contexts to be public?
private
lemma gauss_sum_mul_aux {χ : mul_char R R'} (hχ : is_nontrivial χ) (ψ : add_char R R') (b : R) :
  ∑ a, χ (a * b⁻¹) * ψ (a - b) = ∑ c, χ c * ψ (b * (c - 1)) :=
begin
  cases eq_or_ne b 0 with hb hb,
  { -- case `b = 0`
    simp only [hb, inv_zero, mul_zero, mul_char.map_zero, zero_mul, finset.sum_const_zero,
               map_zero_one, mul_one],
    exact hχ.sum_eq_zero.symm, },
  { -- case `b ≠ 0`
    refine (fintype.sum_bijective _ (mul_left_bijective₀ b hb) _ _ $ λ x, _).symm,
    rw [mul_assoc, mul_comm x, ← mul_assoc, mul_inv_cancel hb, one_mul, mul_sub, mul_one] },
end

/-- We have `gauss_sum χ ψ * gauss_sum χ⁻¹ ψ⁻¹ = fintype.card R`
when `χ` is nontrivial and `ψ` is primitive (and `R` is a field). -/
lemma gauss_sum_mul_gauss_sum_eq_card  {χ : mul_char R R'} (hχ : is_nontrivial χ)
  {ψ : add_char R R'} (hψ : is_primitive ψ) :
  gauss_sum χ ψ * gauss_sum χ⁻¹ ψ⁻¹ = fintype.card R :=
begin
  simp only [gauss_sum, add_char.inv_apply, finset.sum_mul, finset.mul_sum, mul_char.inv_apply'],
  conv in (_ * _ * (_ * _))
    { rw [mul_mul_mul_comm, ← map_mul, ← map_add_mul, ← sub_eq_add_neg], },
  simp_rw gauss_sum_mul_aux hχ ψ,
  rw [finset.sum_comm],
  classical, -- to get `[decidable_eq R]` for `sum_mul_shift`
  simp_rw [← finset.mul_sum, sum_mul_shift _ hψ, sub_eq_zero, mul_ite, mul_zero],
  rw [finset.sum_ite_eq' finset.univ (1 : R)],
  simp only [finset.mem_univ, map_one, one_mul, if_true],
end

/-- When `χ` is a nontrivial quadratic character, then the square of `gauss_sum χ ψ`
is `χ(-1)` times the cardinality of `R`. -/
lemma gauss_sum_sq  {χ : mul_char R R'} (hχ₁ : is_nontrivial χ) (hχ₂ : is_quadratic χ)
  {ψ : add_char R R'} (hψ : is_primitive ψ) :
  (gauss_sum χ ψ) ^ 2 = χ (-1) * fintype.card R :=
begin
  rw [pow_two, ← gauss_sum_mul_gauss_sum_eq_card hχ₁ hψ, hχ₂.inv, mul_rotate'],
  congr,
  rw [mul_comm, ← gauss_sum_mul_shift _ _ (-1 : Rˣ), inv_mul_shift],
  refl,
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
of `χ` and `ψ` is the Gauss sum of `χ^p` and `ψ^p`. -/
lemma gauss_sum_frob (χ : mul_char R R') (ψ : add_char R R') :
  gauss_sum χ ψ ^ p = gauss_sum (χ ^ p) (ψ ^ p) :=
begin
  rw [← frobenius_def, gauss_sum, gauss_sum, map_sum],
  simp_rw [pow_apply' χ fp.1.pos, map_mul, frobenius_def],
  refl,
end

/-- For a quadratic character `χ` and when the characteristic `p` of the target ring
is a unit in the source ring, the `p`th power of the Gauss sum of`χ` and `ψ` is
`χ p` times the original Gauss sum. -/
lemma mul_char.is_quadratic.gauss_sum_frob (hp : is_unit (p : R)) {χ : mul_char R R'}
  (hχ : is_quadratic χ) (ψ : add_char R R') :
  gauss_sum χ ψ ^ p = χ p * gauss_sum χ ψ :=
by rw [gauss_sum_frob, pow_mul_shift, hχ.pow_char p, ← gauss_sum_mul_shift χ ψ hp.unit,
       ← mul_assoc, hp.unit_spec, ← pow_two, ← pow_apply' _ (by norm_num : 0 < 2),
       hχ.sq_eq_one, ← hp.unit_spec, one_apply_coe, one_mul]

/-- For a quadratic character `χ` and when the characteristic `p` of the target ring
is a unit in the source ring and `n` is a natural number, the `p^n`th power of the Gauss
sum of`χ` and `ψ` is `χ (p^n)` times the original Gauss sum. -/
lemma mul_char.is_quadratic.gauss_sum_frob_iter (n : ℕ) (hp : is_unit (p : R))
  {χ : mul_char R R'} (hχ : is_quadratic χ) (ψ : add_char R R') :
  gauss_sum χ ψ ^ (p ^ n) = χ (p ^ n) * gauss_sum χ ψ :=
begin
  induction n with n ih,
  { rw [pow_zero, pow_one, pow_zero, mul_char.map_one, one_mul], },
  { rw [pow_succ, mul_comm p, pow_mul, ih, mul_pow, hχ.gauss_sum_frob _ hp,
        ← mul_assoc, pow_succ, mul_comm (p : R), map_mul,
        ← pow_apply' χ fp.1.pos (p ^ n), hχ.pow_char p], },
end

end gauss_sum_frob

/-!
### Values of quadratic characters
-/

section gauss_sum_values

variables {R : Type u} [comm_ring R] [fintype R] {R' : Type v} [comm_ring R'] [is_domain R']

/-- If the square of the Gauss sum of a quadratic character is `χ(-1) * #R`,
then we get, for all `n : ℕ`, the relation `(χ(-1) * #R) ^ (p^n/2) = χ(p^n)`,
where `p` is the (odd) characteristic of the target ring `R'`.
This version can be used when `R` is not a field, e.g., `ℤ/8ℤ`. -/
lemma char.card_pow_char_pow {χ : mul_char R R'} (hχ : is_quadratic χ) (ψ : add_char R R') (p n : ℕ)
  [fp : fact p.prime] [hch : char_p R' p] (hp : is_unit (p : R)) (hp' : p ≠ 2)
  (hg : (gauss_sum χ ψ) ^ 2 = χ (-1) * fintype.card R) :
  (χ (-1) * fintype.card R) ^ (p ^ n / 2) = χ (p ^ n) :=
begin
  have : gauss_sum χ ψ ≠ 0,
  { intro hf, rw [hf, zero_pow (by norm_num : 0 < 2), eq_comm, mul_eq_zero] at hg,
    exact not_is_unit_prime_of_dvd_card p
      ((char_p.cast_eq_zero_iff R' p _).mp $ hg.resolve_left (is_unit_one.neg.map χ).ne_zero) hp },
  rw ← hg, apply mul_right_cancel₀ this,
  rw [← hχ.gauss_sum_frob_iter p n hp ψ, ← pow_mul, mul_comm, ← pow_succ,
      nat.two_mul_div_two_add_one_of_odd ((fp.1.eq_two_or_odd').resolve_left hp').pow],
end

/-- When `F` and `F'` are finite fields and `χ : F → F'` is a nontrivial quadratic character,
then `(χ(-1) * #F)^(#F'/2) = χ(#F')`. -/
lemma char.card_pow_card {F : Type} [field F] [fintype F] {F' : Type} [field F'] [fintype F']
  {χ : mul_char F F'} (hχ₁ : is_nontrivial χ) (hχ₂ : is_quadratic χ)
  (hch₁ : ring_char F' ≠ ring_char F) (hch₂ : ring_char F' ≠ 2) :
  (χ (-1) * fintype.card F) ^ (fintype.card F' / 2) = χ (fintype.card F') :=
begin
  obtain ⟨n, hp, hc⟩ := finite_field.card F (ring_char F),
  obtain ⟨n', hp', hc'⟩ := finite_field.card F' (ring_char F'),
  let ψ := primitive_char_finite_field F F' hch₁,
  let FF' := cyclotomic_field ψ.n F',
  have hchar := algebra.ring_char_eq F' FF',
  apply (algebra_map F' FF').injective,
  rw [map_pow, map_mul, map_nat_cast, hc', hchar, nat.cast_pow],
  simp only [← mul_char.ring_hom_comp_apply],
  haveI := fact.mk hp',
  haveI := fact.mk (hchar.subst hp'),
  rw [ne, ← nat.prime_dvd_prime_iff_eq hp' hp, ← is_unit_iff_not_dvd_char, hchar] at hch₁,
  exact char.card_pow_char_pow (hχ₂.comp _) ψ.char (ring_char FF') n' hch₁ (hchar ▸ hch₂)
    (gauss_sum_sq (hχ₁.comp $ ring_hom.injective _) (hχ₂.comp _) ψ.prim),
end

end gauss_sum_values

section gauss_sum_two

/-!
### The quadratic character of 2

This section proves the following result.

For every finite field `F` of odd characteristic, we have `2^(#F/2) = χ₈(#F)` in `F`.
This can be used to show that the quadratic character of `F` takes the value
`χ₈(#F)` at `2`.

The proof uses the Gauss sum of `χ₈` and a primitive additive character on `ℤ/8ℤ`;
in this way, the result is reduced to `card_pow_char_pow`.
-/

open zmod

/-- For every finite field `F` of odd characteristic, we have `2^(#F/2) = χ₈(#F)` in `F`. -/
lemma finite_field.two_pow_card {F : Type*} [fintype F] [field F] (hF : ring_char F ≠ 2) :
  (2 : F) ^ (fintype.card F / 2) = χ₈ (fintype.card F) :=
begin
  have hp2 : ∀ (n : ℕ), (2 ^ n : F) ≠ 0 := λ n, pow_ne_zero n (ring.two_ne_zero hF),
  obtain ⟨n, hp, hc⟩ := finite_field.card F (ring_char F),

  -- we work in `FF`, the eighth cyclotomic field extension of `F`
  let FF := (polynomial.cyclotomic 8 F).splitting_field,
  haveI : finite_dimensional F FF :=
    polynomial.is_splitting_field.finite_dimensional FF (polynomial.cyclotomic 8 F),
  haveI : fintype FF := finite_dimensional.fintype_of_fintype F FF,
  have hchar := algebra.ring_char_eq F FF,
  have FFp := hchar.subst hp,
  haveI := fact.mk FFp,
  have hFF := ne_of_eq_of_ne hchar.symm hF, -- `ring_char FF ≠ 2`
  have hu : is_unit (ring_char FF : zmod 8),
  { rw [is_unit_iff_not_dvd_char, ring_char_zmod_n],
    rw [ne, ← nat.prime_dvd_prime_iff_eq FFp nat.prime_two] at hFF,
    change ¬ _ ∣ 2 ^ 3,
    exact mt FFp.dvd_of_dvd_pow hFF },

  -- there is a primitive additive character `ℤ/8ℤ → FF`, sending `a + 8ℤ ↦ τ^a`
  -- with a primitive eighth root of unity `τ`
  let ψ₈ := primitive_zmod_char 8 F (by convert hp2 3; norm_num),
  let τ : FF := ψ₈.char 1,
  have τ_spec : τ ^ 4 = -1,
  { refine (sq_eq_one_iff.1 _).resolve_left _;
    { simp only [τ, ← map_nsmul_pow],
      erw add_char.is_primitive.zmod_char_eq_one_iff 8 ψ₈.prim,
      dec_trivial } },

  -- we consider `χ₈` as a multiplicative character `ℤ/8ℤ → FF`
  let χ := χ₈.ring_hom_comp (int.cast_ring_hom FF),
  have hχ : χ (-1) = 1 := norm_num.int_cast_one,
  have hq : is_quadratic χ := is_quadratic_χ₈.comp _,

  -- we now show that the Gauss sum of `χ` and `ψ₈` has the relevant property
  have hg : gauss_sum χ ψ₈.char ^ 2 = χ (-1) * fintype.card (zmod 8),
  { rw [hχ, one_mul, card, gauss_sum],
    convert ← congr_arg (^ 2) (fin.sum_univ_eight $ λ x, (χ₈ x : FF) * τ ^ x.val),
    { ext, congr, apply pow_one },
    convert_to (0 + 1 * τ ^ 1 + 0 + (-1) * τ ^ 3 + 0 + (-1) * τ ^ 5 + 0 + 1 * τ ^ 7) ^ 2 = _,
    { simp only [χ₈_apply, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons,
        matrix.cons_vec_bit0_eq_alt0, matrix.cons_vec_bit1_eq_alt1, matrix.cons_vec_append,
        matrix.cons_vec_alt0, matrix.cons_vec_alt1, int.cast_zero, int.cast_one, int.cast_neg,
        zero_mul], refl },
    convert_to 8 + (τ ^ 4 + 1) * (τ ^ 10 - 2 * τ ^ 8 - 2 * τ ^ 6 + 6 * τ ^ 4 + τ ^ 2 - 8) = _,
    { ring }, { rw τ_spec, norm_num } },

  -- this allows us to apply `card_pow_char_pow` to our situation
  have h := char.card_pow_char_pow hq ψ₈.char (ring_char FF) n hu hFF hg,
  rw [card, ← hchar, hχ, one_mul, ← hc, ← nat.cast_pow (ring_char F), ← hc] at h,

  -- finally, we change `2` to `8` on the left hand side
  convert_to (8 : F) ^ (fintype.card F / 2) = _,
  { rw [(by norm_num : (8 : F) = 2 ^ 2 * 2), mul_pow,
      (finite_field.is_square_iff hF $ hp2 2).mp ⟨2, pow_two 2⟩, one_mul] },
  apply (algebra_map F FF).injective,
  simp only [map_pow, map_bit0, map_one, map_int_cast],
  convert h, norm_num,
end

end gauss_sum_two
