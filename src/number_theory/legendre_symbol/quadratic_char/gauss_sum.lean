/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import number_theory.legendre_symbol.quadratic_char.basic
import number_theory.legendre_symbol.gauss_sum

/-!
# Quadratic characters of finite fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Further facts relying on Gauss sums.

-/

/-!
### Basic properties of the quadratic character

We prove some properties of the quadratic character.
We work with a finite field `F` here.
The interesting case is when the characteristic of `F` is odd.
-/

section special_values

open zmod mul_char

variables {F : Type*} [field F] [fintype F]

/-- The value of the quadratic character at `2` -/
lemma quadratic_char_two [decidable_eq F] (hF : ring_char F ≠ 2) :
  quadratic_char F 2 = χ₈ (fintype.card F) :=
is_quadratic.eq_of_eq_coe (quadratic_char_is_quadratic F) is_quadratic_χ₈ hF
  ((quadratic_char_eq_pow_of_char_ne_two' hF 2).trans (finite_field.two_pow_card hF))

/-- `2` is a square in `F` iff `#F` is not congruent to `3` or `5` mod `8`. -/
lemma finite_field.is_square_two_iff :
  is_square (2 : F) ↔ fintype.card F % 8 ≠ 3 ∧ fintype.card F % 8 ≠ 5 :=
begin
  classical,
  by_cases hF : ring_char F = 2,
  focus
  { have h := finite_field.even_card_of_char_two hF,
    simp only [finite_field.is_square_of_char_two hF, true_iff], },
  rotate, focus
  { have h := finite_field.odd_card_of_char_ne_two hF,
    rw [← quadratic_char_one_iff_is_square (ring.two_ne_zero hF), quadratic_char_two hF,
        χ₈_nat_eq_if_mod_eight],
    simp only [h, nat.one_ne_zero, if_false, ite_eq_left_iff, ne.def, (dec_trivial : (-1 : ℤ) ≠ 1),
               imp_false, not_not], },
  all_goals
  { rw [← nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 8)] at h,
    have h₁ := nat.mod_lt (fintype.card F) (dec_trivial : 0 < 8),
    revert h₁ h,
    generalize : fintype.card F % 8 = n,
    dec_trivial!, }
end

/-- The value of the quadratic character at `-2` -/
lemma quadratic_char_neg_two [decidable_eq F] (hF : ring_char F ≠ 2) :
  quadratic_char F (-2) = χ₈' (fintype.card F) :=
begin
  rw [(by norm_num : (-2 : F) = (-1) * 2), map_mul, χ₈'_eq_χ₄_mul_χ₈, quadratic_char_neg_one hF,
      quadratic_char_two hF, @cast_nat_cast _ (zmod 4) _ _ _ (by norm_num : 4 ∣ 8)],
end

/-- `-2` is a square in `F` iff `#F` is not congruent to `5` or `7` mod `8`. -/
lemma finite_field.is_square_neg_two_iff :
  is_square (-2 : F) ↔ fintype.card F % 8 ≠ 5 ∧ fintype.card F % 8 ≠ 7 :=
begin
  classical,
  by_cases hF : ring_char F = 2,
  focus
  { have h := finite_field.even_card_of_char_two hF,
    simp only [finite_field.is_square_of_char_two hF, true_iff], },
  rotate, focus
  { have h := finite_field.odd_card_of_char_ne_two hF,
    rw [← quadratic_char_one_iff_is_square (neg_ne_zero.mpr (ring.two_ne_zero hF)),
        quadratic_char_neg_two hF, χ₈'_nat_eq_if_mod_eight],
    simp only [h, nat.one_ne_zero, if_false, ite_eq_left_iff, ne.def, (dec_trivial : (-1 : ℤ) ≠ 1),
               imp_false, not_not], },
  all_goals
  { rw [← nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 8)] at h,
    have h₁ := nat.mod_lt (fintype.card F) (dec_trivial : 0 < 8),
    revert h₁ h,
    generalize : fintype.card F % 8 = n,
    dec_trivial! }
end

/-- The relation between the values of the quadratic character of one field `F` at the
cardinality of another field `F'` and of the quadratic character of `F'` at the cardinality
of `F`. -/
lemma quadratic_char_card_card [decidable_eq F] (hF : ring_char F ≠ 2) {F' : Type*} [field F']
  [fintype F'] [decidable_eq F'] (hF' : ring_char F' ≠ 2) (h : ring_char F' ≠ ring_char F) :
  quadratic_char F (fintype.card F') = quadratic_char F' (quadratic_char F (-1) * fintype.card F) :=
begin
  let χ := (quadratic_char F).ring_hom_comp (algebra_map ℤ F'),
  have hχ₁ : χ.is_nontrivial,
  { obtain ⟨a, ha⟩ := quadratic_char_exists_neg_one hF,
    have hu : is_unit a,
    { contrapose ha,
      exact ne_of_eq_of_ne (map_nonunit (quadratic_char F) ha)
             (mt zero_eq_neg.mp one_ne_zero), },
    use hu.unit,
    simp only [is_unit.unit_spec, ring_hom_comp_apply, eq_int_cast, ne.def, ha],
    rw [int.cast_neg, int.cast_one],
    exact ring.neg_one_ne_one_of_char_ne_two hF', },
  have hχ₂ : χ.is_quadratic := is_quadratic.comp (quadratic_char_is_quadratic F) _,
  have h := char.card_pow_card hχ₁ hχ₂ h hF',
  rw [← quadratic_char_eq_pow_of_char_ne_two' hF'] at h,
  exact (is_quadratic.eq_of_eq_coe (quadratic_char_is_quadratic F')
             (quadratic_char_is_quadratic F) hF' h).symm,
end

/-- The value of the quadratic character at an odd prime `p` different from `ring_char F`. -/
lemma quadratic_char_odd_prime [decidable_eq F] (hF : ring_char F ≠ 2) {p : ℕ} [fact p.prime]
  (hp₁ : p ≠ 2) (hp₂ : ring_char F ≠ p) :
  quadratic_char F p = quadratic_char (zmod p) (χ₄ (fintype.card F) * fintype.card F) :=
begin
  rw [← quadratic_char_neg_one hF],
  have h := quadratic_char_card_card hF (ne_of_eq_of_ne (ring_char_zmod_n p) hp₁)
              (ne_of_eq_of_ne (ring_char_zmod_n p) hp₂.symm),
  rwa [card p] at h,
end

/-- An odd prime `p` is a square in `F` iff the quadratic character of `zmod p` does not
take the value `-1` on `χ₄(#F) * #F`. -/
lemma finite_field.is_square_odd_prime_iff (hF : ring_char F ≠ 2) {p : ℕ} [fact p.prime]
  (hp : p ≠ 2) :
  is_square (p : F) ↔ quadratic_char (zmod p) (χ₄ (fintype.card F) * fintype.card F) ≠ -1 :=
begin
  classical,
  by_cases hFp : ring_char F = p,
  { rw [show (p : F) = 0, by { rw ← hFp, exact ring_char.nat.cast_ring_char }],
    simp only [is_square_zero, ne.def, true_iff, map_mul],
    obtain ⟨n, _, hc⟩ := finite_field.card F (ring_char F),
    have hchar : ring_char F = ring_char (zmod p) := by {rw hFp, exact (ring_char_zmod_n p).symm},
    conv {congr, to_lhs, congr, skip, rw [hc, nat.cast_pow, map_pow, hchar, map_ring_char], },
    simp only [zero_pow n.pos, mul_zero, zero_eq_neg, one_ne_zero, not_false_iff], },
  { rw [← iff.not_left (@quadratic_char_neg_one_iff_not_is_square F _ _ _ _),
        quadratic_char_odd_prime hF hp],
    exact hFp, },
end

end special_values
