/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import data.fintype.parity
import number_theory.legendre_symbol.zmod_char
import field_theory.finite.basic
import number_theory.legendre_symbol.gauss_sum

/-!
# Quadratic characters of finite fields

This file defines the quadratic character on a finite field `F` and proves
some basic statements about it.

## Tags

quadratic character
-/

/-!
### Definition of the quadratic character

We define the quadratic character of a finite field `F` with values in ℤ.
-/

section define

/-- Define the quadratic character with values in ℤ on a monoid with zero `α`.
It takes the value zero at zero; for non-zero argument `a : α`, it is `1`
if `a` is a square, otherwise it is `-1`.

This only deserves the name "character" when it is multiplicative,
e.g., when `α` is a finite field. See `quadratic_char_fun_mul`.

We will later define `quadratic_char` to be a multiplicative character
of type `mul_char F ℤ`, when the domain is a finite field `F`.
-/
def quadratic_char_fun (α : Type*) [monoid_with_zero α] [decidable_eq α]
  [decidable_pred (is_square : α → Prop)] (a : α) : ℤ :=
if a = 0 then 0 else if is_square a then 1 else -1

end define

/-!
### Basic properties of the quadratic character

We prove some properties of the quadratic character.
We work with a finite field `F` here.
The interesting case is when the characteristic of `F` is odd.
-/

section quadratic_char

open mul_char

variables {F : Type*} [field F] [fintype F] [decidable_eq F]

/-- Some basic API lemmas -/
lemma quadratic_char_fun_eq_zero_iff {a : F} : quadratic_char_fun F a = 0 ↔ a = 0 :=
begin
  simp only [quadratic_char_fun],
  by_cases ha : a = 0,
  { simp only [ha, eq_self_iff_true, if_true], },
  { simp only [ha, if_false, iff_false],
    split_ifs; simp only [neg_eq_zero, one_ne_zero, not_false_iff], },
end

@[simp]
lemma quadratic_char_fun_zero : quadratic_char_fun F 0 = 0 :=
by simp only [quadratic_char_fun, eq_self_iff_true, if_true, id.def]

@[simp]
lemma quadratic_char_fun_one : quadratic_char_fun F 1 = 1 :=
by simp only [quadratic_char_fun, one_ne_zero, is_square_one, if_true, if_false, id.def]

/-- If `ring_char F = 2`, then `quadratic_char_fun F` takes the value `1` on nonzero elements. -/
lemma quadratic_char_fun_eq_one_of_char_two (hF : ring_char F = 2) {a : F} (ha : a ≠ 0) :
  quadratic_char_fun F a = 1 :=
begin
  simp only [quadratic_char_fun, ha, if_false, ite_eq_left_iff],
  exact λ h, false.rec _ (h (finite_field.is_square_of_char_two hF a))
end

/-- If `ring_char F` is odd, then `quadratic_char_fun F a` can be computed in
terms of `a ^ (fintype.card F / 2)`. -/
lemma quadratic_char_fun_eq_pow_of_char_ne_two (hF : ring_char F ≠ 2) {a : F} (ha : a ≠ 0) :
  quadratic_char_fun F a = if a ^ (fintype.card F / 2) = 1 then 1 else -1 :=
begin
  simp only [quadratic_char_fun, ha, if_false],
  simp_rw finite_field.is_square_iff hF ha,
end

/-- The quadratic character is multiplicative. -/
lemma quadratic_char_fun_mul (a b : F) :
  quadratic_char_fun F (a * b) = quadratic_char_fun F a * quadratic_char_fun F b :=
begin
  by_cases ha : a = 0,
  { rw [ha, zero_mul, quadratic_char_fun_zero, zero_mul], },
  -- now `a ≠ 0`
  by_cases hb : b = 0,
  { rw [hb, mul_zero, quadratic_char_fun_zero, mul_zero], },
  -- now `a ≠ 0` and `b ≠ 0`
  have hab := mul_ne_zero ha hb,
  by_cases hF : ring_char F = 2,
  { -- case `ring_char F = 2`
    rw [quadratic_char_fun_eq_one_of_char_two hF ha,
        quadratic_char_fun_eq_one_of_char_two hF hb,
        quadratic_char_fun_eq_one_of_char_two hF hab,
        mul_one], },
  { -- case of odd characteristic
    rw [quadratic_char_fun_eq_pow_of_char_ne_two hF ha,
        quadratic_char_fun_eq_pow_of_char_ne_two hF hb,
        quadratic_char_fun_eq_pow_of_char_ne_two hF hab,
        mul_pow],
    cases finite_field.pow_dichotomy hF hb with hb' hb',
    { simp only [hb', mul_one, eq_self_iff_true, if_true], },
    { have h := ring.neg_one_ne_one_of_char_ne_two hF, -- `-1 ≠ 1`
      simp only [hb', h, mul_neg, mul_one, if_false, ite_mul, neg_mul],
      cases finite_field.pow_dichotomy hF ha with ha' ha';
        simp only [ha', h, neg_neg, eq_self_iff_true, if_true, if_false], }, },
end

variables (F)

/-- The quadratic character as a multiplicative character. -/
@[simps] def quadratic_char : mul_char F ℤ :=
{ to_fun := quadratic_char_fun F,
  map_one' := quadratic_char_fun_one,
  map_mul' := quadratic_char_fun_mul,
  map_nonunit' := λ a ha, by { rw of_not_not (mt ne.is_unit ha), exact quadratic_char_fun_zero, } }

variables {F}

/-- The value of the quadratic character on `a` is zero iff `a = 0`. -/
lemma quadratic_char_eq_zero_iff {a : F} : quadratic_char F a = 0 ↔ a = 0 :=
quadratic_char_fun_eq_zero_iff

@[simp]
lemma quadratic_char_zero : quadratic_char F 0 = 0 :=
by simp only [quadratic_char_apply, quadratic_char_fun_zero]

/-- For nonzero `a : F`, `quadratic_char F a = 1 ↔ is_square a`. -/
lemma quadratic_char_one_iff_is_square {a : F} (ha : a ≠ 0) :
  quadratic_char F a = 1 ↔ is_square a :=
by simp only [quadratic_char_apply, quadratic_char_fun, ha, (dec_trivial : (-1 : ℤ) ≠ 1),
              if_false, ite_eq_left_iff, imp_false, not_not]

/-- The quadratic character takes the value `1` on nonzero squares. -/
lemma quadratic_char_sq_one' {a : F} (ha : a ≠ 0) : quadratic_char F (a ^ 2) = 1 :=
by simp only [quadratic_char_fun, ha, pow_eq_zero_iff, nat.succ_pos', is_square_sq, if_true,
              if_false, quadratic_char_apply]

/-- The square of the quadratic character on nonzero arguments is `1`. -/
lemma quadratic_char_sq_one {a : F} (ha : a ≠ 0) : (quadratic_char F a) ^ 2 = 1 :=
by rwa [pow_two, ← map_mul, ← pow_two, quadratic_char_sq_one']

/-- The quadratic character is `1` or `-1` on nonzero arguments. -/
lemma quadratic_char_dichotomy {a : F} (ha : a ≠ 0) :
  quadratic_char F a = 1 ∨ quadratic_char F a = -1 :=
sq_eq_one_iff.1 $ quadratic_char_sq_one ha

/-- The quadratic character is `1` or `-1` on nonzero arguments. -/
lemma quadratic_char_eq_neg_one_iff_not_one {a : F} (ha : a ≠ 0) :
  quadratic_char F a = -1 ↔ ¬ quadratic_char F a = 1 :=
begin
  refine ⟨λ h, _, λ h₂, (or_iff_right h₂).mp (quadratic_char_dichotomy ha)⟩,
  rw h,
  norm_num,
end

/-- For `a : F`, `quadratic_char F a = -1 ↔ ¬ is_square a`. -/
lemma quadratic_char_neg_one_iff_not_is_square {a : F} :
  quadratic_char F a = -1 ↔ ¬ is_square a :=
begin
  by_cases ha : a = 0,
  { simp only [ha, is_square_zero, mul_char.map_zero, zero_eq_neg, one_ne_zero, not_true], },
  { rw [quadratic_char_eq_neg_one_iff_not_one ha, quadratic_char_one_iff_is_square ha] },
end

/-- If `F` has odd characteristic, then `quadratic_char F` takes the value `-1`. -/
lemma quadratic_char_exists_neg_one (hF : ring_char F ≠ 2) : ∃ a, quadratic_char F a = -1 :=
(finite_field.exists_nonsquare hF).imp $ λ b h₁, quadratic_char_neg_one_iff_not_is_square.mpr h₁

/-- If `ring_char F = 2`, then `quadratic_char F` takes the value `1` on nonzero elements. -/
lemma quadratic_char_eq_one_of_char_two (hF : ring_char F = 2) {a : F} (ha : a ≠ 0) :
  quadratic_char F a = 1 :=
quadratic_char_fun_eq_one_of_char_two hF ha

/-- If `ring_char F` is odd, then `quadratic_char F a` can be computed in
terms of `a ^ (fintype.card F / 2)`. -/
lemma quadratic_char_eq_pow_of_char_ne_two (hF : ring_char F ≠ 2) {a : F} (ha : a ≠ 0) :
  quadratic_char F a = if a ^ (fintype.card F / 2) = 1 then 1 else -1 :=
quadratic_char_fun_eq_pow_of_char_ne_two hF ha

lemma quadratic_char_eq_pow_of_char_ne_two' (hF : ring_char F ≠ 2) (a : F) :
  (quadratic_char F a : F) = a ^ (fintype.card F / 2) :=
begin
  by_cases ha : a = 0,
  { have : 0 < fintype.card F / 2 := nat.div_pos fintype.one_lt_card two_pos,
    simp only [ha, zero_pow this, quadratic_char_apply, quadratic_char_zero, int.cast_zero], },
  { rw [quadratic_char_eq_pow_of_char_ne_two hF ha],
    by_cases ha' : a ^ (fintype.card F / 2) = 1,
    { simp only [ha', eq_self_iff_true, if_true, int.cast_one], },
    { have ha'' := or.resolve_left (finite_field.pow_dichotomy hF ha) ha',
      simp only [ha'', int.cast_ite, int.cast_one, int.cast_neg, ite_eq_right_iff],
      exact eq.symm, } }
end

variables (F)

/-- The quadratic character is quadratic as a multiplicative character. -/
lemma quadratic_char_is_quadratic : (quadratic_char F).is_quadratic :=
begin
  intro a,
  by_cases ha : a = 0,
  { left, rw ha, exact quadratic_char_zero, },
  { right, exact quadratic_char_dichotomy ha, },
end

variables {F}

/-- The quadratic character is nontrivial as a multiplicative character
when the domain has odd characteristic. -/
lemma quadratic_char_is_nontrivial (hF : ring_char F ≠ 2) : (quadratic_char F).is_nontrivial :=
begin
  rcases quadratic_char_exists_neg_one hF with ⟨a, ha⟩,
  have hu : is_unit a := by { by_contra hf, rw map_nonunit _ hf at ha, norm_num at ha, },
  refine ⟨hu.unit, (_ : quadratic_char F a ≠ 1)⟩,
  rw ha,
  norm_num,
end

/-- The number of solutions to `x^2 = a` is determined by the quadratic character. -/
lemma quadratic_char_card_sqrts (hF : ring_char F ≠ 2) (a : F) :
  ↑{x : F | x^2 = a}.to_finset.card = quadratic_char F a + 1 :=
begin
  -- we consider the cases `a = 0`, `a` is a nonzero square and `a` is a nonsquare in turn
  by_cases h₀ : a = 0,
  { simp only [h₀, pow_eq_zero_iff, nat.succ_pos', int.coe_nat_succ, int.coe_nat_zero,
               mul_char.map_zero, set.set_of_eq_eq_singleton, set.to_finset_card,
               set.card_singleton], },
  { set s := {x : F | x^2 = a}.to_finset with hs,
    by_cases h : is_square a,
    { rw (quadratic_char_one_iff_is_square h₀).mpr h,
      rcases h with ⟨b, h⟩,
      rw [h, mul_self_eq_zero] at h₀,
      have h₁ : s = [b, -b].to_finset := by
      { ext x,
        simp only [finset.mem_filter, finset.mem_univ, true_and, list.to_finset_cons,
                   list.to_finset_nil, insert_emptyc_eq, finset.mem_insert, finset.mem_singleton],
        rw ← pow_two at h,
        simp only [hs, set.mem_to_finset, set.mem_set_of_eq, h],
        split,
        { exact eq_or_eq_neg_of_sq_eq_sq _ _, },
        { rintro (h₂ | h₂); rw h₂,
          simp only [neg_sq], }, },
      norm_cast,
      rw  [h₁, list.to_finset_cons, list.to_finset_cons, list.to_finset_nil],
      exact finset.card_doubleton
              (ne.symm (mt (ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h₀)), },
    { rw quadratic_char_neg_one_iff_not_is_square.mpr h,
      simp only [int.coe_nat_eq_zero, finset.card_eq_zero, set.to_finset_card,
                 fintype.card_of_finset, set.mem_set_of_eq, add_left_neg],
      ext x,
      simp only [iff_false, finset.mem_filter, finset.mem_univ, true_and, finset.not_mem_empty],
      rw is_square_iff_exists_sq at h,
      exact λ h', h ⟨_, h'.symm⟩, }, },
end

open_locale big_operators

/-- The sum over the values of the quadratic character is zero when the characteristic is odd. -/
lemma quadratic_char_sum_zero (hF : ring_char F ≠ 2) : ∑ (a : F), quadratic_char F a = 0 :=
is_nontrivial.sum_eq_zero (quadratic_char_is_nontrivial hF)

end quadratic_char

/-!
### Special values of the quadratic character

We express `quadratic_char F (-1)` in terms of `χ₄`.
-/

section special_values

open zmod mul_char

variables {F : Type} [field F] [fintype F]

/-- The value of the quadratic character at `-1` -/
lemma quadratic_char_neg_one [decidable_eq F] (hF : ring_char F ≠ 2) :
  quadratic_char F (-1) = χ₄ (fintype.card F) :=
begin
  have h := quadratic_char_eq_pow_of_char_ne_two hF (neg_ne_zero.mpr one_ne_zero),
  rw [h, χ₄_eq_neg_one_pow (finite_field.odd_card_of_char_ne_two hF)],
  set n := fintype.card F / 2,
  cases (nat.even_or_odd n) with h₂ h₂,
  { simp only [even.neg_one_pow h₂, eq_self_iff_true, if_true], },
  { simp only [odd.neg_one_pow h₂, ite_eq_right_iff],
    exact λ hf, false.rec (1 = -1) (ring.neg_one_ne_one_of_char_ne_two hF hf), },
end

/-- `-1` is a square in `F` iff `#F` is not congruent to `3` mod `4`. -/
lemma finite_field.is_square_neg_one_iff : is_square (-1 : F) ↔ fintype.card F % 4 ≠ 3 :=
begin
  classical, -- suggested by the linter (instead of `[decidable_eq F]`)
  by_cases hF : ring_char F = 2,
  { simp only [finite_field.is_square_of_char_two hF, ne.def, true_iff],
    exact (λ hf, one_ne_zero  $ (nat.odd_of_mod_four_eq_three hf).symm.trans
                              $ finite_field.even_card_of_char_two hF) },
  { have h₁ := finite_field.odd_card_of_char_ne_two hF,
    rw [← quadratic_char_one_iff_is_square (neg_ne_zero.mpr (one_ne_zero' F)),
        quadratic_char_neg_one hF, χ₄_nat_eq_if_mod_four, h₁],
    simp only [nat.one_ne_zero, if_false, ite_eq_left_iff, ne.def, (dec_trivial : (-1 : ℤ) ≠ 1),
               imp_false, not_not],
    exact ⟨λ h, ne_of_eq_of_ne h (dec_trivial : 1 ≠ 3),
           or.resolve_right (nat.odd_mod_four_iff.mp h₁)⟩, },
end

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
lemma quadratic_char_card_card [decidable_eq F] (hF : ring_char F ≠ 2) {F' : Type} [field F']
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
