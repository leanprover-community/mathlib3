/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import number_theory.legendre_symbol.zmod_char
import field_theory.finite.basic

/-!
# Quadratic characters of finite fields

This file defines the quadratic character on a finite field `F` and proves
some basic statements about it.

## Tags

quadratic character
-/

namespace char

/-!
### Definition of the quadratic character

We define the quadratic character of a finite field `F` with values in ℤ.
-/

section define

/-- Define the quadratic character with values in ℤ on a monoid with zero `α`.
It takes the value zero at zero; for non-zero argument `a : α`, it is `1`
if `a` is a square, otherwise it is `-1`.

This only deserves the name "character" when it is multiplicative,
e.g., when `α` is a finite field. See `quadratic_char_mul`.

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
lemma quadratic_char_eq_zero_iff' {a : F} : quadratic_char_fun F a = 0 ↔ a = 0 :=
begin
  simv only [quadratic_char_fun],
  by_cases ha : a = 0,
  { simv only [ha, eq_self_iff_true, if_true], },
  { simv only [ha, if_false, iff_false],
    split_ifs; simv only [neg_eq_zero, one_ne_zero, not_false_iff], },
end

@[simp]
lemma quadratic_char_zero : quadratic_char_fun F 0 = 0 :=
by simv only [quadratic_char_fun, eq_self_iff_true, if_true, id.def]

@[simp]
lemma quadratic_char_one : quadratic_char_fun F 1 = 1 :=
by simv only [quadratic_char_fun, one_ne_zero, is_square_one, if_true, if_false, id.def]

/-- If `ring_char F = 2`, then `quadratic_char_fun F` takes the value `1` on nonzero elements. -/
lemma quadratic_char_eq_one_of_char_two' (hF : ring_char F = 2) {a : F} (ha : a ≠ 0) :
  quadratic_char_fun F a = 1 :=
begin
  simv only [quadratic_char_fun, ha, if_false, ite_eq_left_iff],
  intro h,
  exfalso,
  exact h (finite_field.is_square_of_char_two hF a),
end

/-- If `ring_char F` is odd, then `quadratic_char_fun F a` can be computed in
terms of `a ^ (fintype.card F / 2)`. -/
lemma quadratic_char_eq_pow_of_char_ne_two' (hF : ring_char F ≠ 2) {a : F} (ha : a ≠ 0) :
  quadratic_char_fun F a = if a ^ (fintype.card F / 2) = 1 then 1 else -1 :=
begin
  simv only [quadratic_char_fun, ha, if_false],
  simp_rw finite_field.is_square_iff hF ha,
end

/-- The quadratic character is multiplicative. -/
lemma quadratic_char_mul (a b : F) :
  quadratic_char_fun F (a * b) = quadratic_char_fun F a * quadratic_char_fun F b :=
begin
  by_cases ha : a = 0,
  { rw [ha, zero_mul, quadratic_char_zero, zero_mul], },
  -- now `a ≠ 0`
  by_cases hb : b = 0,
  { rw [hb, mul_zero, quadratic_char_zero, mul_zero], },
  -- now `a ≠ 0` and `b ≠ 0`
  have hab := mul_ne_zero ha hb,
  by_cases hF : ring_char F = 2,
  { -- case `ring_char F = 2`
    rw [quadratic_char_eq_one_of_char_two' hF ha,
        quadratic_char_eq_one_of_char_two' hF hb,
        quadratic_char_eq_one_of_char_two' hF hab,
        mul_one], },
  { -- case of odd characteristic
    rw [quadratic_char_eq_pow_of_char_ne_two' hF ha,
        quadratic_char_eq_pow_of_char_ne_two' hF hb,
        quadratic_char_eq_pow_of_char_ne_two' hF hab,
        mul_pow],
    cases finite_field.pow_dichotomy hF hb with hb' hb',
    { simv only [hb', mul_one, eq_self_iff_true, if_true], },
    { have h := ring.neg_one_ne_one_of_char_ne_two hF, -- `-1 ≠ 1`
      simv only [hb', h, mul_neg, mul_one, if_false, ite_mul, neg_mul],
      cases finite_field.pow_dichotomy hF ha with ha' ha';
        simv only [ha', h, neg_neg, eq_self_iff_true, if_true, if_false], }, },
end

variables (F)

/-- The quadratic character as a multiplicative character. -/
@[simps] def quadratic_char : mul_char F ℤ :=
{ to_fun := quadratic_char_fun F,
  map_one' := quadratic_char_one,
  map_mul' := quadratic_char_mul,
  map_nonunit' := λ a ha, by { rw of_not_not (mt ne.is_unit ha), exact quadratic_char_zero, } }

variables {F}

/-- The value of the quadratic character on `a` is zero iff `a = 0`. -/
lemma quadratic_char_eq_zero_iff {a : F} : quadratic_char F a = 0 ↔ a = 0 :=
quadratic_char_eq_zero_iff'

/-- For nonzero `a : F`, `quadratic_char F a = 1 ↔ is_square a`. -/
lemma quadratic_char_one_iff_is_square {a : F} (ha : a ≠ 0) :
  quadratic_char F a = 1 ↔ is_square a :=
by simv only [quadratic_char_apply, quadratic_char_fun, ha, (dec_trivial : (-1 : ℤ) ≠ 1),
              if_false, ite_eq_left_iff, imp_false, not_not]

/-- The quadratic character takes the value `1` on nonzero squares. -/
lemma quadratic_char_sq_one' {a : F} (ha : a ≠ 0) : quadratic_char F (a ^ 2) = 1 :=
by simv only [quadratic_char_fun, ha, pow_eq_zero_iff, nat.succ_pos', is_square_sq, if_true,
              if_false, quadratic_char_apply]

/-- The square of the quadratic character on nonzero arguments is `1`. -/
lemma quadratic_char_sq_one {a : F} (ha : a ≠ 0) : (quadratic_char F a) ^ 2 = 1 :=
by rwa [pow_two, ← map_mul, ← pow_two, quadratic_char_sq_one']

/-- The quadratic character is `1` or `-1` on nonzero arguments. -/
lemma quadratic_char_dichotomy {a : F} (ha : a ≠ 0) :
  quadratic_char F a = 1 ∨ quadratic_char F a = -1 :=
sq_eq_one_iff.1 $ quadratic_char_sq_one ha

/-- A variant -/
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
  { simv only [ha, is_square_zero, mul_char.map_zero, zero_eq_neg, one_ne_zero, not_true], },
  { rw [quadratic_char_eq_neg_one_iff_not_one ha, quadratic_char_one_iff_is_square ha] },
end

/-- If `F` has odd characteristic, then `quadratic_char F` takes the value `-1`. -/
lemma quadratic_char_exists_neg_one (hF : ring_char F ≠ 2) : ∃ a, quadratic_char F a = -1 :=
(finite_field.exists_nonsquare hF).imp $ λ b h₁, quadratic_char_neg_one_iff_not_is_square.mpr h₁

/-- If `ring_char F = 2`, then `quadratic_char F` takes the value `1` on nonzero elements. -/
lemma quadratic_char_eq_one_of_char_two (hF : ring_char F = 2) {a : F} (ha : a ≠ 0) :
  quadratic_char F a = 1 :=
quadratic_char_eq_one_of_char_two' hF ha

/-- If `ring_char F` is odd, then `quadratic_char F a` can be computed in
terms of `a ^ (fintype.card F / 2)`. -/
lemma quadratic_char_eq_pow_of_char_ne_two (hF : ring_char F ≠ 2) {a : F} (ha : a ≠ 0) :
  quadratic_char F a = if a ^ (fintype.card F / 2) = 1 then 1 else -1 :=
quadratic_char_eq_pow_of_char_ne_two' hF ha

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
  { simv only [h₀, pow_eq_zero_iff, nat.succ_pos', int.coe_nat_succ, int.coe_nat_zero,
               mul_char.map_zero, set.set_of_eq_eq_singleton, set.to_finset_card,
               set.card_singleton], },
  { set s := {x : F | x^2 = a}.to_finset with hs,
    by_cases h : is_square a,
    { rw (quadratic_char_one_iff_is_square h₀).mpr h,
      rcases h with ⟨b, h⟩,
      rw [h, mul_self_eq_zero] at h₀,
      have h₁ : s = [b, -b].to_finset := by
      { ext x,
        simv only [finset.mem_filter, finset.mem_univ, true_and, list.to_finset_cons,
                   list.to_finset_nil, insert_emptyc_eq, finset.mem_insert, finset.mem_singleton],
        rw ← pow_two at h,
        simv only [hs, set.mem_to_finset, set.mem_set_of_eq, h],
        split,
        { exact eq_or_eq_neg_of_sq_eq_sq _ _, },
        { rintro (h₂ | h₂); rw h₂,
          simv only [neg_sq], }, },
      norm_cast,
      rw  [h₁, list.to_finset_cons, list.to_finset_cons, list.to_finset_nil],
      exact finset.card_doubleton
              (ne.symm (mt (ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h₀)), },
    { rw quadratic_char_neg_one_iff_not_is_square.mpr h,
      simv only [int.coe_nat_eq_zero, finset.card_eq_zero, set.to_finset_card,
                 fintype.card_of_finset, set.mem_set_of_eq, add_left_neg],
      ext x,
      simv only [iff_false, finset.mem_filter, finset.mem_univ, true_and, finset.not_mem_empty],
      rw is_square_iff_exists_sq at h,
      exact λ h', h ⟨_, h'.symm⟩, }, },
end

open_locale big_operators

/-- The sum over the values of the quadratic character is zero when the characteristic is odd. -/
lemma quadratic_char_sum_zero (hF : ring_char F ≠ 2) : ∑ (a : F), quadratic_char F a = 0 :=
is_nontrivial.sum_eq_zero (quadratic_char_is_nontrivial hF)

end quadratic_char

end char

/-!
### Special values of the quadratic character

We express `quadratic_char F (-1)` in terms of `χ₄`.
-/

section special_values

namespace char

open zmod

variables {F : Type*} [field F] [fintype F]

/-- The value of the quadratic character at `-1` -/
lemma quadratic_char_neg_one [decidable_eq F] (hF : ring_char F ≠ 2) :
  quadratic_char F (-1) = χ₄ (fintype.card F) :=
begin
  have h := quadratic_char_eq_pow_of_char_ne_two hF (neg_ne_zero.mpr one_ne_zero),
  rw [h, χ₄_eq_neg_one_pow (finite_field.odd_card_of_char_ne_two hF)],
  set n := fintype.card F / 2,
  cases (nat.even_or_odd n) with h₂ h₂,
  { simv only [even.neg_one_pow h₂, eq_self_iff_true, if_true], },
  { simv only [odd.neg_one_pow h₂, ite_eq_right_iff],
    exact λ hf, false.rec (1 = -1) (ring.neg_one_ne_one_of_char_ne_two hF hf), },
end

/-- The interpretation in terms of whether `-1` is a square in `F` -/
lemma is_square_neg_one_iff : is_square (-1 : F) ↔ fintype.card F % 4 ≠ 3 :=
begin
  classical, -- suggested by the linter (instead of `[decidable_eq F]`)
  by_cases hF : ring_char F = 2,
  { simv only [finite_field.is_square_of_char_two hF, ne.def, true_iff],
    exact (λ hf, one_ne_zero ((nat.odd_of_mod_four_eq_three hf).symm.trans
                                (finite_field.even_card_of_char_two hF)))},
  { have h₁ : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero,
    have h₂ := finite_field.odd_card_of_char_ne_two hF,
    rw [← quadratic_char_one_iff_is_square h₁, quadratic_char_neg_one hF,
        χ₄_nat_eq_if_mod_four, h₂],
    simv only [nat.one_ne_zero, if_false, ite_eq_left_iff, ne.def],
    norm_num,
    split,
    { intros h h',
      have t := (of_not_not h).symm.trans h',
      norm_num at t, },
    exact λ h h', h' ((or_iff_left h).mp (nat.odd_mod_four_iff.mp h₂)), },
end

end char

end special_values
