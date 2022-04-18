/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import tactic
import field_theory.finite.basic

/-!
# Quadratic characters of finite fields

This file defines the quadratic character on a finite field `F` and proves
some basic statements about it.

## Tags

quadratic character
-/

/-!
### Some general results on finite fields
-/

section general

/-- Create a decidability instance for `is_square` on finite monoids. -/
instance {M : Type*} [fintype M] [monoid M] [decidable_eq M] :
  decidable_pred (is_square : M → Prop) :=
λ a, decidable_of_iff' _ (is_square_iff_exists_sq a)

/-- `0` is always a square (in a monoid with zero). -/
lemma is_square_zero (M : Type*) [monoid_with_zero M] : is_square (0 : M) :=
by { use 0, simp only [mul_zero] }

/-- If `ring_char R = 2`, where `R` is a finite reduced commutative ring,
then every `a : R` is a square. -/
lemma is_square_of_char_two' {R : Type*} [fintype R] [comm_ring R] [is_reduced R] [char_p R 2]
 (a : R) : is_square a :=
exists_imp_exists (λ b h, pow_two b ▸ eq.symm h) $
  ((fintype.bijective_iff_injective_and_card _).mpr ⟨frobenius_inj R 2, rfl⟩).surjective a

namespace finite_field

variables {F : Type*} [field F] [fintype F]

/-- In a finite field of characteristic `2`, all elements are squares. -/
lemma is_square_of_char_two (hF : ring_char F = 2) (a : F) : is_square a :=
begin
  haveI hF' : char_p F 2 := ring_char.of_eq hF,
  exact is_square_of_char_two' a,
end

/-- If the finite field `F` has characteristic `≠ 2`, then it has odd cardinatlity. -/
lemma odd_card_of_char_ne_two (hF : ring_char F ≠ 2) : fintype.card F % 2 = 1 :=
begin
  rcases finite_field.card F (ring_char F) with ⟨ n, hp, h ⟩,
  have h₁ : odd ((ring_char F) ^ (n : ℕ)) :=
  odd.pow ((or_iff_right hF).mp (nat.prime.eq_two_or_odd' hp)),
  rwa [← h, nat.odd_iff] at h₁,
end

/-- Characteristic `≠ 2` implies that `-1 ≠ 1`. -/
lemma neg_one_ne_one_of_char_ne_two (hF : ring_char F ≠ 2) : (-1 : F) ≠ 1 :=
begin
  have hc := char_p.char_is_prime F (ring_char F),
  haveI hF' : fact (2 < ring_char F) := ⟨ lt_of_le_of_ne (nat.prime.two_le hc) (ne.symm hF) ⟩,
  exact char_p.neg_one_ne_one _ (ring_char F),
end

/-- If `F` has odd characteristic, then for nonzero `a : F`, we have that `a ^ (#F / 2) = ±1`. -/
lemma pow_dichotomy (hF : ring_char F ≠ 2) {a : F} (ha : a ≠ 0) :
  a^(fintype.card F / 2) = 1 ∨ a^(fintype.card F / 2) = -1 :=
begin
  have h₁ := finite_field.pow_card_sub_one_eq_one a ha,
  set q := fintype.card F with hq,
  have hq : q % 2 = 1 := finite_field.odd_card_of_char_ne_two hF,
  have h₂ := nat.two_mul_odd_div_two hq,
  rw [← h₂, mul_comm, pow_mul, pow_two] at h₁,
  exact mul_self_eq_one_iff.mp h₁,
end

/-- A unit `a` of a finite field `F` of odd characteristic is a square
if and only if `a ^ (#F / 2) = 1`. -/
lemma unit_is_sqare_iff (hF : ring_char F ≠ 2) (a : Fˣ) :
  is_square a ↔ a ^ (fintype.card F / 2) = 1 :=
begin
  classical,
  obtain ⟨g, hg⟩ := is_cyclic.exists_generator Fˣ,
  obtain ⟨n, hn⟩ : a ∈ submonoid.powers g, { rw mem_powers_iff_mem_zpowers, apply hg },
  have hodd := nat.two_mul_odd_div_two (finite_field.odd_card_of_char_ne_two hF),
  split,
  { rintro ⟨y, rfl⟩,
    rw [← pow_two, ← pow_mul, hodd],
    apply_fun (@coe Fˣ F _),
    push_cast,
    exact finite_field.pow_card_sub_one_eq_one (y : F) (units.ne_zero y),
    exact units.ext, },
  { subst a, assume h,
    have key : 2 * (fintype.card F / 2) ∣ n * (fintype.card F / 2),
    { rw [← pow_mul] at h,
      rw [hodd, ← fintype.card_units, ← order_of_eq_card_of_forall_mem_zpowers hg],
      apply order_of_dvd_of_pow_eq_one h },
    have : 0 < fintype.card F / 2 := nat.div_pos fintype.one_lt_card (by norm_num),
    obtain ⟨m, rfl⟩ := nat.dvd_of_mul_dvd_mul_right this key,
    refine ⟨g ^ m, _⟩,
    rw [mul_comm, pow_mul, pow_two], },
end

/-- A non-zero `a : F` is a square if and only if `a ^ (#F / 2) = 1`. -/
lemma is_square_iff (hF : ring_char F ≠ 2) {a : F} (ha : a ≠ 0) :
  is_square a ↔ a ^ (fintype.card F / 2) = 1 :=
begin
  apply (iff_congr _ (by simp [units.ext_iff])).mp
        (finite_field.unit_is_sqare_iff hF (units.mk0 a ha)),
  simp only [is_square, units.ext_iff, units.coe_mk0, units.coe_mul],
  split, { rintro ⟨y, hy⟩, exact ⟨y, hy⟩ },
  { rintro ⟨y, rfl⟩,
    have hy : y ≠ 0, { rintro rfl, simpa [zero_pow] using ha, },
    refine ⟨units.mk0 y hy, _⟩, simp, }
end

/-- In a finite field of odd characteristic, not every element is a square. -/
lemma exists_nonsquare (hF : ring_char F ≠ 2) : ∃ (a : F), ¬ is_square a :=
begin
  -- idea: the squaring map on `F` is not injetive, hence not surjective
  let sq : F → F := λ x, x^2,
  have h : ¬ function.injective sq,
  begin
    simp only [function.injective, not_forall, exists_prop],
    use [-1, 1],
    split,
    { simp only [sq, one_pow, neg_one_sq], },
    { exact finite_field.neg_one_ne_one_of_char_ne_two hF, },
  end,
  have h₁ := mt (fintype.injective_iff_surjective.mpr) h, -- sq not surjective
  push_neg at h₁,
  cases h₁ with a h₁,
  use a,
  simp only [is_square, sq, not_exists, ne.def] at h₁ ⊢,
  intros b hb,
  rw ← pow_two at hb,
  exact (h₁ b hb.symm),
end

end finite_field

end general

namespace char

/-!
### Definition of the quadratic character

We define the quadratic character of a finite field `F` with values in ℤ.
-/

section define

/-- Define the quadratic character of a finite field `F` with values in ℤ.
It takes the value zero at zero; for non-zero argument `a : F`, it is `1`
if `a` is a square, otherwise it is `-1`.
-/
def quadratic_char (F : Type*) [field F] [fintype F] [decidable_eq F] (a : F) : ℤ :=
begin
  exact if a = 0 then 0 else if is_square a then 1 else -1
end

end define

/-!
### Basic properties of the quadratic character

We prove some properties of the quadratic character. The interesting case
is when the characteristic of the finite field `F` is odd.
-/

section quadratic_char

variables {F : Type*} [field F] [fintype F] [decidable_eq F]

/-- Some basic API lemmas -/
lemma quadratic_char_eq_zero_iff (a : F) : quadratic_char F a = 0 ↔ a = 0 :=
begin
  simp only [quadratic_char],
  by_cases ha : a = 0,
  { simp only [ha, eq_self_iff_true, if_true], },
  { simp [ha],
    split_ifs; simp only [neg_eq_zero, one_ne_zero, not_false_iff], },
end

@[simp]
lemma quadratic_char_zero : quadratic_char F 0 = 0 :=
by simp only [quadratic_char, eq_self_iff_true, if_true, id.def]

@[simp]
lemma quadratic_char_one : quadratic_char F 1 = 1 :=
by simp only [quadratic_char, one_ne_zero, is_square_one, if_true, if_false, id.def]

/-- For nonzero `a : F`, `quadratic_char F a = 1 ↔ is_square a`. -/
lemma quadratic_char_one_iff_is_square {a : F} (ha : a ≠ 0) :
  quadratic_char F a = 1 ↔ is_square a :=
by { simp [quadratic_char, ha, (dec_trivial : (-1 : ℤ) ≠ 1)], tauto }

/-- The quadratic character takes the value `1` on nonzero squares. -/
lemma quadratic_char_sq_one' {a : F} (ha : a ≠ 0) : quadratic_char F (a ^ 2) = 1 :=
by simp only [quadratic_char, ha, pow_eq_zero_iff, nat.succ_pos', is_square_sq, if_true, if_false]

/-- If `ring_char F = 2`, then `quadratic_char F` takes the value `1` on nonzero elements. -/
lemma quadratic_char_eq_one_of_char_two (hF : ring_char F = 2) {a : F} (ha : a ≠ 0) :
  quadratic_char F a = 1 :=
begin
  simp [quadratic_char, ha],
  intro h,
  exfalso,
  exact h (finite_field.is_square_of_char_two hF a),
end

/-- If `ring_char F` is odd, then `quadratic_char F a` can be computed in
terms of `a ^ (fintype.card F / 2)`. -/
lemma quadratic_char_eq_pow_of_char_ne_two (hF : ring_char F ≠ 2) {a : F} (ha : a ≠ 0) :
  quadratic_char F a = if a ^ (fintype.card F / 2) = 1 then 1 else -1 :=
begin
  simp only [quadratic_char, ha, if_false],
  simp_rw finite_field.is_square_iff hF ha,
end

/-- The quadratic character is multiplicative. -/
lemma quadratic_char_mul (a b : F) :
  quadratic_char F (a * b) = quadratic_char F a * quadratic_char F b :=
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
    rw [quadratic_char_eq_one_of_char_two hF ha,
        quadratic_char_eq_one_of_char_two hF hb,
        quadratic_char_eq_one_of_char_two hF hab,
        mul_one], },
  { -- case of odd characteristic
    rw [quadratic_char_eq_pow_of_char_ne_two hF ha,
        quadratic_char_eq_pow_of_char_ne_two hF hb,
        quadratic_char_eq_pow_of_char_ne_two hF hab,
        mul_pow],
    cases finite_field.pow_dichotomy hF hb with hb' hb',
    { simp only [hb', mul_one, eq_self_iff_true, if_true], },
    { have h := finite_field.neg_one_ne_one_of_char_ne_two hF, -- `-1 ≠ 1`
      simp only [hb', h, mul_neg, mul_one, if_false, ite_mul, neg_mul],
      cases finite_field.pow_dichotomy hF ha with ha' ha';
        simp only [ha', h, neg_neg, eq_self_iff_true, if_true, if_false], }, },
end

/-- The quadratic character is a homomorphism of monoids with zero. -/
def quadratic_char_hom : F →*₀ ℤ :=
{ to_fun := quadratic_char F, map_zero' := quadratic_char_zero, map_one' := quadratic_char_one,
  map_mul' := quadratic_char_mul }

/-- The square of the quadratic character on nonzero arguments is `1`. -/
lemma quadratic_char_sq_one {a : F} (ha : a ≠ 0) : (quadratic_char F a)^2 = 1 :=
by rwa [pow_two, ← quadratic_char_mul, ← pow_two, quadratic_char_sq_one']

/-- The quadratic character is `1` or `-1` on nonzero arguments. -/
lemma quadratic_char_dichotomy {a : F} (ha : a ≠ 0) :
  quadratic_char F a = 1 ∨ quadratic_char F a = -1 :=
(sq_eq_one_iff (quadratic_char F a)).mp (quadratic_char_sq_one ha)

/-- If `F` has odd characteristic, then `quadratic_char F` takes the value `-1`. -/
lemma quadratic_char_exists_neg_one (hF : ring_char F ≠ 2) : ∃ a, quadratic_char F a = -1 :=
begin
  cases (finite_field.exists_nonsquare hF) with b h₁,
  have hb : b ≠ 0 := by { intro hf, rw hf at h₁, exact h₁ (is_square_zero F), },
  use b,
  simp only [quadratic_char, hb, if_false, ite_eq_right_iff],
  tauto,
end

open_locale big_operators

/-- The sum over the values of the quadratic character is zero when the characteristic is odd. -/
lemma quadratic_char_sum_zero (hF : ring_char F ≠ 2) : ∑ (a : F), quadratic_char F a = 0 :=
begin
  cases (quadratic_char_exists_neg_one hF) with b hb,
  have h₀ : b ≠ 0 := by
  { intro hf,
    rw [hf, quadratic_char_zero, zero_eq_neg] at hb,
    exact one_ne_zero hb, },
  let mul_b : F → F := λ x, b * x,
  have h₁ : ∑ (a : F), quadratic_char F (b * a) = ∑ (a : F), quadratic_char F a :=
  by refine fintype.sum_bijective _ (mul_left_bijective₀ b h₀) _ _ (λ x, rfl),
  simp only [quadratic_char_mul] at h₁,
  rw [← finset.mul_sum, hb, neg_mul, one_mul] at h₁,
  exact eq_zero_of_neg_eq h₁,
end

end quadratic_char

/-!
### The quadratic chacter mod p

We define the quadratic character on `zmod p` as a special case of `quadratic_char`.

We also define the primitive quadratic characters `χ₄`on `zmod 4`
and `χ₈`, `χ₈'` on `zmod 8`.
-/

section quad_char_mod_p

/-- Define the quadratic character mod `p`, for a prime `p`. -/
def zmod.quadratic_char (p : ℕ) [fact p.prime] : (zmod p) → ℤ := quadratic_char (zmod p)

/-- The quadratic character mod `p` is a homomorphism of monoids with zero. -/
def zmod.quadratic_char_hom (p : ℕ) [fact p.prime] : (zmod p) →*₀ ℤ :=
@quadratic_char_hom (zmod p) _ _ _

/-- Define the nontrivial quadratic character on `zmod 4`, `χ₄`.
It corresponds to the extension `ℚ(√-1)/ℚ`. -/
def χ₄ : (zmod 4) →*₀ ℤ :=
{ to_fun := (![0,1,0,-1] : (zmod 4 → ℤ)),
  map_zero' := rfl, map_one' := rfl, map_mul' := by dec_trivial }

/-- Define the first primitive quadratic character on `zmod 8`, `χ₈`.
It corresponds to the extension `ℚ(√2)/ℚ`. -/
def χ₈ : (zmod 8) →*₀ ℤ :=
{ to_fun := (![0,1,0,-1,0,-1,0,1] : (zmod 8 → ℤ)),
  map_zero' := rfl, map_one' := rfl, map_mul' := by dec_trivial }

/-- Define the second primitive quadratic character on `zmod 8`, `χ₈'`.
It corresponds to the extension `ℚ(√-2)/ℚ`. -/
def χ₈' : (zmod 8) →*₀ ℤ :=
{ to_fun := (![0,1,0,1,0,-1,0,-1] : (zmod 8 → ℤ)),
  map_zero' := rfl, map_one' := rfl, map_mul' := by dec_trivial }

end quad_char_mod_p

end char
