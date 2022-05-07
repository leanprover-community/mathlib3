/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import tactic.basic
import field_theory.finite.basic
import data.int.range

/-!
# Quadratic characters of finite fields

This file defines the quadratic character on a finite field `F` and proves
some basic statements about it.

## Tags

quadratic character
-/

/-!
### Some general results, mostly on finite fields

We collect some results here that are not specific to quadratic characters
but are needed below. They will be moved to appropriate places eventually.
-/

section general

/-- A natural number is odd iff it has residue `1` or `3` mod `4`-/
lemma nat.odd_mod_four_iff {n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3 :=
begin
  split,
  { have help : ∀ (m : ℕ), 0 ≤ m → m < 4 → m % 2 = 1 → m = 1 ∨ m = 3 := dec_trivial,
    intro hn,
    rw [← nat.mod_mod_of_dvd n (by norm_num : 2 ∣ 4)] at hn,
    exact help (n % 4) zero_le' (nat.mod_lt n (by norm_num)) hn, },
  { intro h,
    cases h with h h,
    { exact nat.odd_of_mod_four_eq_one h, },
    { exact nat.odd_of_mod_four_eq_three h }, },
end

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

/-- The finite field `F` has even cardinality iff it has characteristic `2`. -/
lemma even_card_iff_char_two : ring_char F = 2 ↔ fintype.card F % 2 = 0 :=
begin
  rcases finite_field.card F (ring_char F) with ⟨n, hp, h⟩,
  rw [h, nat.pow_mod],
  split,
  { intro hF,
    rw hF,
    simp only [nat.bit0_mod_two, zero_pow', ne.def, pnat.ne_zero, not_false_iff, nat.zero_mod], },
  { rw [← nat.even_iff, nat.even_pow],
    rintros ⟨hev, hnz⟩,
    rw [nat.even_iff, nat.mod_mod] at hev,
    cases (nat.prime.eq_two_or_odd hp) with h₁ h₁,
    { exact h₁, },
    { exact false.rec (ring_char F = 2) (one_ne_zero ((eq.symm h₁).trans hev)), }, },
end

lemma even_card_of_char_two (hF : ring_char F = 2) : fintype.card F % 2 = 0 :=
even_card_iff_char_two.mp hF

lemma odd_card_of_char_ne_two (hF : ring_char F ≠ 2) : fintype.card F % 2 = 1 :=
nat.mod_two_ne_zero.mp (mt even_card_iff_char_two.mpr hF)

/-- Characteristic `≠ 2` implies that `-1 ≠ 1`. -/
lemma neg_one_ne_one_of_char_ne_two (hF : ring_char F ≠ 2) : (-1 : F) ≠ 1 :=
begin
  have hc := char_p.char_is_prime F (ring_char F),
  haveI hF' : fact (2 < ring_char F) := ⟨ lt_of_le_of_ne (nat.prime.two_le hc) (ne.symm hF) ⟩,
  exact char_p.neg_one_ne_one _ (ring_char F),
end

/-- Characteristic `≠ 2` implies that `-a ≠ a` when `a ≠ 0`. -/
lemma neg_ne_self_of_char_ne_two (hF : ring_char F ≠ 2) {a : F} (ha : a ≠ 0) : a ≠ -a :=
begin
  intro hf,
  apply (neg_one_ne_one_of_char_ne_two hF).symm,
  rw [eq_neg_iff_add_eq_zero, ←two_mul, mul_one],
  rw [eq_neg_iff_add_eq_zero, ←two_mul, mul_eq_zero] at hf,
  exact hf.resolve_right ha,
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
lemma unit_is_square_iff (hF : ring_char F ≠ 2) (a : Fˣ) :
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
    { push_cast,
      exact finite_field.pow_card_sub_one_eq_one (y : F) (units.ne_zero y), },
    { exact units.ext, }, },
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
        (finite_field.unit_is_square_iff hF (units.mk0 a ha)),
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
  { simp only [function.injective, not_forall, exists_prop],
    use [-1, 1],
    split,
    { simp only [sq, one_pow, neg_one_sq], },
    { exact finite_field.neg_one_ne_one_of_char_ne_two hF, }, },
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

/-- Define the quadratic character with values in ℤ on a monoid with zero `α`.
It takes the value zero at zero; for non-zero argument `a : α`, it is `1`
if `a` is a square, otherwise it is `-1`.

This only deserves the name "character" when it is multiplicative,
e.g., when `α` is a finite field. See `quadratic_char_mul`.
-/
def quadratic_char (α : Type*) [monoid_with_zero α] [decidable_eq α]
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

variables {F : Type*} [field F] [fintype F] [decidable_eq F]

/-- Some basic API lemmas -/
lemma quadratic_char_eq_zero_iff (a : F) : quadratic_char F a = 0 ↔ a = 0 :=
begin
  simp only [quadratic_char],
  by_cases ha : a = 0,
  { simp only [ha, eq_self_iff_true, if_true], },
  { simp only [ha, if_false, iff_false],
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
by { simp only [quadratic_char, ha, (dec_trivial : (-1 : ℤ) ≠ 1), if_false, ite_eq_left_iff],
     tauto, }

/-- The quadratic character takes the value `1` on nonzero squares. -/
lemma quadratic_char_sq_one' {a : F} (ha : a ≠ 0) : quadratic_char F (a ^ 2) = 1 :=
by simp only [quadratic_char, ha, pow_eq_zero_iff, nat.succ_pos', is_square_sq, if_true, if_false]

/-- If `ring_char F = 2`, then `quadratic_char F` takes the value `1` on nonzero elements. -/
lemma quadratic_char_eq_one_of_char_two (hF : ring_char F = 2) {a : F} (ha : a ≠ 0) :
  quadratic_char F a = 1 :=
begin
  simp only [quadratic_char, ha, if_false, ite_eq_left_iff],
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
@[simps] def quadratic_char_hom : F →*₀ ℤ :=
{ to_fun := quadratic_char F,
  map_zero' := quadratic_char_zero,
  map_one' := quadratic_char_one,
  map_mul' := quadratic_char_mul }

/-- The square of the quadratic character on nonzero arguments is `1`. -/
lemma quadratic_char_sq_one {a : F} (ha : a ≠ 0) : (quadratic_char F a) ^ 2 = 1 :=
by rwa [pow_two, ← quadratic_char_mul, ← pow_two, quadratic_char_sq_one']

/-- The quadratic character is `1` or `-1` on nonzero arguments. -/
lemma quadratic_char_dichotomy {a : F} (ha : a ≠ 0) :
  quadratic_char F a = 1 ∨ quadratic_char F a = -1 :=
(sq_eq_one_iff (quadratic_char F a)).mp (quadratic_char_sq_one ha)

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
  { simp only [ha, is_square_zero, quadratic_char_zero, zero_eq_neg, one_ne_zero, not_true], },
  { rw [quadratic_char_eq_neg_one_iff_not_one ha, quadratic_char_one_iff_is_square ha] },
end

/-- If `F` has odd characteristic, then `quadratic_char F` takes the value `-1`. -/
lemma quadratic_char_exists_neg_one (hF : ring_char F ≠ 2) : ∃ a, quadratic_char F a = -1 :=
(finite_field.exists_nonsquare hF).imp (λ b h₁, quadratic_char_neg_one_iff_not_is_square.mpr h₁)

/-- The number of solutions to `x^2 = a` is determined by the quadratic character. -/
lemma quadratic_char_card_sqrts (hF : ring_char F ≠ 2) (a : F) :
  ↑{x : F | x^2 = a}.to_finset.card = quadratic_char F a + 1 :=
begin
  -- we consider the cases `a = 0`, `a` is a nonzero square and `a` is a nonsquare in turn
  by_cases h₀ : a = 0,
  { simp only [h₀, pow_eq_zero_iff, nat.succ_pos', int.coe_nat_succ, int.coe_nat_zero, zero_add,
               quadratic_char_zero, add_zero, set.set_of_eq_eq_singleton, set.to_finset_card,
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
      simp only [h₁, finset.card_doubleton (finite_field.neg_ne_self_of_char_ne_two hF h₀),
                 list.to_finset_cons, list.to_finset_nil, insert_emptyc_eq, int.coe_nat_succ,
                 int.coe_nat_zero, zero_add], },
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
begin
  cases (quadratic_char_exists_neg_one hF) with b hb,
  have h₀ : b ≠ 0 := by
  { intro hf,
    rw [hf, quadratic_char_zero, zero_eq_neg] at hb,
    exact one_ne_zero hb, },
  have h₁ : ∑ (a : F), quadratic_char F (b * a) = ∑ (a : F), quadratic_char F a :=
    fintype.sum_bijective _ (mul_left_bijective₀ b h₀) _ _ (λ x, rfl),
  simp only [quadratic_char_mul] at h₁,
  rw [← finset.mul_sum, hb, neg_mul, one_mul] at h₁,
  exact eq_zero_of_neg_eq h₁,
end

end quadratic_char

end char

/-!
### Quadratic characters mod 4 and 8

We define the primitive quadratic characters `χ₄`on `zmod 4`
and `χ₈`, `χ₈'` on `zmod 8`.
-/

namespace zmod

section quad_char_mod_p

/-- Define the nontrivial quadratic character on `zmod 4`, `χ₄`.
It corresponds to the extension `ℚ(√-1)/ℚ`. -/
@[simps] def χ₄ : (zmod 4) →*₀ ℤ :=
{ to_fun := (![0,1,0,-1] : (zmod 4 → ℤ)),
  map_zero' := rfl, map_one' := rfl, map_mul' := dec_trivial }

/-- An explicit description of `χ₄` on integers / naturals -/
lemma χ₄_int_eq_if_mod_four (n : ℤ) : χ₄ n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 :=
begin
  have help : ∀ (m : ℤ), 0 ≤ m → m < 4 → χ₄ m = if m % 2 = 0 then 0 else if m = 1 then 1 else -1 :=
  dec_trivial,
  rw [← int.mod_mod_of_dvd n (by norm_num : (2 : ℤ) ∣ 4), ← zmod.int_cast_mod n 4],
  exact help (n % 4) (int.mod_nonneg n (by norm_num)) (int.mod_lt n (by norm_num)),
end

lemma χ₄_nat_eq_if_mod_four (n : ℕ) : χ₄ n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 :=
by exact_mod_cast χ₄_int_eq_if_mod_four n

/-- Alternative description for odd `n : ℕ` in terms of powers of `-1` -/
lemma χ₄_eq_neg_one_pow {n : ℕ} (hn : n % 2 = 1) : χ₄ n = (-1)^(n / 2) :=
begin
  rw χ₄_nat_eq_if_mod_four,
  simp only [hn, nat.one_ne_zero, if_false],
  have h := (nat.div_add_mod n 4).symm,
  cases (nat.odd_mod_four_iff.mp hn) with h4 h4,
  { split_ifs,
    rw h4 at h,
    rw [h],
    nth_rewrite 0 (by norm_num : 4 = 2 * 2),
    rw [mul_assoc, add_comm, nat.add_mul_div_left _ _ (by norm_num : 0 < 2), pow_add, pow_mul],
    norm_num, },
  { split_ifs,
    { exfalso,
      rw h4 at h_1,
      norm_num at h_1, },
    { rw h4 at h,
      rw [h],
      nth_rewrite 0 (by norm_num : 4 = 2 * 2),
      rw [mul_assoc, add_comm, nat.add_mul_div_left _ _ (by norm_num : 0 < 2), pow_add, pow_mul],
      norm_num, }, },
end

/-- Define the first primitive quadratic character on `zmod 8`, `χ₈`.
It corresponds to the extension `ℚ(√2)/ℚ`. -/
@[simps] def χ₈ : (zmod 8) →*₀ ℤ :=
{ to_fun := (![0,1,0,-1,0,-1,0,1] : (zmod 8 → ℤ)),
  map_zero' := rfl, map_one' := rfl, map_mul' := by dec_trivial }

/-- Define the second primitive quadratic character on `zmod 8`, `χ₈'`.
It corresponds to the extension `ℚ(√-2)/ℚ`. -/
@[simps] def χ₈' : (zmod 8) →*₀ ℤ :=
{ to_fun := (![0,1,0,1,0,-1,0,-1] : (zmod 8 → ℤ)),
  map_zero' := rfl, map_one' := rfl, map_mul' := by dec_trivial }

end quad_char_mod_p

end zmod

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
  have h₁ : (-1 : F) ≠ 0 := by { rw neg_ne_zero, exact one_ne_zero },
  have h := quadratic_char_eq_pow_of_char_ne_two hF h₁,
  rw [h, χ₄_eq_neg_one_pow (finite_field.odd_card_of_char_ne_two hF)],
  set n := fintype.card F / 2,
  cases (nat.even_or_odd n) with h₂ h₂,
  { simp only [even.neg_one_pow h₂, eq_self_iff_true, if_true], },
  { simp only [odd.neg_one_pow h₂, ite_eq_right_iff],
    exact λ (hf : -1 = 1),
            false.rec (1 = -1) (finite_field.neg_one_ne_one_of_char_ne_two hF hf), },
end

/-- The interpretation in terms of whether `-1` is a square in `F` -/
lemma is_square_neg_one_iff : is_square (-1 : F) ↔ fintype.card F % 4 ≠ 3 :=
begin
  classical, -- suggested by the linter (instead of `[decidable_eq F]`)
  by_cases hF : (ring_char F = 2),
  { simp only [finite_field.is_square_of_char_two hF, ne.def, true_iff],
    exact (λ hf, one_ne_zero ((nat.odd_of_mod_four_eq_three hf).symm.trans
                                (finite_field.even_card_of_char_two hF)))},
  { have h₁ : (-1 : F) ≠ 0 := by { rw neg_ne_zero, exact one_ne_zero },
    have h₂ := finite_field.odd_card_of_char_ne_two hF,
    rw [← quadratic_char_one_iff_is_square h₁, quadratic_char_neg_one hF,
        χ₄_nat_eq_if_mod_four, h₂],
    have h₃ := nat.odd_mod_four_iff.mp h₂,
    simp only [nat.one_ne_zero, if_false, ite_eq_left_iff, ne.def],
    norm_num,
    split,
    { intros h h',
      have t := (of_not_not h).symm.trans h',
      norm_num at t, },
    exact λ h h', h' ((or_iff_left h).mp h₃), },
end

end char

end special_values
