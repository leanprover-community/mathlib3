/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import tactic.basic
import field_theory.finite.basic

/-!
# Some auxiliary results

We collect some results here that are not specific to quadratic characters
or Legendre symbols, but are needed in some places there.
They will be moved to appropriate places eventually.
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
