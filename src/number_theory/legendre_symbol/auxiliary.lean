/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import tactic.basic
import field_theory.finite.basic
import field_theory.finite.galois_field
import field_theory.galois
import ring_theory.trace

/-!
# Some auxiliary results

We collect some results here that are not specific to quadratic characters
or Legendre symbols, but are needed in some places there.
They will be moved to appropriate places eventually.
-/

section general

/-- A natural number is odd iff it has residue `1` or `3` mod `4`-/
-- TODO: move this to `data.nat.modeq`, right after `nat.odd_of_mod_four_eq_three`
lemma nat.odd_mod_four_iff {n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3 :=
begin
  refine ⟨_, λ h, or.dcases_on h nat.odd_of_mod_four_eq_one nat.odd_of_mod_four_eq_three⟩,
  have help : ∀ (m : ℕ), 0 ≤ m → m < 4 → m % 2 = 1 → m = 1 ∨ m = 3 := dec_trivial,
  exact λ hn, help (n % 4) zero_le' (nat.mod_lt n (by norm_num))
               ((nat.mod_mod_of_dvd n (by norm_num : 2 ∣ 4)).trans hn),
end

-- Auxiliary stuff for monoids

/-- If `x ^ n = 1`, then `x ^ m` is the same as `x ^ (m % n)` -/
-- TODO: move this to `algebra.group_power.basic`, right after `pow_sub_mul_pow`
@[to_additive nsmul_eq_mod_nsmul "If `n • x = 0`, then `m • x` is the same as `(m % n) • x`"]
lemma pow_eq_pow_mod {M : Type*} [monoid M] {x : M} (m : ℕ) {n : ℕ} (h : x ^ n = 1) :
  x ^ m = x ^ (m % n) :=
begin
  nth_rewrite 0 [← nat.div_add_mod m n],
  rw [pow_add, pow_mul, h, one_pow, one_mul],
end

/-- We define the inverse as a `monoid_with_zero_hom` by extending the inverse map by zero
on non-units. -/
-- This exists for groups with zero (`inv_monoid_with_zero_hom`)
-- TODO: put the following two definitions in `algebra.group_with_zero.basic`,
-- before `inv_monoid_with_zero_hom`
noncomputable
def monoid_with_zero.inverse {M : Type*} [comm_monoid_with_zero M] :
  M →*₀ M :=
{ to_fun := ring.inverse,
  map_zero' := ring.inverse_zero _,
  map_one' := ring.inverse_one _,
  map_mul' := λ x y, (ring.mul_inverse_rev x y).trans (mul_comm _ _) }

/-- We define `x ↦ x^n` (for positive `n : ℕ`) as a `monoid_with_zero_hom` -/
def pow_monoid_with_zero_hom {M : Type*} [comm_monoid_with_zero M] {n : ℕ} (hn : 0 < n) :
  M →*₀ M :=
{ map_zero' := zero_pow hn,
  ..pow_monoid_hom n }

end general

-- Auxiliary stuff for rings

section ring

/-- We have `2 ≠ 0` in a nontrivial ring whose characteristic is not `2`. -/
-- Note: there is `two_ne_zero` (assuming `[ordered_semiring]`)
-- and `two_ne_zero'`(assuming `[char_zero]`), which both don't fit the needs here.
-- TODO: move this and the next three lemmas to `algebra.char_p.basic`,
-- before `char_p.neg_one_ne_one`.
@[protected]
lemma ring.two_ne_zero {R : Type*} [non_assoc_semiring R] [nontrivial R] (hR : ring_char R ≠ 2) :
  (2 : R) ≠ 0 :=
begin
  rw [ne.def, (by norm_cast : (2 : R) = (2 : ℕ)), ring_char.spec, nat.dvd_prime nat.prime_two],
  exact mt (or_iff_left hR).mp char_p.ring_char_ne_one,
end

/-- Characteristic `≠ 2` and nontrivial implies that `-1 ≠ 1`. -/
-- We have `char_p.neg_one_ne_one`, which assumes `[ring R] (p : ℕ) [char_p R p] [fact (2 < p)]`.
-- This is a version using `ring_char` instead.
lemma ring.neg_one_ne_one_of_char_ne_two {R : Type*} [non_assoc_ring R] [nontrivial R]
 (hR : ring_char R ≠ 2) :
  (-1 : R) ≠ 1 :=
λ h, ring.two_ne_zero hR (neg_eq_iff_add_eq_zero.mp h)

/-- Characteristic `≠ 2` in a domain implies that `-a = a` iff `a = 0`. -/
lemma ring.eq_self_iff_eq_zero_of_char_ne_two {R : Type*} [non_assoc_ring R] [nontrivial R]
 [no_zero_divisors R] (hR : ring_char R ≠ 2) {a : R} :
  -a = a ↔ a = 0 :=
⟨λ h, (mul_eq_zero.mp $ (two_mul a).trans $ neg_eq_iff_add_eq_zero.mp h).resolve_left
         (ring.two_ne_zero hR),
 λ h, ((congr_arg (λ x, - x) h).trans neg_zero).trans h.symm⟩

/-- If two integers from `{0, 1, -1}` result in equal elements in a ring `R`
that is nontrivial and of characteristic not `2`, then they are equal. -/
lemma int.cast_inj_on_of_ring_char_ne_two {R : Type*} [non_assoc_ring R] [nontrivial R]
  (hR : ring_char R ≠ 2) :
  ({0, 1, -1} : set ℤ).inj_on (coe : ℤ → R) :=
begin
  intros a ha b hb h,
  apply eq_of_sub_eq_zero,
  by_contra hf,
  change a = 0 ∨ a = 1 ∨ a = -1 at ha,
  change b = 0 ∨ b = 1 ∨ b = -1 at hb,
  have hh : a - b = 1 ∨ b - a = 1 ∨ a - b = 2 ∨ b - a = 2 := by
  { rcases ha with ha | ha | ha; rcases hb with hb | hb | hb,
    swap 5, swap 9, -- move goals with `a = b` to the front
    iterate 3 { rw [ha, hb, sub_self] at hf, tauto, }, -- 6 goals remain
    all_goals { rw [ha, hb], norm_num, }, },
  have h' : ((a - b : ℤ) : R) = 0 := by exact_mod_cast sub_eq_zero_of_eq h,
  have h'' : ((b - a : ℤ) : R) = 0 := by exact_mod_cast sub_eq_zero_of_eq h.symm,
  rcases hh with hh | hh | hh | hh,
  { rw [hh, (by norm_cast : ((1 : ℤ) : R) = 1)] at h', exact one_ne_zero h', },
  { rw [hh, (by norm_cast : ((1 : ℤ) : R) = 1)] at h'', exact one_ne_zero h'', },
  { rw [hh, (by norm_cast : ((2 : ℤ) : R) = 2)] at h', exact ring.two_ne_zero hR h', },
  { rw [hh, (by norm_cast : ((2 : ℤ) : R) = 2)] at h'', exact ring.two_ne_zero hR h'', },
end

/-- If `ring_char R = 2`, where `R` is a finite reduced commutative ring,
then every `a : R` is a square. -/
-- SUGGESTION: move this to `algebra.char_p.basic`, after `frobenius_inj`
-- ALTERNATIVE: move to `algebra.char_p.two` (and rename to `char_two.is_square`?)
lemma is_square_of_char_two' {R : Type*} [fintype R] [comm_ring R] [is_reduced R] [char_p R 2]
 (a : R) : is_square a :=
exists_imp_exists (λ b h, pow_two b ▸ eq.symm h) $
  ((fintype.bijective_iff_injective_and_card _).mpr ⟨frobenius_inj R 2, rfl⟩).surjective a

/-- A prime `p` is a unit in a finite commutative ring `R`
iff it does not divide the characteristic. -/
-- TODO: move the following three lemmas to `algebra.char_p.basic`
lemma is_unit_iff_not_dvd_char (R : Type*) [comm_ring R] [fintype R] (p : ℕ) [fact p.prime] :
  is_unit (p : R) ↔ ¬ p ∣ ring_char R :=
begin
  have hch := char_p.cast_eq_zero R (ring_char R),
  split,
  { rintros h₁ ⟨q, hq⟩,
    rcases is_unit.exists_left_inv h₁ with ⟨a, ha⟩,
    have h₃ : ¬ ring_char R ∣ q :=
    begin
      rintro ⟨r, hr⟩,
      rw [hr, ← mul_assoc, mul_comm p, mul_assoc] at hq,
      nth_rewrite 0 ← mul_one (ring_char R) at hq,
      exact nat.prime.not_dvd_one (fact.out p.prime)
             ⟨r, mul_left_cancel₀ (char_p.char_ne_zero_of_fintype R (ring_char R)) hq⟩,
    end,
    have h₄ := mt (char_p.int_cast_eq_zero_iff R (ring_char R) q).mp,
    apply_fun (coe : ℕ → R) at hq,
    apply_fun ((*) a) at hq,
    rw [nat.cast_mul, hch, mul_zero, ← mul_assoc, ha, one_mul] at hq,
    norm_cast at h₄,
    exact h₄ h₃ hq.symm, },
  { intro h,
    rcases nat.is_coprime_iff_coprime.mpr ((nat.prime.coprime_iff_not_dvd (fact.out _)).mpr h)
      with ⟨a, b, hab⟩,
    apply_fun (coe : ℤ → R) at hab,
    push_cast at hab,
    rw [hch, mul_zero, add_zero, mul_comm] at hab,
    exact is_unit_of_mul_eq_one (p : R) a hab, },
end

/-- The prime divisors of the characteristic of a finite commutative ring are exactly
the prime divisors of its cardinality. -/
lemma prime_dvd_char_iff_dvd_card {R : Type*} [comm_ring R] [fintype R] (p : ℕ) [fact p.prime] :
  p ∣ ring_char R ↔ p ∣ fintype.card R :=
begin
  refine ⟨λ h, h.trans $ int.coe_nat_dvd.mp $ (char_p.int_cast_eq_zero_iff R (ring_char R)
    (fintype.card R)).mp $ char_p.cast_card_eq_zero R, λ h, _⟩,
  by_contra h₀,
  rcases exists_prime_add_order_of_dvd_card p h with ⟨r, hr⟩,
  have hr₁ := add_order_of_nsmul_eq_zero r,
  rw [hr, nsmul_eq_mul] at hr₁,
  rcases is_unit.exists_left_inv ((is_unit_iff_not_dvd_char R p).mpr h₀) with ⟨u, hu⟩,
  apply_fun ((*) u) at hr₁,
  rw [mul_zero, ← mul_assoc, hu, one_mul] at hr₁,
  exact mt add_monoid.order_of_eq_one_iff.mpr
          (ne_of_eq_of_ne hr (nat.prime.ne_one (fact.out p.prime))) hr₁,
end

/-- A prime that does not divide the cardinality of a finite commutative ring `R`
is a unit in `R`. -/
lemma not_is_unit_prime_of_dvd_card {R : Type*} [comm_ring R] [fintype R] (p : ℕ) [fact p.prime]
 (hp : p ∣ fintype.card R) : ¬ is_unit (p : R) :=
mt (is_unit_iff_not_dvd_char R p).mp (not_not.mpr ((prime_dvd_char_iff_dvd_card p).mpr hp))

end ring

-- Auxiliary stuff for finite fields

section finite_field

namespace finite_field

variables {F : Type*} [field F] [fintype F]

/-- In a finite field of characteristic `2`, all elements are squares. -/
-- TODO: move the following lemmas (up to and incluiding `exists_nonsquare`)
-- to the end of `field_theory.finite.basic`
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
    exact (nat.prime.eq_two_or_odd hp).resolve_right (ne_of_eq_of_ne hev zero_ne_one), },
end

lemma even_card_of_char_two (hF : ring_char F = 2) : fintype.card F % 2 = 0 :=
even_card_iff_char_two.mp hF

lemma odd_card_of_char_ne_two (hF : ring_char F ≠ 2) : fintype.card F % 2 = 1 :=
nat.mod_two_ne_zero.mp (mt even_card_iff_char_two.mpr hF)

/-- If `F` has odd characteristic, then for nonzero `a : F`, we have that `a ^ (#F / 2) = ±1`. -/
lemma pow_dichotomy (hF : ring_char F ≠ 2) {a : F} (ha : a ≠ 0) :
  a ^ (fintype.card F / 2) = 1 ∨ a ^ (fintype.card F / 2) = -1 :=
begin
  have h₁ := finite_field.pow_card_sub_one_eq_one a ha,
  rw [← nat.two_mul_odd_div_two (finite_field.odd_card_of_char_ne_two hF),
      mul_comm, pow_mul, pow_two] at h₁,
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
    apply_fun (@coe Fˣ F _) using units.ext,
    { push_cast,
      exact finite_field.pow_card_sub_one_eq_one (y : F) (units.ne_zero y), }, },
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
  split,
  { rintro ⟨y, hy⟩, exact ⟨y, hy⟩ },
  { rintro ⟨y, rfl⟩,
    have hy : y ≠ 0, { rintro rfl, simpa [zero_pow] using ha, },
    refine ⟨units.mk0 y hy, _⟩, simp, }
end

/-- In a finite field of odd characteristic, not every element is a square. -/
lemma exists_nonsquare (hF : ring_char F ≠ 2) : ∃ (a : F), ¬ is_square a :=
begin
  -- idea: the squaring map on `F` is not injetive, hence not surjective
  let sq : F → F := λ x, x ^ 2,
  have h : ¬ function.injective sq,
  { simp only [function.injective, not_forall, exists_prop],
    use [-1, 1],
    split,
    { simp only [sq, one_pow, neg_one_sq], },
    { exact ring.neg_one_ne_one_of_char_ne_two hF, }, },
  have h₁ := mt (fintype.injective_iff_surjective.mpr) h, -- sq not surjective
  push_neg at h₁,
  cases h₁ with a h₁,
  use a,
  simp only [is_square, sq, not_exists, ne.def] at h₁ ⊢,
  intros b hb,
  rw ← pow_two at hb,
  exact h₁ b hb.symm,
end

/-- The trace map from a finite field of characteristic `p` to `zmod p` -/
-- These two lemmas depend on `ring_theory.trace` and finite fields.
-- SUGGESTION: move them to the end of `ring_theory.trace` (this would
-- require adding `import field_theory.finite.basic` to it)
-- ALTERNATIVE: add a new file `field_theory.finite.trace` for them.
noncomputable
def trace_to_zmod (F : Type*) [field F] :
 F →ₗ[zmod (ring_char F)] zmod (ring_char F) :=
begin
  letI := zmod.algebra F (ring_char F),
  exact algebra.trace (zmod (ring_char F)) F,
end

/-- The trace map from a finite field to its prime field is nongedenerate. -/
lemma trace_to_zmod_nondegenerate (F : Type*) [field F] [fintype F] {a : F}
 (ha : a ≠ 0) : ∃ b : F, trace_to_zmod F (a * b) ≠ 0 :=
begin
  haveI : fact (ring_char F).prime := ⟨char_p.char_is_prime F _⟩,
  have htr := trace_form_nondegenerate (zmod (ring_char F)) F a,
  simp_rw [algebra.trace_form_apply] at htr,
  simp_rw [trace_to_zmod],
  by_contra' hf,
  exact ha (htr hf),
end

end finite_field

end finite_field
