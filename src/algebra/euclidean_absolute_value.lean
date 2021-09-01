/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import algebra.absolute_value
import algebra.euclidean_domain
import data.polynomial.field_division

/-!
# Euclidean absolute values

This file defines a bundled type `euclidean_absolute_value R S` of absolute
values compatible with the Euclidean domain structure on its domain `R`.

## Main definitions

 * `euclidean_absolute_value R S` is the type of absolute values on `R` mapping to `S`
    that preserve the order on `R` arising from the Euclidean domain structure.
 * `euclidean_absolute_value.abs` is the "standard" absolute value on `ℤ`,
   mapping negative `x` to `-x`.
 * `euclidean_absolute_value.card_pow_degree` is an Euclidean absolute value on
   `𝔽_q[t]` the ring of polynomials over a finite field of cardinality `q`,
   mapping a polynomial `p` to `q ^ degree p` (where `q ^ degree 0 = 0`)
-/
local infix ` ≺ `:50 := euclidean_domain.r

/-- A `euclidean_absolute_value` is an absolute value `abv : R → S` that is compatible with the
`euclidean_domain` structure on `R`, namely `abv` is strictly monotone with respect to the well
founded relation `≺` on `R`. -/
structure euclidean_absolute_value (R S : Type*) [euclidean_domain R] [ordered_semiring S]
  extends absolute_value R S :=
(map_lt_map_iff' : ∀ x y, to_fun x < to_fun y ↔ x ≺ y)

namespace euclidean_absolute_value

variables {R S : Type*} [euclidean_domain R] [ordered_semiring S]
variables (abv : euclidean_absolute_value R S)

instance : has_coe_to_fun (euclidean_absolute_value R S) :=
{ F := λ _, R → S,
  coe := λ abv, abv.to_fun }

instance : has_coe (euclidean_absolute_value R S) (absolute_value R S) :=
⟨euclidean_absolute_value.to_absolute_value⟩

@[simp, norm_cast] lemma coe_coe : ((abv : absolute_value R S) : R → S) = abv := rfl

-- Copies of the lemmas for absolute values:
protected theorem nonneg (x : R) : 0 ≤ abv x := abv.nonneg' x
@[simp] protected theorem eq_zero {x : R} : abv x = 0 ↔ x = 0 := abv.eq_zero' x
protected theorem add_le (x y : R) : abv (x + y) ≤ abv x + abv y := abv.add_le' x y
@[simp] protected theorem map_mul (x y : R) : abv (x * y) = abv x * abv y := abv.map_mul' x y
protected theorem pos {x : R} (hx : x ≠ 0) : 0 < abv x := (abv : absolute_value R S).pos hx
@[simp] protected theorem pos_iff {x : R} : 0 < abv x ↔ x ≠ 0 := (abv : absolute_value R S).pos_iff
protected theorem ne_zero {x : R} (hx : x ≠ 0) : abv x ≠ 0 := (abv : absolute_value R S).ne_zero hx
@[simp] protected theorem map_zero : abv 0 = 0 := (abv : absolute_value R S).map_zero

@[simp]
lemma map_lt_map_iff {x y : R} : abv x < abv y ↔ x ≺ y := abv.map_lt_map_iff' x y

lemma sub_mod_lt (a : R) {b : R} (hb : b ≠ 0) :
  abv (a % b) < abv b :=
abv.map_lt_map_iff.mpr (euclidean_domain.mod_lt a hb)

@[simp] lemma map_sub_eq_zero_iff (a b : R) : abv (a - b) = 0 ↔ a = b :=
abv.eq_zero.trans sub_eq_zero

section int

open int

-- TODO: generalize to `linear_ordered_euclidean_domain`s if we ever get a definition of those
/-- `abs : ℤ → ℤ` is a Euclidean absolute value -/
protected def abs : euclidean_absolute_value ℤ ℤ :=
{ map_lt_map_iff' := λ x y, show abs x < abs y ↔ nat_abs x < nat_abs y,
    by rw [abs_eq_nat_abs, abs_eq_nat_abs, coe_nat_lt],
  .. absolute_value.abs }

@[simp] lemma abs_to_absolute_value :
  euclidean_absolute_value.abs.to_absolute_value = absolute_value.abs :=
rfl

instance : inhabited (euclidean_absolute_value ℤ ℤ) := ⟨euclidean_absolute_value.abs⟩

end int

section polynomial

variables {Fq : Type*} [field Fq] [fintype Fq]

open polynomial

open_locale classical

/-- `card_pow_degree` is the absolute value on `𝔽_q[t]` sending `f` to `q ^ degree f`.

`card_pow_degree 0` is defined to be `0`. -/
noncomputable def card_pow_degree :
  euclidean_absolute_value (polynomial Fq) ℤ :=
have card_pos : 0 < fintype.card Fq := fintype.card_pos_iff.mpr infer_instance,
have pow_pos : ∀ n, 0 < (fintype.card Fq : ℤ) ^ n := λ n, pow_pos (int.coe_nat_pos.mpr card_pos) n,
{ to_fun := λ p, if p = 0 then 0 else fintype.card Fq ^ p.nat_degree,
  nonneg' := λ p, by { split_ifs, { refl }, exact pow_nonneg (int.coe_zero_le _) _ },
  eq_zero' := λ p, ite_eq_left_iff.trans $ ⟨λ h, by { contrapose! h, exact ⟨h, (pow_pos _).ne'⟩ },
    absurd⟩,
  add_le' := λ p q, begin
    by_cases hp : p = 0, { simp [hp] },
    by_cases hq : q = 0, { simp [hq] },
    by_cases hpq : p + q = 0,
    { simp only [hpq, hp, hq, eq_self_iff_true, if_true, if_false],
      exact add_nonneg (pow_pos _).le (pow_pos _).le },
    simp only [hpq, hp, hq, if_false],
    refine le_trans (pow_le_pow (by linarith) (polynomial.nat_degree_add_le _ _)) _,
    refine le_trans (le_max_iff.mpr _)
      (max_le_add_of_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)),
    exact (max_choice p.nat_degree q.nat_degree).imp (λ h, by rw [h]) (λ h, by rw [h])
  end,
  map_mul' := λ p q, begin
    by_cases hp : p = 0, { simp [hp] },
    by_cases hq : q = 0, { simp [hq] },
    have hpq : p * q ≠ 0 := mul_ne_zero hp hq,
    simp only [hpq, hp, hq, eq_self_iff_true, if_true, if_false,
      polynomial.nat_degree_mul hp hq, pow_add],
  end,
  map_lt_map_iff' := λ p q, begin
    simp only [euclidean_domain.r],
    split_ifs with hp hq hq,
    { simp only [hp, hq, lt_self_iff_false] },
    { simp only [hp, hq, degree_zero, ne.def, bot_lt_iff_ne_bot,
        degree_eq_bot, pow_pos, not_false_iff] },
    { simp only [hp, hq, degree_zero, not_lt_bot, (pow_pos _).not_lt] },
    { rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq, with_bot.coe_lt_coe, pow_lt_pow_iff],
      exact_mod_cast @fintype.one_lt_card Fq _ _ },
  end }

@[simp] lemma card_pow_degree_zero : card_pow_degree (0 : polynomial Fq) = 0 := if_pos rfl

@[simp] lemma card_pow_degree_nonzero (p : polynomial Fq) (hp : p ≠ 0) :
  card_pow_degree p = fintype.card Fq ^ p.nat_degree :=
if_neg hp

end polynomial

end euclidean_absolute_value
