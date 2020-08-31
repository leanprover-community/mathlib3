/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro, Johan Commelin
-/
import data.int.modeq
import data.zmod.basic
import linear_algebra.adic_completion
import data.padics.padic_numbers
import ring_theory.discrete_valuation_ring

/-!
# p-adic integers

This file defines the p-adic integers `ℤ_p` as the subtype of `ℚ_p` with norm `≤ 1`.
We show that `ℤ_p`
* is complete
* is nonarchimedean
* is a normed ring
* is a local ring
* is a discrete valuation ring
* has a ring hom to `ℤ/p^nℤ` for each `n`

## Important definitions

* `padic_int` : the type of p-adic numbers
* `to_zmod`: ring hom to `ℤ/pℤ`
* `to_zmod_pow` : ring hom to `ℤ/p^nℤ`

## Notation

We introduce the notation `ℤ_[p]` for the p-adic integers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact (nat.prime p)] as a type class argument.

Coercions into `ℤ_p` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouêva, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, p-adic integer
-/

open nat padic metric local_ring
noncomputable theory
open_locale classical

/-- The p-adic integers ℤ_p are the p-adic numbers with norm ≤ 1. -/
def padic_int (p : ℕ) [fact p.prime] := {x : ℚ_[p] // ∥x∥ ≤ 1}
notation `ℤ_[`p`]` := padic_int p

namespace padic_int
variables {p : ℕ} [fact p.prime]

instance : has_coe ℤ_[p] ℚ_[p] := ⟨subtype.val⟩

@[ext] lemma ext {x y : ℤ_[p]} : (x : ℚ_[p]) = y → x = y := subtype.ext_iff_val.2

/-- Addition on ℤ_p is inherited from ℚ_p. -/
instance : has_add ℤ_[p] :=
⟨λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x+y,
    le_trans (padic_norm_e.nonarchimedean _ _) (max_le_iff.2 ⟨hx,hy⟩)⟩⟩

/-- Multiplication on ℤ_p is inherited from ℚ_p. -/
instance : has_mul ℤ_[p] :=
⟨λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x*y,
    begin rw padic_norm_e.mul, apply mul_le_one; {assumption <|> apply norm_nonneg} end⟩⟩

/-- Negation on ℤ_p is inherited from ℚ_p. -/
instance : has_neg ℤ_[p] :=
⟨λ ⟨x, hx⟩, ⟨-x, by simpa⟩⟩

/-- Zero on ℤ_p is inherited from ℚ_p. -/
instance : has_zero ℤ_[p] :=
⟨⟨0, by norm_num⟩⟩

instance : inhabited ℤ_[p] := ⟨0⟩

/-- One on ℤ_p is inherited from ℚ_p. -/
instance : has_one ℤ_[p] :=
⟨⟨1, by norm_num⟩⟩

@[simp] lemma mk_zero {h} : (⟨0, h⟩ : ℤ_[p]) = (0 : ℤ_[p]) := rfl

@[simp] lemma val_eq_coe (z : ℤ_[p]) : z.val = z := rfl

@[simp, norm_cast] lemma coe_add : ∀ (z1 z2 : ℤ_[p]), ((z1 + z2 : ℤ_[p]) : ℚ_[p]) = z1 + z2
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp, norm_cast] lemma coe_mul : ∀ (z1 z2 : ℤ_[p]), ((z1 * z2 : ℤ_[p]) : ℚ_[p]) = z1 * z2
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp, norm_cast] lemma coe_neg : ∀ (z1 : ℤ_[p]), ((-z1 : ℤ_[p]) : ℚ_[p]) = -z1
| ⟨_, _⟩ := rfl

@[simp, norm_cast] lemma coe_one : ((1 : ℤ_[p]) : ℚ_[p]) = 1 := rfl

@[simp, norm_cast] lemma coe_coe : ∀ n : ℕ, ((n : ℤ_[p]) : ℚ_[p]) = n
| 0 := rfl
| (k+1) := by simp [coe_coe]


@[simp, norm_cast] lemma coe_coe_int : ∀ (z : ℤ), ((z : ℤ_[p]) : ℚ_[p]) = z
| (int.of_nat n) := by simp
| -[1+n] := by simp

@[simp, norm_cast] lemma coe_zero : ((0 : ℤ_[p]) : ℚ_[p]) = 0 := rfl

instance : ring ℤ_[p] :=
begin
  refine { add := (+),
           mul := (*),
           neg := has_neg.neg,
           zero := 0,
           one := 1,
           .. };
  intros; ext; simp; ring
end

@[simp, norm_cast] lemma coe_sub : ∀ (z1 z2 : ℤ_[p]), (↑(z1 - z2) : ℚ_[p]) = ↑z1 - ↑z2
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp, norm_cast] lemma cast_pow (x : ℤ_[p]) : ∀ (n : ℕ), (↑(x^n) : ℚ_[p]) = (↑x : ℚ_[p])^n
| 0 := by simp
| (k+1) := by simp [monoid.pow, pow]; congr; apply cast_pow

@[simp] lemma mk_coe : ∀ (k : ℤ_[p]), (⟨k, k.2⟩ : ℤ_[p]) = k
| ⟨_, _⟩ := rfl

/-- The inverse of a p-adic integer with norm equal to 1 is also a p-adic integer. Otherwise, the
inverse is defined to be 0. -/
def inv : ℤ_[p] → ℤ_[p]
| ⟨k, _⟩ := if h : ∥k∥ = 1 then ⟨1/k, by simp [h]⟩ else 0

instance : char_zero ℤ_[p] :=
{ cast_injective :=
  λ m n h, cast_injective $
  show (m:ℚ_[p]) = n, by { rw subtype.ext_iff at h, norm_cast at h, exact h } }


@[simp, norm_cast] lemma coe_int_eq (z1 z2 : ℤ) : (z1 : ℤ_[p]) = z2 ↔ z1 = z2 :=
suffices (z1 : ℚ_[p]) = z2 ↔ z1 = z2, from iff.trans (by norm_cast) this,
by norm_cast

end padic_int

section instances
variables {p : ℕ} [fact p.prime]

instance : metric_space ℤ_[p] := subtype.metric_space

instance : has_norm ℤ_[p] := ⟨λ z, ∥(z : ℚ_[p])∥⟩

lemma padic_norm_z {z : ℤ_[p]} : ∥z∥ = ∥(z : ℚ_[p])∥ := rfl

instance : normed_ring ℤ_[p] :=
{ dist_eq := λ ⟨_, _⟩ ⟨_, _⟩, rfl,
  norm_mul := λ ⟨_, _⟩ ⟨_, _⟩, norm_mul_le _ _ }

instance padic_norm_z.is_absolute_value : is_absolute_value (λ z : ℤ_[p], ∥z∥) :=
{ abv_nonneg := norm_nonneg,
  abv_eq_zero := λ ⟨_, _⟩, by simp [norm_eq_zero],
  abv_add := λ ⟨_,_⟩ ⟨_, _⟩, norm_add_le _ _,
  abv_mul := λ _ _, by simp [padic_norm_z] }

protected lemma padic_int.pmul_comm : ∀ z1 z2 : ℤ_[p], z1*z2 = z2*z1
| ⟨q1, h1⟩ ⟨q2, h2⟩ := show (⟨q1*q2, _⟩ : ℤ_[p]) = ⟨q2*q1, _⟩, by simp [mul_comm]

instance : comm_ring ℤ_[p] :=
{ mul_comm := padic_int.pmul_comm,
  ..padic_int.ring }

protected lemma padic_int.zero_ne_one : (0 : ℤ_[p]) ≠ 1 :=
show (⟨(0 : ℚ_[p]), _⟩ : ℤ_[p]) ≠ ⟨(1 : ℚ_[p]), _⟩, from mt subtype.ext_iff_val.1 zero_ne_one

protected lemma padic_int.eq_zero_or_eq_zero_of_mul_eq_zero :
          ∀ (a b : ℤ_[p]), a * b = 0 → a = 0 ∨ b = 0
| ⟨a, ha⟩ ⟨b, hb⟩ := λ h : (⟨a * b, _⟩ : ℤ_[p]) = ⟨0, _⟩,
have a * b = 0, from subtype.ext_iff_val.1 h,
(mul_eq_zero.1 this).elim
  (λ h1, or.inl (by simp [h1]; refl))
  (λ h2, or.inr (by simp [h2]; refl))

instance : integral_domain ℤ_[p] :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := padic_int.eq_zero_or_eq_zero_of_mul_eq_zero,
  exists_pair_ne := ⟨0, 1, padic_int.zero_ne_one⟩,
  ..padic_int.comm_ring }

end instances

namespace padic_norm_z

variables {p : ℕ} [fact p.prime]

lemma le_one : ∀ z : ℤ_[p], ∥z∥ ≤ 1
| ⟨_, h⟩ := h

@[simp] lemma one : ∥(1 : ℤ_[p])∥ = 1 := by simp [norm, padic_norm_z]

@[simp] lemma mul (z1 z2 : ℤ_[p]) : ∥z1 * z2∥ = ∥z1∥ * ∥z2∥ :=
by simp [padic_norm_z]

@[simp] lemma pow (z : ℤ_[p]) : ∀ n : ℕ, ∥z^n∥ = ∥z∥^n
| 0 := by simp
| (k+1) := show ∥z*z^k∥ = ∥z∥*∥z∥^k, by {rw mul, congr, apply pow}

theorem nonarchimedean : ∀ (q r : ℤ_[p]), ∥q + r∥ ≤ max (∥q∥) (∥r∥)
| ⟨_, _⟩ ⟨_, _⟩ := padic_norm_e.nonarchimedean _ _

theorem add_eq_max_of_ne : ∀ {q r : ℤ_[p]}, ∥q∥ ≠ ∥r∥ → ∥q+r∥ = max (∥q∥) (∥r∥)
| ⟨_, _⟩ ⟨_, _⟩ := padic_norm_e.add_eq_max_of_ne

lemma norm_one : ∥(1 : ℤ_[p])∥ = 1 := normed_field.norm_one

lemma eq_of_norm_add_lt_right {z1 z2 : ℤ_[p]}
  (h : ∥z1 + z2∥ < ∥z2∥) : ∥z1∥ = ∥z2∥ :=
by_contradiction $ λ hne,
  not_lt_of_ge (by rw padic_norm_z.add_eq_max_of_ne hne; apply le_max_right) h

lemma eq_of_norm_add_lt_left {z1 z2 : ℤ_[p]}
  (h : ∥z1 + z2∥ < ∥z1∥) : ∥z1∥ = ∥z2∥ :=
by_contradiction $ λ hne,
  not_lt_of_ge (by rw padic_norm_z.add_eq_max_of_ne hne; apply le_max_left) h

@[simp] lemma padic_norm_e_of_padic_int (z : ℤ_[p]) : ∥(↑z : ℚ_[p])∥ = ∥z∥ :=
by simp [padic_norm_z]

lemma padic_norm_z_of_int (z : ℤ) : ∥(z : ℤ_[p])∥ = ∥(z : ℚ_[p])∥ :=
by simp [padic_norm_z]

@[simp] lemma padic_norm_z_eq_padic_norm_e {q : ℚ_[p]} (hq : ∥q∥ ≤ 1) :
  @norm ℤ_[p] _ ⟨q, hq⟩ = ∥q∥ := rfl

@[simp] lemma norm_p : ∥(p : ℤ_[p])∥ = p⁻¹ :=
show ∥((p : ℤ_[p]) : ℚ_[p])∥ = p⁻¹, by exact_mod_cast padic_norm_e.norm_p

@[simp] lemma norm_p_pow (n : ℕ) : ∥(p : ℤ_[p])^n∥ = p^(-n:ℤ) :=
show ∥((p^n : ℤ_[p]) : ℚ_[p])∥ = p^(-n:ℤ),
by { convert padic_norm_e.norm_p_pow n, simp, }

end padic_norm_z

namespace padic_int

variables {p : ℕ} [hp_prime : fact p.prime]
include hp_prime

lemma pow_p_dvd_int_iff (n : ℕ) (a : ℤ) : (p ^ n : ℤ_[p]) ∣ a ↔ ↑p ^ n ∣ a :=
begin
  split,
  { intro h,
    cases h with w hw,
    have := congr_arg has_norm.norm hw,
    simp only [padic_norm_z.padic_norm_z_of_int, padic_norm_z.norm_p_pow, padic_norm_z.mul,
               fpow_neg, fpow_coe_nat] at this,
    rw_mod_cast [padic_norm_e.norm_int_lt_pow_iff_dvd, this],
    simp only [fpow_neg, fpow_coe_nat, nat.cast_pow],
    convert mul_le_of_le_one_right _ _ using 1,
    { apply inv_nonneg.mpr, apply pow_nonneg, exact_mod_cast le_of_lt hp_prime.pos },
    { apply padic_norm_z.le_one } },
  { intro h,
    simpa only [ring_hom.map_pow] using (int.cast_ring_hom ℤ_[p]).map_dvd h, }
end

/-! ### Valuation on `ℤ_[p]` -/

/-- `padic_int.valuation` lifts the p-adic valuation on `ℚ` to `ℤ_[p]`.  -/
def valuation (x : ℤ_[p]) := padic.valuation (x : ℚ_[p])

lemma norm_eq_pow_val {x : ℤ_[p]} (hx : x ≠ 0) :
  ∥x∥ = p^(-x.valuation) :=
begin
  convert padic.norm_eq_pow_val _,
  contrapose! hx,
  exact subtype.val_injective hx
end

@[simp] lemma valuation_zero : valuation (0 : ℤ_[p]) = 0 :=
padic.valuation_zero

@[simp] lemma valuation_one : valuation (1 : ℤ_[p]) = 0 :=
padic.valuation_one

@[simp] lemma valuation_p : valuation (p : ℤ_[p]) = 1 :=
by simp [valuation, -cast_eq_of_rat_of_nat]

lemma valuation_nonneg (x : ℤ_[p]) : 0 ≤ x.valuation :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  have h : (1 : ℝ) < p := by exact_mod_cast hp_prime.one_lt,
  rw [← neg_nonpos, ← (fpow_strict_mono h).le_iff_le],
  show (p : ℝ) ^ -valuation x ≤ p ^ 0,
  rw [← norm_eq_pow_val hx],
  simpa using x.property,
end

@[simp] lemma valuation_p_pow_mul (n : ℕ) (c : ℤ_[p]) (hc : c ≠ 0) :
  (↑p ^ n * c).valuation = n + c.valuation :=
begin
  have : ∥↑p ^ n * c∥ = ∥(p ^ n : ℤ_[p])∥ * ∥c∥,
  { exact padic_norm_z.mul _ _ },
  have aux : ↑p ^ n * c ≠ 0,
  { contrapose! hc, rw mul_eq_zero at hc, cases hc,
    { refine (hp_prime.ne_zero _).elim,
      exact_mod_cast (pow_eq_zero hc) },
    { exact hc } },
  rwa [norm_eq_pow_val aux, padic_norm_z.norm_p_pow, norm_eq_pow_val hc,
      ← fpow_add, ← neg_add, fpow_inj, neg_inj] at this,
  { exact_mod_cast hp_prime.pos },
  { exact_mod_cast hp_prime.ne_one },
  { exact_mod_cast hp_prime.ne_zero },
end

/-! ### Units of `ℤ_[p]` -/

local attribute [reducible] padic_int

lemma mul_inv : ∀ {z : ℤ_[p]}, ∥z∥ = 1 → z * z.inv = 1
| ⟨k, _⟩ h :=
  begin
    have hk : k ≠ 0, from λ h', @zero_ne_one ℚ_[p] _ _ (by simpa [h'] using h),
    unfold padic_int.inv, split_ifs,
    { change (⟨k * (1/k), _⟩ : ℤ_[p]) = 1,
      simp [hk], refl },
    { apply subtype.ext_iff_val.2, simp [mul_inv_cancel hk] }
  end

lemma inv_mul {z : ℤ_[p]} (hz : ∥z∥ = 1) : z.inv * z = 1 :=
by rw [mul_comm, mul_inv hz]

lemma is_unit_iff {z : ℤ_[p]} : is_unit z ↔ ∥z∥ = 1 :=
⟨λ h, begin
  rcases is_unit_iff_dvd_one.1 h with ⟨w, eq⟩,
  refine le_antisymm (padic_norm_z.le_one _) _,
  have := mul_le_mul_of_nonneg_left (padic_norm_z.le_one w) (norm_nonneg z),
  rwa [mul_one, ← padic_norm_z.mul, ← eq, padic_norm_z.one] at this
end, λ h, ⟨⟨z, z.inv, mul_inv h, inv_mul h⟩, rfl⟩⟩

lemma norm_lt_one_add {z1 z2 : ℤ_[p]} (hz1 : ∥z1∥ < 1) (hz2 : ∥z2∥ < 1) : ∥z1 + z2∥ < 1 :=
lt_of_le_of_lt (padic_norm_z.nonarchimedean _ _) (max_lt hz1 hz2)

lemma norm_lt_one_mul {z1 z2 : ℤ_[p]} (hz2 : ∥z2∥ < 1) : ∥z1 * z2∥ < 1 :=
calc  ∥z1 * z2∥ = ∥z1∥ * ∥z2∥ : by simp
           ... < 1 : mul_lt_one_of_nonneg_of_lt_one_right (padic_norm_z.le_one _) (norm_nonneg _) hz2

@[simp] lemma mem_nonunits {z : ℤ_[p]} : z ∈ nonunits ℤ_[p] ↔ ∥z∥ < 1 :=
by rw lt_iff_le_and_ne; simp [padic_norm_z.le_one z, nonunits, is_unit_iff]

/-- A `p`-adic number `u` with `∥u∥ = 1` is a unit of `ℤ_[p]`. -/
def mk_units {u : ℚ_[p]} (h : ∥u∥ = 1) : units ℤ_[p] :=
let z : ℤ_[p] := ⟨u, le_of_eq h⟩ in ⟨z, z.inv, mul_inv h, inv_mul h⟩

@[simp]
lemma mk_units_eq {u : ℚ_[p]} (h : ∥u∥ = 1) : ((mk_units h : ℤ_[p]) : ℚ_[p]) = u :=
rfl

@[simp] lemma norm_units (u : units ℤ_[p]) : ∥(u : ℤ_[p])∥ = 1 :=
is_unit_iff.mp $ by simp

/-- `unit_coeff hx` is the unit `u` in the unique representation `x = u * p ^ n`.
See `unit_coeff_spec`. -/
def unit_coeff {x : ℤ_[p]} (hx : x ≠ 0) : units ℤ_[p] :=
let u : ℚ_[p] := x*p^(-x.valuation) in
have hu : ∥u∥ = 1,
by simp [hx, nat.fpow_ne_zero_of_pos (by exact_mod_cast hp_prime.pos) x.valuation,
         norm_eq_pow_val, fpow_neg, inv_mul_cancel, -cast_eq_of_rat_of_nat],
mk_units hu

@[simp] lemma unit_coeff_coe {x : ℤ_[p]} (hx : x ≠ 0) :
  (unit_coeff hx : ℚ_[p]) = x * p ^ (-x.valuation) := rfl

lemma unit_coeff_spec {x : ℤ_[p]} (hx : x ≠ 0) :
  x = (unit_coeff hx : ℤ_[p]) * p ^ int.nat_abs (valuation x) :=
begin
  apply subtype.coe_injective,
  push_cast,
  have repr : (x : ℚ_[p]) = (unit_coeff hx) * p ^ x.valuation,
  { rw [unit_coeff_coe, mul_assoc, ← fpow_add],
    { simp },
    { exact_mod_cast hp_prime.ne_zero } },
  convert repr using 2,
  rw [← fpow_coe_nat, int.nat_abs_of_nonneg (valuation_nonneg x)],
end

instance : local_ring ℤ_[p] :=
local_of_nonunits_ideal zero_ne_one $ λ x y, by simp; exact norm_lt_one_add

private def cau_seq_to_rat_cau_seq (f : cau_seq ℤ_[p] norm) :
  cau_seq ℚ_[p] (λ a, ∥a∥) :=
⟨ λ n, f n,
  λ _ hε, by simpa [norm, padic_norm_z] using f.cauchy hε ⟩

instance complete : cau_seq.is_complete ℤ_[p] norm :=
⟨ λ f,
  have hqn : ∥cau_seq.lim (cau_seq_to_rat_cau_seq f)∥ ≤ 1,
    from padic_norm_e_lim_le zero_lt_one (λ _, padic_norm_z.le_one _),
  ⟨ ⟨_, hqn⟩,
    λ ε, by simpa [norm, padic_norm_z] using cau_seq.equiv_lim (cau_seq_to_rat_cau_seq f) ε⟩⟩

/-- The coercion from ℤ[p] to ℚ[p] as a ring homomorphism. -/
def coe.ring_hom : ℤ_[p] →+* ℚ_[p]  :=
{ to_fun := (coe : ℤ_[p] → ℚ_[p]),
  map_zero' := rfl,
  map_one' := rfl,
  map_mul' := coe_mul,
  map_add' := coe_add }

lemma p_dvd_of_norm_lt_one {x : ℤ_[p]} (hx : ∥x∥ < 1) : ↑p ∣ x :=
begin
  by_cases hx0 : x = 0, { simp only [hx0, dvd_zero] },
  rw unit_coeff_spec hx0,
  by_cases H : x.valuation.nat_abs = 0,
  { rw [int.nat_abs_eq_zero] at H,
    rw [norm_eq_pow_val hx0, H, neg_zero, fpow_zero] at hx,
    exact (lt_irrefl _ hx).elim, },
  { apply dvd_mul_of_dvd_right,
    exact dvd_pow (dvd_refl _) H, }
end

lemma p_nonnunit : (p : ℤ_[p]) ∈ nonunits ℤ_[p] :=
have (p : ℝ)⁻¹ < 1, from inv_lt_one $ by exact_mod_cast hp_prime.one_lt,
by simp [this]

lemma maximal_ideal_eq_span_p : maximal_ideal ℤ_[p] = ideal.span {p} :=
begin
  apply le_antisymm,
  { intros x hx,
    rw ideal.mem_span_singleton,
    simp only [local_ring.mem_maximal_ideal, mem_nonunits] at hx,
    exact p_dvd_of_norm_lt_one hx, },
  { rw [ideal.span_le, set.singleton_subset_iff], exact p_nonnunit }
end

lemma prime_p : prime (p : ℤ_[p]) :=
begin
  rw [← ideal.span_singleton_prime, ← maximal_ideal_eq_span_p],
  { apply_instance },
  { exact_mod_cast hp_prime.ne_zero }
end

lemma irreducible_p : irreducible (p : ℤ_[p]) :=
irreducible_of_prime prime_p

instance : discrete_valuation_ring ℤ_[p] :=
discrete_valuation_ring.of_has_unit_mul_pow_irreducible_factorization
⟨p, irreducible_p, λ x hx, ⟨x.valuation.nat_abs, unit_coeff hx,
  by rw [mul_comm, ← unit_coeff_spec hx]⟩⟩

lemma ideal_eq_span_pow_p {s : ideal ℤ_[p]} (hs : s ≠ ⊥) :
  ∃ n : ℕ, s = ideal.span {p ^ n} :=
discrete_valuation_ring.ideal_eq_span_pow_irreducible hs irreducible_p

lemma norm_int_lt_one_iff_dvd (k : ℤ) : ∥(k : ℤ_[p])∥ < 1 ↔ ↑p ∣ k :=
suffices ∥(k : ℚ_[p])∥ < 1 ↔ ↑p ∣ k, by rwa padic_norm_z.padic_norm_z_of_int,
padic_norm_e.norm_int_lt_one_iff_dvd k

lemma norm_lt_one_iff_dvd (x : ℤ_[p]) : ∥x∥ < 1 ↔ ↑p ∣ x :=
begin
  rw [← mem_nonunits, ← local_ring.mem_maximal_ideal, maximal_ideal_eq_span_p,
      ideal.mem_span_singleton],
end

lemma is_unit_denom (r : ℚ) (h : ∥(r : ℚ_[p])∥ ≤ 1) : is_unit (r.denom : ℤ_[p]) :=
begin
  rw is_unit_iff,
  apply le_antisymm (r.denom : ℤ_[p]).2,
  rw [← not_lt, val_eq_coe, coe_coe],
  intro norm_denom_lt,
  have hr : ∥(r * r.denom : ℚ_[p])∥ = ∥(r.num : ℚ_[p])∥,
  { rw_mod_cast @rat.mul_denom_eq_num r, refl, },
  rw padic_norm_e.mul at hr,
  have key : ∥(r.num : ℚ_[p])∥ < 1,
  { calc _ = _ : hr.symm
    ... < 1 * 1 : _
    ... = 1 : mul_one 1,
    apply mul_lt_mul' h norm_denom_lt (norm_nonneg _) zero_lt_one, },
  have : ↑p ∣ r.num ∧ (p : ℤ) ∣ r.denom,
  { simp only [← norm_int_lt_one_iff_dvd, ← padic_norm_z.padic_norm_e_of_padic_int],
    norm_cast, exact ⟨key, norm_denom_lt⟩ },
  apply hp_prime.not_dvd_one,
  rwa [← r.cop.gcd_eq_one, nat.dvd_gcd_iff, ← int.coe_nat_dvd_left, ← int.coe_nat_dvd],
end

lemma norm_sub_mod_part_aux (r : ℚ) (h : ∥(r : ℚ_[p])∥ ≤ 1) :
  ↑p ∣ r.num - r.num * r.denom.gcd_a p % p * ↑(r.denom) :=
begin
  rw ← zmod.int_coe_zmod_eq_zero_iff_dvd,
  simp only [int.cast_coe_nat, zmod.cast_mod_nat p, int.cast_mul, int.cast_sub],
  have := congr_arg (coe : ℤ → zmod p) (gcd_eq_gcd_ab r.denom p),
  simp only [int.cast_coe_nat, add_zero, int.cast_add, zmod.cast_self, int.cast_mul, zero_mul] at this,
  push_cast,
  rw [mul_right_comm, mul_assoc, ←this],
  suffices rdcp : r.denom.coprime p,
  { rw rdcp.gcd_eq_one, simp only [mul_one, cast_one, sub_self], },
  apply coprime.symm,
  apply (coprime_or_dvd_of_prime ‹_› _).resolve_right,
  rw [← int.coe_nat_dvd, ← norm_int_lt_one_iff_dvd, not_lt],
  apply ge_of_eq,
  rw ← is_unit_iff,
  exact is_unit_denom r h,
end

section
variables (r : ℚ)
variable (p)

omit hp_prime

/--
`mod_part r p` is an integer that satisfies
`∥(r - mod_part p r : ℚ_[p])∥ < 1` when `∥(r : ℚ_[p])∥ ≤ 1`,
see `padic_int.norm_sub_mod_part`.
It is the unique non-negative integer that is `< p` with this property.

(Note that this definition assumes `r : ℚ`.
See `padic_int.zmod_repr` for a version that takes values in `ℕ`
and works for arbitrary `x : ℤ_[p]`.) -/
def mod_part : ℤ :=
(r.num * gcd_a r.denom p) % p

include hp_prime

lemma mod_part_lt_p : mod_part p r < p :=
begin
  convert int.mod_lt _ _,
  { simp },
  { exact_mod_cast hp_prime.ne_zero }
end

lemma mod_part_nonneg : 0 ≤ mod_part p r :=
int.mod_nonneg _ $ by exact_mod_cast hp_prime.ne_zero

variable {p}

lemma norm_sub_mod_part (h : ∥(r : ℚ_[p])∥ ≤ 1) : ∥(⟨r,h⟩ - mod_part p r : ℤ_[p])∥ < 1 :=
begin
  let n := mod_part p r,  by_cases aux : (⟨r,h⟩ - n : ℤ_[p]) = 0,
  { rw [aux, norm_zero], exact zero_lt_one, },
  suffices : ↑p ∣ (⟨r,h⟩ - n : ℤ_[p]),
  { rcases this with ⟨x, hx⟩,
    calc ∥(⟨r,h⟩ - n : ℤ_[p])∥
        = ∥(p : ℤ_[p])∥ * ∥x∥ : by rw [hx, padic_norm_z.mul]
    ... ≤ ∥(p : ℤ_[p])∥ * 1   : mul_le_mul (le_refl _) x.2 (norm_nonneg _) (norm_nonneg _)
    ... < 1 : _,
    { rw [mul_one, padic_norm_z.norm_p],
      apply inv_lt_one,
      exact_mod_cast hp_prime.one_lt }, },
  rw ← (is_unit_denom r h).dvd_mul_right,
  suffices : ↑p ∣ r.num - n * r.denom,
  { convert (int.cast_ring_hom ℤ_[p]).map_dvd this,
    simp only [sub_mul, int.cast_coe_nat, ring_hom.eq_int_cast, int.cast_mul,
      sub_left_inj, int.cast_sub],
    apply subtype.coe_injective,
    simp only [coe_mul, subtype.coe_mk, coe_coe],
    rw_mod_cast @rat.mul_denom_eq_num r, refl },
  dsimp [n, mod_part],
  apply norm_sub_mod_part_aux r h,
end

end

section

lemma zmod_congr_of_sub_mem_span_aux (n : ℕ) (x : ℤ_[p]) (a b : ℤ)
  (ha : x - a ∈ (ideal.span {p ^ n} : ideal ℤ_[p]))
  (hb : x - b ∈ (ideal.span {p ^ n} : ideal ℤ_[p])) :
  (a : zmod (p ^ n)) = b :=
begin
  rw [ideal.mem_span_singleton] at ha hb,
  rw [← sub_eq_zero, ← int.cast_sub,
      zmod.int_coe_zmod_eq_zero_iff_dvd, int.coe_nat_pow],
  rw [← dvd_neg, neg_sub] at ha,
  have := dvd_add ha hb,
  rwa [sub_eq_add_neg, sub_eq_add_neg, add_assoc, neg_add_cancel_left,
      ← sub_eq_add_neg, ← int.cast_sub, pow_p_dvd_int_iff] at this,
end

lemma zmod_congr_of_sub_mem_span (n : ℕ) (x : ℤ_[p]) (a b : ℕ)
  (ha : x - a ∈ (ideal.span {p ^ n} : ideal ℤ_[p]))
  (hb : x - b ∈ (ideal.span {p ^ n} : ideal ℤ_[p])) :
  (a : zmod (p ^ n)) = b :=
zmod_congr_of_sub_mem_span_aux n x a b ha hb

lemma zmod_congr_of_sub_mem_max_ideal (x : ℤ_[p]) (m n : ℕ)
  (hm : x - m ∈ maximal_ideal ℤ_[p]) (hn : x - n ∈ maximal_ideal ℤ_[p]) :
  (m : zmod p) = n :=
begin
  rw maximal_ideal_eq_span_p at hm hn,
  have := zmod_congr_of_sub_mem_span_aux 1 x m n,
  simp only [_root_.pow_one] at this,
  specialize this hm hn,
  apply_fun zmod.cast_hom (show p ∣ p ^ 1, by rw nat.pow_one) (zmod p) at this,
  simpa only [ring_hom.map_int_cast],
end

variable (x : ℤ_[p])

lemma exists_mem_range : ∃ n : ℕ, n < p ∧ (x - n ∈ maximal_ideal ℤ_[p]) :=
begin
  simp only [maximal_ideal_eq_span_p, ideal.mem_span_singleton, ← norm_lt_one_iff_dvd],
  obtain ⟨r, hr⟩ := rat_dense (x : ℚ_[p]) zero_lt_one,
  have H : ∥(r : ℚ_[p])∥ ≤ 1,
  { rw norm_sub_rev at hr,
    rw show (r : ℚ_[p]) = (r - x) + x, by ring,
    apply le_trans (padic_norm_e.nonarchimedean _ _),
    apply max_le (le_of_lt hr) x.2 },
  have hnp := mod_part_lt_p p r,
  have hn := norm_sub_mod_part r H,
  lift mod_part p r to ℕ using mod_part_nonneg p r with n,
  use [n],
  split, {exact_mod_cast hnp},
  simp only [padic_norm_z, coe_sub, subtype.coe_mk, coe_coe] at hn ⊢,
  rw show (x - n : ℚ_[p]) = (x - r) + (r - n), by ring,
  apply lt_of_le_of_lt (padic_norm_e.nonarchimedean _ _),
  apply max_lt hr,
  simpa using hn
end

/--
`zmod_repr x` is the unique natural number smaller than `p`
satisfying `∥(x - zmod_repr x : ℤ_[p])∥ < 1`.
-/
def zmod_repr : ℕ :=
classical.some (exists_mem_range x)

lemma zmod_repr_spec : zmod_repr x < p ∧ (x - zmod_repr x ∈ maximal_ideal ℤ_[p]) :=
classical.some_spec (exists_mem_range x)

lemma zmod_repr_lt_p : zmod_repr x < p := (zmod_repr_spec _).1

lemma sub_zmod_repr_mem : (x - zmod_repr x ∈ maximal_ideal ℤ_[p]) := (zmod_repr_spec _).2

end

/--
`to_zmod_hom` is an auxiliary constructor for creating ring homs from `ℤ_[p]` to `zmod v`.
-/
def to_zmod_hom (v : ℕ) (f : ℤ_[p] → ℕ) (f_spec : ∀ x, x - f x ∈ (ideal.span {v} : ideal ℤ_[p]))
  (f_congr : ∀ (x : ℤ_[p]) (a b : ℕ),
     x - a ∈ (ideal.span {v} : ideal ℤ_[p]) → x - b ∈ (ideal.span {v} : ideal ℤ_[p]) →
       (a : zmod v) = b) :
  ℤ_[p] →+* zmod v :=
{ to_fun := λ x, f x,
  map_zero' :=
  begin
    rw [f_congr (0 : ℤ_[p]) _ 0, cast_zero],
    { exact f_spec _ },
    { simp only [sub_zero, cast_zero, submodule.zero_mem], }
  end,
  map_one' :=
  begin
    rw [f_congr (1 : ℤ_[p]) _ 1, cast_one],
    { exact f_spec _ },
    { simp only [sub_self, cast_one, submodule.zero_mem], }
  end,
  map_add' :=
  begin
    intros x y,
    rw [f_congr (x + y) _ (f x + f y), cast_add],
    { exact f_spec _ },
    { convert ideal.add_mem _ (f_spec x) (f_spec y),
      rw cast_add,
      ring, }
  end,
  map_mul' :=
  begin
    intros x y,
    rw [f_congr (x * y) _ (f x * f y), cast_mul],
    { exact f_spec _ },
    { let I : ideal ℤ_[p] := ideal.span {v},
      have A : x * (y - f y) ∈ I := I.mul_mem_left (f_spec _),
      have B : (x - f x) * (f y) ∈ I := I.mul_mem_right (f_spec _),
      convert I.add_mem A B,
      rw cast_mul,
      ring, }
  end, }

/--
`to_zmod` is a ring hom from `ℤ_[p]` to `zmod p`,
with the equality `to_zmod x = (zmod_repr x : zmod p)`.
-/
def to_zmod : ℤ_[p] →+* zmod p :=
to_zmod_hom p zmod_repr
  (by { rw ←maximal_ideal_eq_span_p, exact sub_zmod_repr_mem })
  (by { rw ←maximal_ideal_eq_span_p, exact zmod_congr_of_sub_mem_max_ideal } )

/--
`z - (to_zmod z : ℤ_[p])` is contained in the maximal ideal of `ℤ_[p]`, for every `z : ℤ_[p]`.

The coercion from `zmod p` to `ℤ_[p]` is `zmod.has_coe_t`,
which coerces `zmod p` into artibrary rings.
This is unfortunate, but a consequence of the fact that we allow `zmod p`
to coerce to rings of arbitrary characteristic, instead of only rings of characteristic `p`.
This coercion is only a ring homomorphism if it coerces into a ring whose characteristic divides `p`.
While this is not the case here we can still make use of the coercion.
-/
lemma to_zmod_spec (z : ℤ_[p]) : z - (to_zmod z : ℤ_[p]) ∈ maximal_ideal ℤ_[p] :=
begin
  convert sub_zmod_repr_mem z using 2,
  dsimp [to_zmod, to_zmod_hom],
  unfreezingI { rcases (exists_eq_add_of_lt (hp_prime.pos)) with ⟨p', rfl⟩ },
  change ↑(zmod.val _) = _,
  simp [zmod.val_cast_nat],
  rw mod_eq_of_lt,
  simpa only [zero_add] using zmod_repr_lt_p z,
end

lemma ker_to_zmod : (to_zmod : ℤ_[p] →+* zmod p).ker = maximal_ideal ℤ_[p] :=
begin
  ext x,
  rw ring_hom.mem_ker,
  split,
  { intro h,
    simpa only [h, zmod.cast_zero, sub_zero] using to_zmod_spec x, },
  { intro h,
    rw ← sub_zero x at h,
    dsimp [to_zmod, to_zmod_hom],
    convert zmod_congr_of_sub_mem_max_ideal x _ 0 _ h,
    apply sub_zmod_repr_mem, }
end

/-- `appr n x` gives a value `v : ℕ` such that `x` and `↑v : ℤ_p` are congruent mod `p^n`.
See `appr_spec`. -/
noncomputable def appr : ℤ_[p] → ℕ → ℕ
| x 0     := 0
| x (n+1) :=
let y := x - appr x n in
if hy : y = 0 then
  appr x n
else
  let u := unit_coeff hy in
  appr x n + p ^ n * (to_zmod ((u : ℤ_[p]) * (p ^ (y.valuation - n).nat_abs))).val

lemma appr_lt (x : ℤ_[p]) (n : ℕ) : x.appr n < p ^ n :=
begin
  induction n with n ih generalizing x,
  { simp only [appr, succ_pos', nat.pow_zero], },
  simp only [appr, ring_hom.map_nat_cast, zmod.cast_self, ring_hom.map_pow, int.nat_abs, ring_hom.map_mul],
  have hp : p ^ n < p ^ (n + 1),
  { simp [← nat.pow_eq_pow],
    apply pow_lt_pow hp_prime.one_lt (lt_add_one n) },
  split_ifs with h,
  { apply lt_trans (ih _) hp, },
  { calc _ < p ^ n + p ^ n * (p - 1) : _
    ... = p ^ (n + 1) : _,
    { apply add_lt_add_of_lt_of_le (ih _),
      apply nat.mul_le_mul_left,
      apply le_pred_of_lt,
      apply zmod.val_lt },
    { rw [nat.mul_sub_left_distrib, mul_one, ← nat.pow_succ],
      apply nat.add_sub_cancel' (le_of_lt hp) } }
end

lemma appr_spec (n : ℕ) : ∀ (x : ℤ_[p]), x - appr x n ∈ (ideal.span {p^n} : ideal ℤ_[p]) :=
begin
  simp only [ideal.mem_span_singleton],
  induction n with n ih,
  { simp only [is_unit_one, is_unit.dvd, pow_zero, forall_true_iff], },
  { intro x,
    dsimp only [appr],
    split_ifs with h,
    { rw h, apply dvd_zero },
    { push_cast, rw sub_add_eq_sub_sub,
      obtain ⟨c, hc⟩ := ih x,
      simp only [ring_hom.map_nat_cast, zmod.cast_self, ring_hom.map_pow, ring_hom.map_mul, zmod.nat_cast_val],
      have hc' : c ≠ 0,
      { rintro rfl, simp only [mul_zero] at hc, contradiction },
      conv_rhs { congr, simp only [hc], },
      rw show (x - ↑(appr x n)).valuation = (↑p ^ n * c).valuation,
      { rw hc },
      rw [valuation_p_pow_mul _ _ hc', add_sub_cancel', pow_succ', ← mul_sub],
      apply mul_dvd_mul_left,
      by_cases hc0 : c.valuation.nat_abs = 0,
      { simp only [hc0, mul_one, pow_zero],
        rw [mul_comm, unit_coeff_spec h] at hc,
        have hcu : is_unit c,
        { rw int.nat_abs_eq_zero at hc0,
          rw [is_unit_iff, norm_eq_pow_val hc', hc0, neg_zero, fpow_zero], },
        rcases hcu with ⟨c, rfl⟩,
        obtain rfl := discrete_valuation_ring.unit_mul_pow_congr_unit _ _ _ _ _ hc,
        swap, { exact irreducible_p },
        rw [← ideal.mem_span_singleton, ← maximal_ideal_eq_span_p],
        apply to_zmod_spec, },
      { rw [_root_.zero_pow (nat.pos_of_ne_zero hc0)],
        simp only [sub_zero, zmod.cast_zero, mul_zero],
        rw unit_coeff_spec hc',
        apply dvd_mul_of_dvd_right,
        apply dvd_pow (dvd_refl _),
        exact hc0, } } }
end

/-- A ring hom from `ℤ_[p]` to `zmod (p^n)`, with underlying function `padic_int.appr n`. -/
def to_zmod_pow (n : ℕ) : ℤ_[p] →+* zmod (p ^ n) :=
to_zmod_hom (p^n) (λ x, appr x n)
  (by { intros, convert appr_spec n _ using 1, simp })
  (by { intros x a b ha hb,
        apply zmod_congr_of_sub_mem_span n x a b; [simpa using ha, simpa using hb] })

lemma ker_to_zmod_pow (n : ℕ) : (to_zmod_pow n : ℤ_[p] →+* zmod (p ^ n)).ker = ideal.span {p ^ n} :=
begin
  ext x,
  rw ring_hom.mem_ker,
  split,
  { intro h,
    suffices : x.appr n = 0,
    { convert appr_spec n x, simp only [this, sub_zero, cast_zero], },
    dsimp [to_zmod_pow, to_zmod_hom] at h,
    rw zmod.nat_coe_zmod_eq_zero_iff_dvd at h,
    apply eq_zero_of_dvd_of_lt h (appr_lt _ _),  },
  { intro h,
    rw ← sub_zero x at h,
    dsimp [to_zmod_pow, to_zmod_hom],
    rw [zmod_congr_of_sub_mem_span n x _ 0 _ h, cast_zero],
    apply appr_spec, }
end

end padic_int

namespace padic_norm_z
variables {p : ℕ} [fact p.prime]

lemma padic_val_of_cong_pow_p {z1 z2 : ℤ} {n : ℕ} (hz : z1 ≡ z2 [ZMOD ↑(p^n)]) :
      ∥(z1 - z2 : ℚ_[p])∥ ≤ ↑(↑p ^ (-n : ℤ) : ℚ) :=
have hdvd : ↑(p^n) ∣ z2 - z1, from int.modeq.modeq_iff_dvd.1 hz,
have (z2 - z1 : ℚ_[p]) = ↑(↑(z2 - z1) : ℚ), by norm_cast,
begin
  rw [norm_sub_rev, this, padic_norm_e.eq_padic_norm],
  exact_mod_cast padic_norm.dvd_iff_norm_le.mp hdvd
end

end padic_norm_z
