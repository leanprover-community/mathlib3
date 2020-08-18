/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro
-/
import data.int.modeq
import data.zmod.basic
import linear_algebra.adic_completion
import data.padics.padic_numbers
import ring_theory.discrete_valuation_ring

/-!
# p-adic integers

This file defines the p-adic integers ℤ_p as the subtype of ℚ_p with norm ≤ 1. We show that ℤ_p is a
complete nonarchimedean normed local ring.

## Important definitions

* `padic_int` : the type of p-adic numbers

## Notation

We introduce the notation ℤ_[p] for the p-adic integers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking (prime p) as a type class argument.

Coercions into ℤ_p are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouêva, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, p-adic integer
-/

open nat padic metric
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

@[simp] lemma padic_norm_z_eq_padic_norm_e {q : ℚ_[p]} (hq : ∥q∥ ≤ 1) :
  @norm ℤ_[p] _ ⟨q, hq⟩ = ∥q∥ := rfl

@[simp] lemma norm_p : ∥(p : ℤ_[p])∥ = p⁻¹ :=
show ∥((p : ℤ_[p]) : ℚ_[p])∥ = p⁻¹, by exact_mod_cast padic_norm_e.norm_p

@[simp] lemma norm_p_pow (n : ℕ) : ∥(p : ℤ_[p])^n∥ = p^(-n:ℤ) :=
show ∥((p^n : ℤ_[p]) : ℚ_[p])∥ = p^(-n:ℤ),
by { convert padic_norm_e.norm_p_pow n, simp, }

end padic_norm_z

private lemma mul_lt_one {α} [decidable_linear_ordered_comm_ring α] {a b : α} (hbz : 0 < b)
  (ha : a < 1) (hb : b < 1) : a * b < 1 :=
suffices a*b < 1*1, by simpa,
mul_lt_mul ha (le_of_lt hb) hbz zero_le_one

private lemma mul_lt_one_of_le_of_lt {α} [decidable_linear_ordered_comm_ring α] {a b : α} (ha : a ≤ 1)
  (hbz : 0 ≤ b) (hb : b < 1) : a * b < 1 :=
if hb' : b = 0 then by simpa [hb'] using zero_lt_one
else if ha' : a = 1 then by simpa [ha']
else mul_lt_one (lt_of_le_of_ne hbz (ne.symm hb')) (lt_of_le_of_ne ha ha') hb

namespace padic_int

variables {p : ℕ} [fact p.prime]

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
  have h : (1 : ℝ) < p := by exact_mod_cast nat.prime.one_lt ‹_›,
  rw [← neg_nonpos, ← (fpow_strict_mono h).le_iff_le],
  show (p : ℝ) ^ -valuation x ≤ p ^ 0,
  rw [← norm_eq_pow_val hx],
  simpa using x.property,
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
           ... < 1 : mul_lt_one_of_le_of_lt (padic_norm_z.le_one _) (norm_nonneg _) hz2

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
by simp [hx, nat.fpow_ne_zero_of_pos (by exact_mod_cast nat.prime.pos ‹_›) x.valuation,
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
    { exact_mod_cast nat.prime.ne_zero ‹_› } },
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
have (p : ℝ)⁻¹ < 1, from inv_lt_one $ by exact_mod_cast nat.prime.one_lt ‹_›,
by simp [this]

lemma maximal_ideal_eq_span_p : local_ring.maximal_ideal ℤ_[p] = ideal.span {p} :=
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
  { exact_mod_cast nat.prime.ne_zero ‹_› }
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

@[simp, norm_cast] lemma coe_int_eq (z1 z2 : ℤ) : (z1 : ℤ_[p]) = z2 ↔ z1 = z2 :=
suffices (z1 : ℚ_[p]) = z2 ↔ z1 = z2, from iff.trans (by norm_cast) this,
by norm_cast

lemma int.to_nat_of_neg : ∀ {z : ℤ}, ¬ 0 ≤ z → z.to_nat = 0
| (-[1+n]) _ := rfl
| (int.of_nat n) h := (h $ int.of_nat_nonneg n).elim

lemma give_better_name (k : ℤ) : ∥(k : ℤ_[p])∥ < 1 ↔ ↑p ∣ k :=
begin
  split,
  { intro h,
    contrapose! h,
    apply le_of_eq,
    rw eq_comm,
    calc ∥(k : ℤ_[p])∥ = ∥((k : ℚ) : ℚ_[p])∥ : by { rw [padic_norm_z], norm_cast }
    ... = padic_norm p k : padic_norm_e.eq_padic_norm _
    ... = 1 : _,
    rw padic_norm,
    split_ifs with H,
    { exfalso, apply h, norm_cast at H, rw H, simp only [dvd_zero] },
    norm_cast at H,
    norm_cast,
    convert fpow_zero _,
    simp only [neg_eq_zero],
    rw padic_val_rat.padic_val_rat_of_int _ (nat.prime.ne_one ‹_›) H,
    norm_cast,
    rw [← enat.coe_inj, enat.coe_get, enat.coe_zero],
    apply multiplicity.multiplicity_eq_zero_of_not_dvd h, },
  { rintro ⟨x, rfl⟩,
    push_cast,
    rw padic_norm_z.mul,
    calc _ ≤ ∥(p : ℤ_[p])∥ * 1 : mul_le_mul (le_refl _) (x : ℤ_[p]).2 (norm_nonneg _) (norm_nonneg _)
    ... < 1 : _,
    { rw [mul_one, padic_norm_z.norm_p],
      apply inv_lt_one,
      exact_mod_cast nat.prime.one_lt ‹_› }, },
end

lemma is_unit_denom (r : ℚ) (h : ∥(r : ℚ_[p])∥ ≤ 1) : is_unit (r.denom : ℤ_[p]) :=
begin
  rw is_unit_iff,
  apply le_antisymm (r.denom : ℤ_[p]).2,
  rw [← not_lt, val_eq_coe, coe_coe],
  intro oops,
  have help : ∥(r * r.denom : ℚ_[p])∥ = ∥(r.num : ℚ_[p])∥,
  { rw_mod_cast @rat.mul_denom_eq_num r, refl, },
  rw padic_norm_e.mul at help,
  have key : ∥(r.num : ℚ_[p])∥ < 1,
  { calc _ = _ : help.symm
    ... < 1 * 1 : _
    ... = 1 : mul_one 1,
    apply mul_lt_mul' h oops (norm_nonneg _) zero_lt_one, },
  have oolala : ↑p ∣ r.num ∧ (p : ℤ) ∣ r.denom,
  { simp only [← give_better_name, ← padic_norm_z.padic_norm_e_of_padic_int],
    norm_cast, exact ⟨key, oops⟩ },
  suffices boom : p ∣ 1,
  { exact nat.prime.not_dvd_one ‹_› boom },
  rwa [← r.cop.gcd_eq_one, nat.dvd_gcd_iff, ← int.coe_nat_dvd_left, ← int.coe_nat_dvd],
end

@[simp] lemma zmod.coe_to_nat (p : ℕ) :
  ∀ (z : ℤ) (h : 0 ≤ z), (z.to_nat : zmod p) = z
| (n : ℕ) h := by simp only [int.cast_coe_nat, int.to_nat_coe_nat]
| -[1+n]  h := false.elim h

@[simp] lemma zmod.coe_int_mod (p : ℕ) (z : ℤ) :
  ((z % p : ℤ) : zmod p) = z :=
begin
  rw int.mod_def,
  simp only [int.cast_coe_nat, zmod.cast_self, int.cast_mul, zero_mul, sub_zero, int.cast_sub],
end

@[simp] lemma zmod.coe_nat_mod (p : ℕ) (h : p ≠ 0) (z : ℤ) : (z.nat_mod p : zmod p) = z :=
begin
  show ↑(int.to_nat _) = _,
  rw [zmod.coe_to_nat, zmod.coe_int_mod],
  { apply int.mod_nonneg, exact_mod_cast h }
end

lemma hopla_hop (r : ℚ) (h : ∥(r : ℚ_[p])∥ ≤ 1) :
  let n : ℤ := r.num * r.denom.gcd_a p
  in ¬(⟨r, h⟩ - (n.nat_mod p) : ℤ_[p]) = 0 →
     ↑p ∣ r.num - (n.nat_mod p) * ↑(r.denom) :=
begin
  intros n aux,
  rw ← zmod.int_coe_zmod_eq_zero_iff_dvd,
  simp only [int.cast_coe_nat, zmod.coe_nat_mod p (nat.prime.ne_zero ‹_›), int.cast_mul, int.cast_sub],
  have := congr_arg (coe : ℤ → zmod p) (gcd_eq_gcd_ab r.denom p),
  simp only [int.cast_coe_nat, add_zero, int.cast_add, zmod.cast_self, int.cast_mul, zero_mul] at this,
  rw [mul_right_comm, mul_assoc, ← this],
  suffices help : r.denom.coprime p,
  { rw help.gcd_eq_one, simp only [mul_one, cast_one, sub_self], },
  apply coprime.symm,
  apply (coprime_or_dvd_of_prime ‹_› _).resolve_right,
  rw [← int.coe_nat_dvd, ← give_better_name, not_lt],
  apply ge_of_eq,
  rw ← is_unit_iff,
  exact is_unit_denom r h,
end

lemma exists_mem_range_of_norm_rat_le_one (r : ℚ) (h : ∥(r : ℚ_[p])∥ ≤ 1) :
  ∃ n ∈ finset.range p, ∥(⟨r,h⟩ - n : ℤ_[p])∥ < 1 :=
begin
  let n := r.num * gcd_a r.denom p,
  use (int.nat_mod n p),
  split,
  { rw finset.mem_range,
    unfold int.nat_mod,
    by_cases h : 0 ≤ n % p,
    { zify, rw int.to_nat_of_nonneg h, convert int.mod_lt _ _,
      simp,
      exact_mod_cast nat.prime.ne_zero ‹_› },
    { zify, rw int.to_nat_of_neg h, exact_mod_cast nat.prime.pos ‹_› } },
  { by_cases aux : (⟨r,h⟩ - (n.nat_mod p) : ℤ_[p]) = 0,
    { rw [aux, norm_zero], exact zero_lt_one, },
    suffices : ↑p ∣ (⟨r,h⟩ - (n.nat_mod p) : ℤ_[p]),
    { rcases this with ⟨x, hx⟩,
      calc ∥(⟨r,h⟩ - (n.nat_mod p) : ℤ_[p])∥
          = ∥(p : ℤ_[p])∥ * ∥x∥ : by rw [hx, padic_norm_z.mul]
      ... ≤ ∥(p : ℤ_[p])∥ * 1   : mul_le_mul (le_refl _) x.2 (norm_nonneg _) (norm_nonneg _)
      ... < 1 : _,
      { rw [mul_one, padic_norm_z.norm_p],
        apply inv_lt_one,
        exact_mod_cast nat.prime.one_lt ‹_› }, },
    rw ← (is_unit_denom r h).dvd_mul_right,
    suffices : ↑p ∣ r.num - (n.nat_mod p) * r.denom,
    { convert (int.cast_ring_hom ℤ_[p]).map_dvd this,
      simp only [sub_mul, int.cast_coe_nat, ring_hom.eq_int_cast, int.cast_mul,
        sub_left_inj, int.cast_sub],
      apply subtype.coe_injective,
      simp only [coe_mul, subtype.coe_mk, coe_coe],
      rw_mod_cast @rat.mul_denom_eq_num r, refl },
    apply hopla_hop r h aux, }
end

lemma exists_mem_range (x : ℤ_[p]) :
  ∃ n ∈ finset.range p, ∥(x - n : ℤ_[p])∥ < 1 :=
begin
  obtain ⟨r, hr⟩ := rat_dense (x : ℚ_[p]) zero_lt_one,
  have H : ∥(r : ℚ_[p])∥ ≤ 1,
  { rw norm_sub_rev at hr,
    rw show (r : ℚ_[p]) = (r - x) + x, by ring,
    apply le_trans (padic_norm_e.nonarchimedean _ _),
    apply max_le (le_of_lt hr) x.2, },
  obtain ⟨n, hn, yes⟩ := exists_mem_range_of_norm_rat_le_one r H,
  use [n, hn],
  simp only [padic_norm_z, coe_sub, subtype.coe_mk, coe_coe] at yes ⊢,
  rw show (x - n : ℚ_[p]) = (x - r) + (r - n), by ring,
  apply lt_of_le_of_lt (padic_norm_e.nonarchimedean _ _),
  apply max_lt hr yes,
end

lemma exists_mem_range_congr (x : ℤ_[p]) (m n : ℕ) (hmp : m < p) (hnp : n < p)
  (hm : ∥x - m∥ < 1) (hn : ∥x - n∥ < 1) :
  m = n :=
begin
  rw norm_sub_rev at hm,
  have : ∥((m - n : ℤ) : ℤ_[p])∥ < 1,
  { rw show ((m - n : ℤ) : ℤ_[p]) = (↑m - x) + (x - n), { push_cast, ring },
    apply lt_of_le_of_lt (padic_norm_z.nonarchimedean _ _),
    apply max_lt hm hn },
  rw [give_better_name, ← int.modeq.modeq_iff_dvd, int.modeq, eq_comm] at this,
  rw [int.mod_eq_of_lt, int.mod_eq_of_lt] at this;
  { simpa },
end

lemma exists_mem_range_congr' (x : ℤ_[p]) (m n : ℕ)
  (hm : ∥x - m∥ < 1) (hn : ∥x - n∥ < 1) :
  (m : zmod p) = n :=
begin
  rw norm_sub_rev at hm,
  have : ∥((m - n : ℤ) : ℤ_[p])∥ < 1,
  { rw show ((m - n : ℤ) : ℤ_[p]) = (↑m - x) + (x - n), { push_cast, ring },
    apply lt_of_le_of_lt (padic_norm_z.nonarchimedean _ _),
    apply max_lt hm hn },
  rw [give_better_name, ← zmod.int_coe_zmod_eq_zero_iff_dvd] at this,
  simpa [sub_eq_zero],
end

def to_zmod : ℤ_[p] →+* zmod p :=
{ to_fun := λ x, ((classical.some (exists_mem_range x) : ℕ) : zmod p),
  map_zero' :=
  begin
    obtain ⟨hcp, hc⟩ := classical.some_spec (exists_mem_range (0 : ℤ_[p])),
    rw finset.mem_range at hcp,
    rw exists_mem_range_congr _ _ 0 hcp _ hc,
    { simp only [cast_zero], },
    { simp only [norm_zero, sub_zero, cast_zero], exact zero_lt_one },
    { exact nat.prime.pos ‹_› },
  end,
  map_one' :=
  begin
    obtain ⟨hcp, hc⟩ := classical.some_spec (exists_mem_range (1 : ℤ_[p])),
    rw finset.mem_range at hcp,
    rw exists_mem_range_congr _ _ 1 hcp _ hc,
    { simp only [cast_one], },
    { simp only [norm_zero, sub_self, cast_one], exact zero_lt_one },
    { exact nat.prime.one_lt ‹_› },
  end,
  map_add' :=
  begin
    intros x y,
    obtain ⟨hxp, hx⟩ := classical.some_spec (exists_mem_range x),
    obtain ⟨hyp, hy⟩ := classical.some_spec (exists_mem_range y),
    obtain ⟨hxyp, hxy⟩ := classical.some_spec (exists_mem_range (x + y)),
    rw ← nat.cast_add,
    rw exists_mem_range_congr' (x + y) _ _ hxy,
    have := lt_of_le_of_lt (padic_norm_z.nonarchimedean _ _) (max_lt hx hy),
    convert this using 2,
    abel,
    congr,
    simp,
    rw add_comm,
  end,
  map_mul' :=
  begin
    intros x y,
    obtain ⟨hxp, hx⟩ := classical.some_spec (exists_mem_range x),
    obtain ⟨hyp, hy⟩ := classical.some_spec (exists_mem_range y),
    obtain ⟨hxyp, hxy⟩ := classical.some_spec (exists_mem_range (x * y)),
    rw ← nat.cast_mul,
    rw exists_mem_range_congr' (x * y) _ _ hxy,
    let X : ℕ := classical.some (exists_mem_range x),
    let Y : ℕ := classical.some (exists_mem_range y),
    show ∥x * y - ↑(X * Y)∥ < 1,
    change ∥x - X∥ < 1 at hx,
    change ∥y - Y∥ < 1 at hy,
    simp only [padic_norm_z, coe_sub, coe_mul, cast_mul, finset.mem_range, coe_coe] at *,
    have key1 : ∥(x : ℚ_[p])∥ * ∥(y - Y : ℚ_[p])∥ < 1,
    { rw mul_comm,
      apply lt_of_le_of_lt _ hy,
      calc _ ≤ _ : mul_le_mul (le_refl _) x.2 (norm_nonneg _) (norm_nonneg _)
      ... = ∥(y - Y : ℚ_[p])∥ : mul_one _, },
    have key2 : ∥(x - X : ℚ_[p])∥ * ∥(Y : ℚ_[p])∥ < 1,
    { apply lt_of_le_of_lt _ hx,
      calc _ ≤ _ : mul_le_mul (le_refl _) _ (norm_nonneg _) (norm_nonneg _)
      ... = ∥(x - X : ℚ_[p])∥ : mul_one _,
      convert (Y : ℤ_[p]).2, simp only [val_eq_coe, coe_coe], },
    rw ← padic_norm_e.mul at key1 key2,
    have := lt_of_le_of_lt (padic_norm_e.nonarchimedean _ _) (max_lt key1 key2),
    convert this using 2,
    ring,
  end,
}

-- lemma z_dense (x : ℤ_[p]) : ∀ (ε : ℝ), 0 < ε → (∃ (k : ℤ), dist x ↑k < ε) :=
-- begin
--   intros ε hε,
--   obtain ⟨r, hr⟩ := rat_dense (x : ℚ_[p]) hε,
--   -- let k : ℤ := r.num,
--   -- use k,
--   -- rw dist_eq_norm,
--   -- apply lt_of_le_of_lt _ hr,
--   -- rw show ∥x - k∥ = ∥(x - r : ℚ_[p]) + (r - k)∥,
--   -- { rw padic_norm_z, congr' 1, ring, simp [cast_eq_of_rat], sorry },
--   -- apply le_trans (padic_norm_e.nonarchimedean _ _),
--   -- rw max_le_iff,
--   -- refine ⟨le_refl _, _⟩,
-- end

-- lemma dense_embedding : dense_embedding (coe : ℤ → ℤ_[p]) :=
-- dense_embedding.mk' _ continuous_of_discrete_topology
--   (begin intro x, rw mem_closure_range_iff, apply z_dense end)
--   (λ x y, by exact_mod_cast id)
--   (begin  end )


end padic_int

namespace padic_norm_z
variables {p : ℕ} [fact p.prime]

lemma padic_val_of_cong_pow_p {z1 z2 : ℤ} {n : ℕ} (hz : z1 ≡ z2 [ZMOD ↑(p^n)]) :
      ∥(z1 - z2 : ℚ_[p])∥ ≤ ↑(↑p ^ (-n : ℤ) : ℚ) :=
have hdvd : ↑(p^n) ∣ z2 - z1, from int.modeq.modeq_iff_dvd.1 hz,
have (z2 - z1 : ℚ_[p]) = ↑(↑(z2 - z1) : ℚ), by norm_cast,
begin
  rw [norm_sub_rev, this, padic_norm_e.eq_padic_norm],
  exact_mod_cast padic_norm.le_of_dvd p hdvd
end

end padic_norm_z
