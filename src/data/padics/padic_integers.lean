/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro
-/
import data.int.modeq
import data.padics.padic_numbers

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
  zero_ne_one := padic_int.zero_ne_one,
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

local attribute [reducible] padic_int

lemma mul_inv : ∀ {z : ℤ_[p]}, ∥z∥ = 1 → z * z.inv = 1
| ⟨k, _⟩ h :=
  begin
    have hk : k ≠ 0, from λ h', @zero_ne_one ℚ_[p] _ _ _ (by simpa [h'] using h),
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

instance is_ring_hom_coe : is_ring_hom (coe : ℤ_[p] → ℚ_[p]) :=
{ map_one := rfl,
  map_mul := coe_mul,
  map_add := coe_add }

instance : algebra ℤ_[p] ℚ_[p] := (ring_hom.of coe).to_algebra

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
