/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro
-/
import data.int.modeq
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
  show ↑p ^ -valuation x ≤ ↑p ^ 0,
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

def mk_units {u : ℚ_[p]} (h : ∥u∥ = 1) : units ℤ_[p] :=
let z : ℤ_[p] := ⟨u, le_of_eq h⟩ in ⟨z, z.inv, mul_inv h, inv_mul h⟩

@[simp]
lemma mk_units_eq {u : ℚ_[p]} (h : ∥u∥ = 1) : ((mk_units h : ℤ_[p]) : ℚ_[p]) = u :=
rfl

@[simp] lemma norm_units (u : units ℤ_[p]) : ∥(u : ℤ_[p])∥ = 1 :=
is_unit_iff.mp $ by simp

lemma exists_repr {x : ℤ_[p]} (hx : x ≠ 0) :
  ∃ (u : units ℤ_[p]) (n : ℕ), x = u*p^n :=
begin
  let u : ℚ_[p] := x*p^(-x.valuation),
  have repr : (x : ℚ_[p]) = u*p^x.valuation,
  { rw [mul_assoc, ← fpow_add],
    { simp },
    { exact_mod_cast nat.prime.ne_zero ‹_› } },
  have hu : ∥u∥ = 1,
    by simp [hx, nat.fpow_ne_zero_of_pos (by exact_mod_cast nat.prime.pos ‹_›) x.valuation,
             norm_eq_pow_val, fpow_neg, inv_mul_cancel, -cast_eq_of_rat_of_nat],
  obtain ⟨n, hn⟩ : ∃ n : ℕ, valuation x = n,
    from int.eq_coe_of_zero_le (valuation_nonneg x),
  use [mk_units hu, n],
  apply subtype.val_injective,
  simp [hn, repr]
end

def unit_coeff {x : ℤ_[p]} (hx : x ≠ 0) : units ℤ_[p] :=
classical.some $ exists_repr hx

def repr_exp {x : ℤ_[p]} (hx : x ≠ 0) : ℕ :=
classical.some $ classical.some_spec (exists_repr hx)

lemma repr_exp_spec {x : ℤ_[p]} (hx : x ≠ 0) :
  x = ↑(unit_coeff hx) * ↑p ^ (repr_exp hx) :=
classical.some_spec (classical.some_spec (exists_repr hx))

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

/-- `base : ℤ_[p]` is `p` considered as a p-adic integer. -/
def base : ℤ_[p] :=
⟨p, le_of_lt padic_norm_e.norm_p_lt_one⟩

lemma base_eq_p : (base : ℤ_[p]) = p := subtype.ext $ by simp [base]

lemma base_nonunit : base ∈ nonunits ℤ_[p] :=
by simp [base, -cast_eq_of_rat_of_nat, -padic_norm_e.norm_p, padic_norm_e.norm_p_lt_one]

lemma norm_nonunit : ∥(base : ℤ_[p])∥ = 1 / p :=
by simp [base, -cast_eq_of_rat_of_nat, padic_norm_e.norm_p]

instance : algebra ℤ_[p] ℚ_[p] := (coe.ring_hom : ℤ_[p] →+* ℚ_[p]).to_algebra

lemma not_a_field : local_ring.maximal_ideal ℤ_[p] ≠ ⊥ :=
begin
  refine (submodule.ne_bot_iff _).mpr ⟨base, _, _⟩,
  { exact base_nonunit },
  { rw [ne.def, ← norm_eq_zero, norm_nonunit],
    apply one_div_ne_zero,
    exact_mod_cast _inst_1.ne_zero }
end

instance : can_lift ℤ_[p] (units ℤ_[p]) :=
{ coe := coe,
  cond := is_unit,
  prf := λ z hz, hz }

lemma ideal_is_principal_aux
  (s : ideal ℤ_[p])
  (h_all_pows : ¬∃ (i : ℕ), ¬s ≤ ideal.span {base ^ (i+1)}) :
  s = submodule.span ℤ_[p] {0} :=
begin
  suffices : s = ⊥, by simpa,
  push_neg at h_all_pows,
  rw submodule.eq_bot_iff,
  intros x hxs,
  by_contradiction h_xne,
  rcases exists_repr h_xne with ⟨xu, n, hxu⟩,
  have := h_all_pows (n+1) hxs,
  rw [ideal.mem_span_singleton', base_eq_p, hxu] at this,
  cases this with a ha,
  have := congr_arg has_norm.norm ha,
  refine ne_of_lt _ this,
  calc _ = ∥a∥ * ↑p ^ (-(n + 1 + 1) : ℤ) : by simp
      ... ≤ ↑p ^ (-(n + 1 + 1) : ℤ) : _
      ... < ↑p ^ (-n : ℤ) : _
      ... = _ : _,
  { refine mul_le_of_le_one_left _ (padic_norm_z.le_one _),
    apply fpow_nonneg_of_nonneg,
    exact_mod_cast le_of_lt (nat.prime.pos ‹_›) },
  { rw fpow_lt_iff_lt,
    { linarith },
    { exact_mod_cast nat.prime.one_lt ‹_› } },
  { simp }
end

lemma ideal_is_principal (s : ideal ℤ_[p]) : s.is_principal :=
begin
  constructor,
  by_cases h_bot : s = ⊥,
  { subst h_bot,
    use 0,
    simp },
  { have h_bot' := h_bot,
    rw submodule.eq_bot_iff at h_bot,
    push_neg at h_bot,
    rcases h_bot with ⟨z, hzs, hznz⟩,
    have exists_n : ∃ n : ℕ, ∃ z, ∃ u : units ℤ_[p], z ∈ s ∧ z = ↑u * ↑p ^ n,
      from ⟨repr_exp hznz, z, unit_coeff hznz, hzs, repr_exp_spec hznz⟩,
    let min_n := nat.find exists_n,
    obtain ⟨min_z, u, minz_s, minz_spec⟩ : ∃ (z : ℤ_[p]) (u : units ℤ_[p]), z ∈ s ∧ z = ↑u * ↑p ^ min_n :=
      nat.find_spec exists_n,
    have uinv_min_z : ↑u⁻¹ * min_z = p ^ min_n,
    { symmetry,
      rw [units.eq_inv_mul_iff_mul_eq, minz_spec] },
    have uinv_min_z_s : ↑u⁻¹ * min_z ∈ s, from ideal.mul_mem_left _ minz_s,
    rw uinv_min_z at uinv_min_z_s,
    have span_sub_s : submodule.span ℤ_[p] {↑p ^ min_n} ≤ s,
    { exact (submodule.span_singleton_le_iff_mem _ _).mpr uinv_min_z_s, },
    have s_sub_span : s ≤ submodule.span ℤ_[p] {↑p ^ min_n},
    { intros y hy,
      have exists_n_spec := @nat.find_min' _ _ exists_n,
      dsimp at exists_n_spec,
      by_cases hyz : y = 0,
      { simp [hyz] },
      { have min_n_y : min_n ≤ repr_exp hyz := @exists_n_spec (repr_exp hyz) ⟨y, unit_coeff hyz, hy, repr_exp_spec hyz⟩,
        rw repr_exp_spec hyz,
        apply ideal.mul_mem_left _ _,
        have : repr_exp hyz = (repr_exp hyz - min_n) + min_n, {omega},
        rw [this, _root_.pow_add],
        apply ideal.mul_mem_left _ (submodule.mem_span_singleton_self _) } },
    use p ^ min_n,
    apply le_antisymm; assumption }

end

lemma ideal_is_principal2 (s : ideal ℤ_[p]) : s.is_principal :=
begin
  constructor,
  by_cases h_all_pows : ∃ i : ℕ, ¬ s ≤ ideal.span {base^(i)},
  { let i := nat.find h_all_pows,
    have i_spec : ¬s ≤ ideal.span {base ^ (i)} := nat.find_spec h_all_pows,
    have i_spec2 :  ∀ m, ¬s ≤ ideal.span {base ^ (m )} → i ≤ m := @nat.find_min' _ _ h_all_pows,
    have s_i_pred : s ≤ ideal.span {base^i.pred},
    { by_contradiction h,
      have := i_spec2 _ h,
      rw nat.le_pred_se },
     },
  -- { use 0, exact ideal_is_principal_aux s h_all_pows }
end

#check ideal.span_singleton_mul_right_unit

lemma ideal_is_principal (s : ideal ℤ_[p]) : s.is_principal :=
begin
  constructor,
  by_cases h_all_pows :
    ∃ i : ℕ, s ≤ ideal.span {(base : ℤ_[p]) ^ i} ∧ ¬ s ≤ ideal.span {base ^ (i+1)},
  { rcases h_all_pows with ⟨i, hsi, hsi_succ⟩,
    have : ∃ z, z ∈ s ∧ z ∉ (ideal.span {base ^ (i+1)} : ideal ℤ_[p]) := sorry,
    rcases this with ⟨z, hzs, hznsp⟩,
    have : z ∈ (ideal.span {base ^ i} : ideal ℤ_[p]) := sorry,
    rw ideal.mem_span_singleton' at this,
    cases this with g hgz,
    have hg_ne : g ∉ (ideal.span {base} : ideal ℤ_[p]) := sorry,
    have hg_unit : is_unit g := sorry,
    lift g to units ℤ_[p] using hg_unit,
    have : z * g.inv = base ^ i := sorry,
  }
end



lemma ideal_is_principal (s : ideal ℤ_[p]) : s.is_principal :=
begin
  constructor,
  by_cases h_all_pows : ∀ i : ℕ, s ≤ submodule.span ℤ_[p] {nonunit ^ (i+1)},
  { admit },
  { push_neg at h_all_pows,
    cases h_all_pows with i h_si,
    have : ∃ z, z ∈ s ∧ z ∉ (submodule.span ℤ_[p] {nonunit ^ (i+1)} : ideal ℤ_[p]) := sorry,
    rcases this with ⟨z, hzs, hznsp⟩,
     }
end

instance : discrete_valuation_ring ℤ_[p] :=
{ principal := ideal_is_principal,
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩,
  not_a_field' := not_a_field,
  .. padic_int.local_ring }
/- (discrete_valuation_ring.iff_PID_with_one_nonzero_prime _).mpr
⟨ _,
  _ ⟩ -/

#check is_principal_ideal_ring
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
