/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro, Johan Commelin
-/
import number_theory.padics.padic_numbers
import ring_theory.discrete_valuation_ring
import topology.metric_space.cau_seq_filter

/-!
# p-adic integers

This file defines the `p`-adic integers `ℤ_[p]` as the subtype of `ℚ_[p]` with norm `≤ 1`.
We show that `ℤ_[p]`
* is complete,
* is nonarchimedean,
* is a normed ring,
* is a local ring, and
* is a discrete valuation ring.

The relation between `ℤ_[p]` and `zmod p` is established in another file.

## Important definitions

* `padic_int` : the type of `p`-adic integers

## Notation

We introduce the notation `ℤ_[p]` for the `p`-adic integers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact p.prime]` as a type class argument.

Coercions into `ℤ_[p]` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, p-adic integer
-/

open padic metric local_ring
noncomputable theory
open_locale classical

/-- The `p`-adic integers `ℤ_[p]` are the `p`-adic numbers with norm `≤ 1`. -/
def padic_int (p : ℕ) [fact p.prime] := {x : ℚ_[p] // ‖x‖ ≤ 1}

notation `ℤ_[`p`]` := padic_int p

namespace padic_int

/-! ### Ring structure and coercion to `ℚ_[p]` -/

variables {p : ℕ} [fact p.prime]

instance : has_coe ℤ_[p] ℚ_[p] := ⟨subtype.val⟩

lemma ext {x y : ℤ_[p]} : (x : ℚ_[p]) = y → x = y := subtype.ext

variables (p)

/-- The `p`-adic integers as a subring of `ℚ_[p]`. -/
def subring : subring (ℚ_[p]) :=
{ carrier := {x : ℚ_[p] | ‖x‖ ≤ 1},
  zero_mem' := by norm_num,
  one_mem' := by norm_num,
  add_mem' := λ x y hx hy, (padic_norm_e.nonarchimedean _ _).trans $ max_le_iff.2 ⟨hx, hy⟩,
  mul_mem' := λ x y hx hy, (padic_norm_e.mul _ _).trans_le $ mul_le_one hx (norm_nonneg _) hy,
  neg_mem' := λ x hx, (norm_neg _).trans_le hx }

@[simp] lemma mem_subring_iff {x : ℚ_[p]} : x ∈ subring p ↔ ‖x‖ ≤ 1 := iff.rfl

variables {p}

/-- Addition on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : has_add ℤ_[p] := (by apply_instance : has_add (subring p))

/-- Multiplication on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : has_mul ℤ_[p] := (by apply_instance : has_mul (subring p))

/-- Negation on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : has_neg ℤ_[p] := (by apply_instance : has_neg (subring p))

/-- Subtraction on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : has_sub ℤ_[p] := (by apply_instance : has_sub (subring p))

/-- Zero on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : has_zero ℤ_[p] := (by apply_instance : has_zero (subring p))

instance : inhabited ℤ_[p] := ⟨0⟩

/-- One on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : has_one ℤ_[p] := ⟨⟨1, by norm_num⟩⟩

@[simp] lemma mk_zero {h} : (⟨0, h⟩ : ℤ_[p]) = (0 : ℤ_[p]) := rfl

@[simp] lemma val_eq_coe (z : ℤ_[p]) : z.val = z := rfl

@[simp, norm_cast] lemma coe_add (z1 z2 : ℤ_[p]) : ((z1 + z2 : ℤ_[p]) : ℚ_[p]) = z1 + z2 := rfl
@[simp, norm_cast] lemma coe_mul (z1 z2 : ℤ_[p]) : ((z1 * z2 : ℤ_[p]) : ℚ_[p]) = z1 * z2 := rfl
@[simp, norm_cast] lemma coe_neg (z1 : ℤ_[p]) : ((-z1 : ℤ_[p]) : ℚ_[p]) = -z1 := rfl
@[simp, norm_cast] lemma coe_sub (z1 z2 : ℤ_[p]) : ((z1 - z2 : ℤ_[p]) : ℚ_[p]) = z1 - z2 := rfl
@[simp, norm_cast] lemma coe_one : ((1 : ℤ_[p]) : ℚ_[p]) = 1 := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : ℤ_[p]) : ℚ_[p]) = 0 := rfl

lemma coe_eq_zero (z : ℤ_[p]) : (z : ℚ_[p]) = 0 ↔ z = 0 :=
by rw [← coe_zero, subtype.coe_inj]

lemma coe_ne_zero (z : ℤ_[p]) : (z : ℚ_[p]) ≠ 0 ↔ z ≠ 0 := z.coe_eq_zero.not

instance : add_comm_group ℤ_[p] :=
(by apply_instance : add_comm_group (subring p))

instance : comm_ring ℤ_[p] :=
(by apply_instance : comm_ring (subring p))

@[simp, norm_cast] lemma coe_nat_cast (n : ℕ) : ((n : ℤ_[p]) : ℚ_[p]) = n := rfl
@[simp, norm_cast] lemma coe_int_cast (z : ℤ) : ((z : ℤ_[p]) : ℚ_[p]) = z := rfl

/-- The coercion from `ℤ_[p]` to `ℚ_[p]` as a ring homomorphism. -/
def coe.ring_hom : ℤ_[p] →+* ℚ_[p] := (subring p).subtype

@[simp, norm_cast] lemma coe_pow (x : ℤ_[p]) (n : ℕ) : (↑(x^n) : ℚ_[p]) = (↑x : ℚ_[p])^n := rfl

@[simp] lemma mk_coe (k : ℤ_[p]) : (⟨k, k.2⟩ : ℤ_[p]) = k := subtype.coe_eta _ _

/-- The inverse of a `p`-adic integer with norm equal to `1` is also a `p`-adic integer.
Otherwise, the inverse is defined to be `0`. -/
def inv : ℤ_[p] → ℤ_[p]
| ⟨k, _⟩ := if h : ‖k‖ = 1 then ⟨k⁻¹, by simp [h]⟩ else 0

instance : char_zero ℤ_[p] :=
{ cast_injective :=
  λ m n h, nat.cast_injective $
  show (m:ℚ_[p]) = n, by { rw subtype.ext_iff at h, norm_cast at h, exact h } }

@[simp, norm_cast] lemma coe_int_eq (z1 z2 : ℤ) : (z1 : ℤ_[p]) = z2 ↔ z1 = z2 :=
suffices (z1 : ℚ_[p]) = z2 ↔ z1 = z2, from iff.trans (by norm_cast) this,
by norm_cast

/-- A sequence of integers that is Cauchy with respect to the `p`-adic norm converges to a `p`-adic
integer. -/
def of_int_seq (seq : ℕ → ℤ) (h : is_cau_seq (padic_norm p) (λ n, seq n)) : ℤ_[p] :=
⟨⟦⟨_, h⟩⟧,
 show ↑(padic_seq.norm _) ≤ (1 : ℝ), begin
   rw padic_seq.norm,
   split_ifs with hne; norm_cast,
   { exact zero_le_one },
   { apply padic_norm.of_int }
 end ⟩

end padic_int

namespace padic_int

/-! ### Instances

We now show that `ℤ_[p]` is a
* complete metric space
* normed ring
* integral domain
-/

variables (p : ℕ) [fact p.prime]

instance : metric_space ℤ_[p] := subtype.metric_space

instance complete_space : complete_space ℤ_[p] :=
have is_closed {x : ℚ_[p] | ‖x‖ ≤ 1}, from is_closed_le continuous_norm continuous_const,
this.complete_space_coe

instance : has_norm ℤ_[p] := ⟨λ z, ‖(z : ℚ_[p])‖⟩

variables {p}

lemma norm_def {z : ℤ_[p]} : ‖z‖ = ‖(z : ℚ_[p])‖ := rfl

variables (p)

instance : normed_comm_ring ℤ_[p] :=
{ dist_eq := λ ⟨_, _⟩ ⟨_, _⟩, rfl,
  norm_mul := by simp [norm_def],
  norm := norm, .. padic_int.comm_ring, .. padic_int.metric_space p }

instance : norm_one_class ℤ_[p] := ⟨norm_def.trans norm_one⟩

instance is_absolute_value : is_absolute_value (λ z : ℤ_[p], ‖z‖) :=
{ abv_nonneg := norm_nonneg,
  abv_eq_zero := λ ⟨_, _⟩, by simp [norm_eq_zero],
  abv_add := λ ⟨_,_⟩ ⟨_, _⟩, norm_add_le _ _,
  abv_mul := λ _ _, by simp only [norm_def, padic_norm_e.mul, padic_int.coe_mul] }

variables {p}

instance : is_domain ℤ_[p] := function.injective.is_domain (subring p).subtype subtype.coe_injective

end padic_int

namespace padic_int

/-! ### Norm -/

variables {p : ℕ} [fact p.prime]

lemma norm_le_one (z : ℤ_[p]) : ‖z‖ ≤ 1 := z.2

@[simp] lemma norm_mul (z1 z2 : ℤ_[p]) : ‖z1 * z2‖ = ‖z1‖ * ‖z2‖ := by simp [norm_def]

@[simp] lemma norm_pow (z : ℤ_[p]) : ∀ n : ℕ, ‖z ^ n‖ = ‖z‖ ^ n
| 0 := by simp
| (k + 1) := by { rw [pow_succ, pow_succ, norm_mul], congr, apply norm_pow }

theorem nonarchimedean (q r : ℤ_[p]) : ‖q + r‖ ≤ max (‖q‖) (‖r‖) := padic_norm_e.nonarchimedean _ _

theorem norm_add_eq_max_of_ne {q r : ℤ_[p]} : ‖q‖ ≠ ‖r‖ → ‖q+r‖ = max (‖q‖) (‖r‖) :=
padic_norm_e.add_eq_max_of_ne

lemma norm_eq_of_norm_add_lt_right {z1 z2 : ℤ_[p]} (h : ‖z1 + z2‖ < ‖z2‖) : ‖z1‖ = ‖z2‖ :=
by_contradiction $ λ hne, not_lt_of_ge (by rw norm_add_eq_max_of_ne hne; apply le_max_right) h

lemma norm_eq_of_norm_add_lt_left {z1 z2 : ℤ_[p]} (h : ‖z1 + z2‖ < ‖z1‖) : ‖z1‖ = ‖z2‖ :=
by_contradiction $ λ hne, not_lt_of_ge (by rw norm_add_eq_max_of_ne hne; apply le_max_left) h

@[simp] lemma padic_norm_e_of_padic_int (z : ℤ_[p]) : ‖(z : ℚ_[p])‖ = ‖z‖ := by simp [norm_def]

lemma norm_int_cast_eq_padic_norm (z : ℤ) : ‖(z : ℤ_[p])‖ = ‖(z : ℚ_[p])‖ := by simp [norm_def]

@[simp] lemma norm_eq_padic_norm {q : ℚ_[p]} (hq : ‖q‖ ≤ 1) : @norm ℤ_[p] _ ⟨q, hq⟩ = ‖q‖ := rfl

@[simp] lemma norm_p : ‖(p : ℤ_[p])‖ = p⁻¹ := padic_norm_e.norm_p

@[simp] lemma norm_p_pow (n : ℕ) : ‖(p : ℤ_[p])^n‖ = p^(-n:ℤ) := padic_norm_e.norm_p_pow n

private def cau_seq_to_rat_cau_seq (f : cau_seq ℤ_[p] norm) : cau_seq ℚ_[p] (λ a, ‖a‖) :=
⟨ λ n, f n, λ _ hε, by simpa [norm, norm_def] using f.cauchy hε ⟩

variables (p)

instance complete : cau_seq.is_complete ℤ_[p] norm :=
⟨ λ f,
  have hqn : ‖cau_seq.lim (cau_seq_to_rat_cau_seq f)‖ ≤ 1,
    from padic_norm_e_lim_le zero_lt_one (λ _, norm_le_one _),
  ⟨⟨_, hqn⟩, λ ε, by simpa [norm, norm_def] using cau_seq.equiv_lim (cau_seq_to_rat_cau_seq f) ε⟩⟩

end padic_int

namespace padic_int

variables (p : ℕ) [hp : fact p.prime]

include hp

lemma exists_pow_neg_lt {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, ↑p ^ -(k : ℤ) < ε :=
begin
  obtain ⟨k, hk⟩ := exists_nat_gt ε⁻¹,
  use k,
  rw ← inv_lt_inv hε (_root_.zpow_pos_of_pos _ _),
  { rw [zpow_neg, inv_inv, zpow_coe_nat],
    apply lt_of_lt_of_le hk,
    norm_cast,
    apply le_of_lt,
    convert nat.lt_pow_self _ _ using 1,
    exact hp.1.one_lt },
  { exact_mod_cast hp.1.pos }
end

lemma exists_pow_neg_lt_rat {ε : ℚ} (hε : 0 < ε) : ∃ k : ℕ, ↑p ^ -(k : ℤ) < ε :=
begin
  obtain ⟨k, hk⟩ := @exists_pow_neg_lt p _ ε (by exact_mod_cast hε),
  use k,
  rw (show (p : ℝ) = (p : ℚ), by simp) at hk,
  exact_mod_cast hk
end

variable {p}

lemma norm_int_lt_one_iff_dvd (k : ℤ) : ‖(k : ℤ_[p])‖ < 1 ↔ (p : ℤ) ∣ k :=
suffices ‖(k : ℚ_[p])‖ < 1 ↔ ↑p ∣ k, by rwa norm_int_cast_eq_padic_norm,
padic_norm_e.norm_int_lt_one_iff_dvd k

lemma norm_int_le_pow_iff_dvd {k : ℤ} {n : ℕ} : ‖(k : ℤ_[p])‖ ≤ p ^ (-n : ℤ) ↔ (p ^ n : ℤ) ∣ k :=
suffices ‖(k : ℚ_[p])‖ ≤ p ^ (-n : ℤ) ↔ ↑(p ^ n) ∣ k,
by simpa [norm_int_cast_eq_padic_norm], padic_norm_e.norm_int_le_pow_iff_dvd _ _

/-! ### Valuation on `ℤ_[p]` -/

/-- `padic_int.valuation` lifts the `p`-adic valuation on `ℚ` to `ℤ_[p]`.  -/
def valuation (x : ℤ_[p]) := padic.valuation (x : ℚ_[p])

lemma norm_eq_pow_val {x : ℤ_[p]} (hx : x ≠ 0) : ‖x‖ = (p : ℝ) ^ -x.valuation :=
begin
  convert padic.norm_eq_pow_val _,
  contrapose! hx,
  exact subtype.val_injective hx
end

@[simp] lemma valuation_zero : valuation (0 : ℤ_[p]) = 0 := padic.valuation_zero

@[simp] lemma valuation_one : valuation (1 : ℤ_[p]) = 0 := padic.valuation_one

@[simp] lemma valuation_p : valuation (p : ℤ_[p]) = 1 := by simp [valuation]

lemma valuation_nonneg (x : ℤ_[p]) : 0 ≤ x.valuation :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  have h : (1 : ℝ) < p := by exact_mod_cast hp.1.one_lt,
  rw [← neg_nonpos, ← (zpow_strict_mono h).le_iff_le],
  show (p : ℝ) ^ -valuation x ≤ p ^ (0 : ℤ),
  rw [← norm_eq_pow_val hx],
  simpa using x.property
end

@[simp] lemma valuation_p_pow_mul (n : ℕ) (c : ℤ_[p]) (hc : c ≠ 0) :
  (↑p ^ n * c).valuation = n + c.valuation :=
begin
  have : ‖(↑p ^ n * c)‖ = ‖(p ^ n : ℤ_[p])‖ * ‖c‖,
  { exact norm_mul _ _ },
  have aux : (↑p ^ n * c) ≠ 0,
  { contrapose! hc, rw mul_eq_zero at hc, cases hc,
    { refine (hp.1.ne_zero _).elim,
      exact_mod_cast (pow_eq_zero hc) },
    { exact hc } },
  rwa [norm_eq_pow_val aux, norm_p_pow, norm_eq_pow_val hc,
      ← zpow_add₀, ← neg_add, zpow_inj, neg_inj] at this,
  { exact_mod_cast hp.1.pos },
  { exact_mod_cast hp.1.ne_one },
  { exact_mod_cast hp.1.ne_zero }
end

section units

/-! ### Units of `ℤ_[p]` -/

local attribute [reducible] padic_int

lemma mul_inv : ∀ {z : ℤ_[p]}, ‖z‖ = 1 → z * z.inv = 1
| ⟨k, _⟩ h :=
  begin
    have hk : k ≠ 0, from λ h', zero_ne_one' ℚ_[p] (by simpa [h'] using h),
    unfold padic_int.inv,
    rw [norm_eq_padic_norm] at h,
    rw dif_pos h,
    apply subtype.ext_iff_val.2,
    simp [mul_inv_cancel hk]
  end

lemma inv_mul {z : ℤ_[p]} (hz : ‖z‖ = 1) : z.inv * z = 1 := by rw [mul_comm, mul_inv hz]

lemma is_unit_iff {z : ℤ_[p]} : is_unit z ↔ ‖z‖ = 1 :=
⟨λ h, begin
  rcases is_unit_iff_dvd_one.1 h with ⟨w, eq⟩,
  refine le_antisymm (norm_le_one _) _,
  have := mul_le_mul_of_nonneg_left (norm_le_one w) (norm_nonneg z),
  rwa [mul_one, ← norm_mul, ← eq, norm_one] at this
end, λ h, ⟨⟨z, z.inv, mul_inv h, inv_mul h⟩, rfl⟩⟩

lemma norm_lt_one_add {z1 z2 : ℤ_[p]} (hz1 : ‖z1‖ < 1) (hz2 : ‖z2‖ < 1) : ‖z1 + z2‖ < 1 :=
lt_of_le_of_lt (nonarchimedean _ _) (max_lt hz1 hz2)

lemma norm_lt_one_mul {z1 z2 : ℤ_[p]} (hz2 : ‖z2‖ < 1) : ‖z1 * z2‖ < 1 :=
calc ‖z1 * z2‖ = ‖z1‖ * ‖z2‖ : by simp
          ... < 1 : mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one _) (norm_nonneg _) hz2

@[simp] lemma mem_nonunits {z : ℤ_[p]} : z ∈ nonunits ℤ_[p] ↔ ‖z‖ < 1 :=
by rw lt_iff_le_and_ne; simp [norm_le_one z, nonunits, is_unit_iff]

/-- A `p`-adic number `u` with `‖u‖ = 1` is a unit of `ℤ_[p]`. -/
def mk_units {u : ℚ_[p]} (h : ‖u‖ = 1) : ℤ_[p]ˣ :=
let z : ℤ_[p] := ⟨u, le_of_eq h⟩ in ⟨z, z.inv, mul_inv h, inv_mul h⟩

@[simp] lemma mk_units_eq {u : ℚ_[p]} (h : ‖u‖ = 1) : ((mk_units h : ℤ_[p]) : ℚ_[p]) = u := rfl

@[simp] lemma norm_units (u : ℤ_[p]ˣ) : ‖(u : ℤ_[p])‖ = 1 := is_unit_iff.mp $ by simp

/-- `unit_coeff hx` is the unit `u` in the unique representation `x = u * p ^ n`.
See `unit_coeff_spec`. -/
def unit_coeff {x : ℤ_[p]} (hx : x ≠ 0) : ℤ_[p]ˣ :=
let u : ℚ_[p] := x * p ^ -x.valuation in
have hu : ‖u‖ = 1,
by simp [hx, nat.zpow_ne_zero_of_pos (by exact_mod_cast hp.1.pos) x.valuation,
         norm_eq_pow_val, zpow_neg, inv_mul_cancel],
mk_units hu

@[simp] lemma unit_coeff_coe {x : ℤ_[p]} (hx : x ≠ 0) :
  (unit_coeff hx : ℚ_[p]) = x * p ^ -x.valuation := rfl

lemma unit_coeff_spec {x : ℤ_[p]} (hx : x ≠ 0) :
  x = (unit_coeff hx : ℤ_[p]) * p ^ int.nat_abs (valuation x) :=
begin
  apply subtype.coe_injective,
  push_cast,
  have repr : (x : ℚ_[p]) = (unit_coeff hx) * p ^ x.valuation,
  { rw [unit_coeff_coe, mul_assoc, ← zpow_add₀],
    { simp },
    { exact_mod_cast hp.1.ne_zero } },
  convert repr using 2,
  rw [← zpow_coe_nat, int.nat_abs_of_nonneg (valuation_nonneg x)]
end

end units

section norm_le_iff

/-! ### Various characterizations of open unit balls -/

lemma norm_le_pow_iff_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
  ‖x‖ ≤ p ^ (-n : ℤ) ↔ ↑n ≤ x.valuation :=
begin
  rw norm_eq_pow_val hx,
  lift x.valuation to ℕ using x.valuation_nonneg with k hk,
  simp only [int.coe_nat_le, zpow_neg, zpow_coe_nat],
  have aux : ∀ n : ℕ, 0 < (p ^ n : ℝ),
  { apply pow_pos, exact_mod_cast hp.1.pos },
  rw [inv_le_inv (aux _) (aux _)],
  have : p ^ n ≤ p ^ k ↔ n ≤ k := (pow_strict_mono_right hp.1.one_lt).le_iff_le,
  rw [← this],
  norm_cast
end

lemma mem_span_pow_iff_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
  x ∈ (ideal.span {p ^ n} : ideal ℤ_[p]) ↔ ↑n ≤ x.valuation :=
begin
  rw [ideal.mem_span_singleton],
  split,
  { rintro ⟨c, rfl⟩,
    suffices : c ≠ 0,
    { rw [valuation_p_pow_mul _ _ this, le_add_iff_nonneg_right], apply valuation_nonneg },
    contrapose! hx, rw [hx, mul_zero] },
  { rw [unit_coeff_spec hx] { occs := occurrences.pos [2] },
    lift x.valuation to ℕ using x.valuation_nonneg with k hk,
    simp only [int.nat_abs_of_nat, units.is_unit, is_unit.dvd_mul_left, int.coe_nat_le],
    intro H,
    obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le H,
    simp only [pow_add, dvd_mul_right] }
end

lemma norm_le_pow_iff_mem_span_pow (x : ℤ_[p]) (n : ℕ) :
  ‖x‖ ≤ p ^ (-n : ℤ) ↔ x ∈ (ideal.span {p ^ n} : ideal ℤ_[p]) :=
begin
  by_cases hx : x = 0,
  { subst hx,
    simp only [norm_zero, zpow_neg, zpow_coe_nat, inv_nonneg, iff_true, submodule.zero_mem],
    exact_mod_cast nat.zero_le _ },
  rw [norm_le_pow_iff_le_valuation x hx, mem_span_pow_iff_le_valuation x hx]
end

lemma norm_le_pow_iff_norm_lt_pow_add_one (x : ℤ_[p]) (n : ℤ) : ‖x‖ ≤ p ^ n ↔ ‖x‖ < p ^ (n + 1) :=
begin
  rw norm_def, exact padic.norm_le_pow_iff_norm_lt_pow_add_one _ _,
end

lemma norm_lt_pow_iff_norm_le_pow_sub_one (x : ℤ_[p]) (n : ℤ) : ‖x‖ < p ^ n ↔ ‖x‖ ≤ p ^ (n - 1) :=
by rw [norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel]

lemma norm_lt_one_iff_dvd (x : ℤ_[p]) : ‖x‖ < 1 ↔ ↑p ∣ x :=
begin
  have := norm_le_pow_iff_mem_span_pow x 1,
  rw [ideal.mem_span_singleton, pow_one] at this,
  rw [← this, norm_le_pow_iff_norm_lt_pow_add_one],
  simp only [zpow_zero, int.coe_nat_zero, int.coe_nat_succ, add_left_neg, zero_add]
end

@[simp] lemma pow_p_dvd_int_iff (n : ℕ) (a : ℤ) : (p ^ n : ℤ_[p]) ∣ a ↔ ↑p ^ n ∣ a :=
by rw [← norm_int_le_pow_iff_dvd, norm_le_pow_iff_mem_span_pow, ideal.mem_span_singleton]

end norm_le_iff

section dvr

/-! ### Discrete valuation ring -/

instance : local_ring ℤ_[p] :=
local_ring.of_nonunits_add $ by simp only [mem_nonunits]; exact λ x y, norm_lt_one_add

lemma p_nonnunit : (p : ℤ_[p]) ∈ nonunits ℤ_[p] :=
have (p : ℝ)⁻¹ < 1, from inv_lt_one $ by exact_mod_cast hp.1.one_lt,
by simp [this]

lemma maximal_ideal_eq_span_p : maximal_ideal ℤ_[p] = ideal.span {p} :=
begin
  apply le_antisymm,
  { intros x hx,
    simp only [local_ring.mem_maximal_ideal, mem_nonunits] at hx,
    rwa [ideal.mem_span_singleton, ← norm_lt_one_iff_dvd] },
  { rw [ideal.span_le, set.singleton_subset_iff], exact p_nonnunit }
end

lemma prime_p : prime (p : ℤ_[p]) :=
begin
  rw [← ideal.span_singleton_prime, ← maximal_ideal_eq_span_p],
  { apply_instance },
  { exact_mod_cast hp.1.ne_zero }
end

lemma irreducible_p : irreducible (p : ℤ_[p]) := prime.irreducible prime_p

instance : discrete_valuation_ring ℤ_[p] :=
discrete_valuation_ring.of_has_unit_mul_pow_irreducible_factorization
⟨p, irreducible_p, λ x hx, ⟨x.valuation.nat_abs, unit_coeff hx,
  by rw [mul_comm, ← unit_coeff_spec hx]⟩⟩

lemma ideal_eq_span_pow_p {s : ideal ℤ_[p]} (hs : s ≠ ⊥) : ∃ n : ℕ, s = ideal.span {p ^ n} :=
discrete_valuation_ring.ideal_eq_span_pow_irreducible hs irreducible_p

open cau_seq

instance : is_adic_complete (maximal_ideal ℤ_[p]) ℤ_[p] :=
{ prec' := λ x hx,
  begin
    simp only [← ideal.one_eq_top, smul_eq_mul, mul_one, smodeq.sub_mem, maximal_ideal_eq_span_p,
      ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow] at hx ⊢,
    let x' : cau_seq ℤ_[p] norm := ⟨x, _⟩, swap,
    { intros ε hε, obtain ⟨m, hm⟩ := exists_pow_neg_lt p hε,
      refine ⟨m, λ n hn, lt_of_le_of_lt _ hm⟩, rw [← neg_sub, norm_neg], exact hx hn },
    { refine ⟨x'.lim, λ n, _⟩,
      have : (0:ℝ) < p ^ (-n : ℤ), { apply zpow_pos_of_pos, exact_mod_cast hp.1.pos },
      obtain ⟨i, hi⟩ := equiv_def₃ (equiv_lim x') this,
      by_cases hin : i ≤ n,
      { exact (hi i le_rfl n hin).le },
      { push_neg at hin, specialize hi i le_rfl i le_rfl, specialize hx hin.le,
        have := nonarchimedean (x n - x i) (x i - x'.lim),
        rw [sub_add_sub_cancel] at this,
        refine this.trans (max_le_iff.mpr ⟨hx, hi.le⟩) } }
  end }

end dvr

section fraction_ring

instance algebra : algebra ℤ_[p] ℚ_[p] := algebra.of_subring (subring p)

@[simp] lemma algebra_map_apply (x : ℤ_[p]) : algebra_map ℤ_[p] ℚ_[p] x = x := rfl

instance is_fraction_ring : is_fraction_ring ℤ_[p] ℚ_[p] :=
{ map_units := λ ⟨x, hx⟩,
  by rwa [set_like.coe_mk, algebra_map_apply, is_unit_iff_ne_zero, padic_int.coe_ne_zero,
      ←mem_non_zero_divisors_iff_ne_zero],
  surj := λ x,
  begin
    by_cases hx : ‖ x ‖ ≤ 1,
    { use (⟨x, hx⟩, 1),
      rw [submonoid.coe_one, map_one, mul_one, padic_int.algebra_map_apply, subtype.coe_mk] },
    { set n := int.to_nat(- x.valuation) with hn,
      have hn_coe : (n : ℤ) = -x.valuation,
      { rw [hn, int.to_nat_of_nonneg],
        rw right.nonneg_neg_iff,
        rw [padic.norm_le_one_iff_val_nonneg, not_le] at hx,
        exact hx.le },
      set a := x * p^n with ha,
      have ha_norm : ‖ a ‖ = 1,
      { have hx : x ≠ 0,
        { intro h0,
          rw [h0, norm_zero] at hx,
          exact hx (zero_le_one) },
        rw [ha, padic_norm_e.mul, padic_norm_e.norm_p_pow,
          padic.norm_eq_pow_val hx, ← zpow_add', hn_coe, neg_neg, add_left_neg, zpow_zero],
        exact or.inl (nat.cast_ne_zero.mpr (ne_zero.ne p)), },
      use (⟨a, le_of_eq ha_norm⟩,
        ⟨(p^n : ℤ_[p]), mem_non_zero_divisors_iff_ne_zero.mpr (ne_zero.ne _)⟩),
      simp only [set_like.coe_mk, map_pow, map_nat_cast, algebra_map_apply,
        padic_int.coe_pow, padic_int.coe_nat_cast, subtype.coe_mk] }
  end,
  eq_iff_exists := λ x y,
  begin
    rw [algebra_map_apply, algebra_map_apply, subtype.coe_inj],
    refine ⟨λ h, ⟨1, by rw h⟩, _⟩,
    rintro ⟨⟨c, hc⟩, h⟩,
    exact (mul_eq_mul_left_iff.mp h).resolve_right (mem_non_zero_divisors_iff_ne_zero.mp hc)
  end }

end fraction_ring

end padic_int
