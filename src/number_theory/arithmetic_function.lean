/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import algebra.big_operators.ring
import number_theory.divisors

/-!
# Arithmetic Functions and Dirichlet Convolution

This file defines arithmetic functions, which are functions from `ℕ` to a specified type that map 0
to 0. In the literature, they are often instead defined as functions from `ℕ+`. These arithmetic
functions are endowed with a multiplication, given by Dirichlet convolution, and pointwise addition,
to form the Dirichlet ring.

## Main Definitions
 * `arithmetic_function α` consists of functions `f : ℕ → α` such that `f 0 = 0`.

## Tags
arithmetic functions, dirichlet convolution, divisors

-/

open finset
open_locale big_operators

namespace nat
variable (α : Type*)

/-- An arithmetic function is a function from `ℕ` that maps 0 to 0. In the literature, they are
  often instead defined as functions from `ℕ+`. Multiplication on `arithmetic_functions` is by
  Dirichlet convolution. -/
structure arithmetic_function [has_zero α] :=
(to_fun : ℕ → α)
(map_zero' : to_fun 0 = 0)

variable {α}

namespace arithmetic_function

section has_zero
variable [has_zero α]

instance : has_coe_to_fun (arithmetic_function α) := ⟨λ _, ℕ → α, to_fun⟩

@[simp] lemma to_fun_eq (f : arithmetic_function α) : f.to_fun = f := rfl

@[simp]
lemma map_zero {f : arithmetic_function α} : f 0 = 0 := f.map_zero'

theorem coe_inj {f g : arithmetic_function α} : (f : ℕ → α) = g ↔ f = g :=
begin
  split; intro h,
  { cases f,
    cases g,
    cases h,
    refl },
  { rw h }
end

instance : has_zero (arithmetic_function α) := ⟨⟨λ _, 0, rfl⟩⟩

@[simp]
lemma zero_apply {x : ℕ} : (0 : arithmetic_function α) x = 0 := rfl

instance : inhabited (arithmetic_function α) := ⟨0⟩

@[ext] theorem ext ⦃f g : arithmetic_function α⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj.1 (funext h)

theorem ext_iff {f g : arithmetic_function α} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

section has_one
variable [has_one α]

instance : has_one (arithmetic_function α) := ⟨⟨λ x, ite (x = 1) 1 0, rfl⟩⟩

@[simp]
lemma one_one : (1 : arithmetic_function α) 1 = 1 := rfl

@[simp]
lemma one_apply_ne {x : ℕ} (h : x ≠ 1) : (1 : arithmetic_function α) x = 0 := if_neg h

end has_one
end has_zero

instance nat_coe [semiring α] : has_coe (arithmetic_function ℕ) (arithmetic_function α) :=
⟨λ f, ⟨↑(f : ℕ → ℕ), by { transitivity ↑(f 0), refl, simp }⟩⟩

@[simp]
lemma nat_coe_apply [semiring α] {f : arithmetic_function ℕ} {x : ℕ} :
  (f : arithmetic_function α) x = f x := rfl

instance int_coe [ring α] : has_coe (arithmetic_function ℤ) (arithmetic_function α) :=
⟨λ f, ⟨↑(f : ℕ → ℤ), by { transitivity ↑(f 0), refl, simp }⟩⟩

@[simp]
lemma int_coe_apply [ring α] {f : arithmetic_function ℤ} {x : ℕ} :
  (f : arithmetic_function α) x = f x := rfl

@[simp]
lemma coe_coe [ring α] {f : arithmetic_function ℕ} :
  ((f : arithmetic_function ℤ) : arithmetic_function α) = f :=
by { ext, simp, }

section add_monoid

variable [add_monoid α]

instance : has_add (arithmetic_function α) := ⟨λ f g, ⟨λ n, f n + g n, by simp⟩⟩

@[simp]
lemma add_apply {f g : arithmetic_function α} {n : ℕ} : (f + g) n = f n + g n := rfl

instance : add_monoid (arithmetic_function α) :=
{ add_assoc := λ _ _ _, ext (λ _, add_assoc _ _ _),
  zero_add := λ _, ext (λ _, zero_add _),
  add_zero := λ _, ext (λ _, add_zero _),
  .. arithmetic_function.has_zero,
  .. arithmetic_function.has_add }

end add_monoid

instance [add_comm_monoid α] : add_comm_monoid (arithmetic_function α) :=
{ add_comm := λ _ _, ext (λ _, add_comm _ _),
  .. arithmetic_function.add_monoid }

instance [add_group α] : add_group (arithmetic_function α) :=
{ neg := λ f, ⟨λ n, - f n, by simp⟩,
  add_left_neg := λ _, ext (λ _, add_left_neg _),
  .. arithmetic_function.add_monoid }

instance [add_comm_group α] : add_comm_group (arithmetic_function α) :=
{ .. arithmetic_function.add_comm_monoid,
  .. arithmetic_function.add_group }

section dirichlet_ring
variable [semiring α]

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
instance : has_mul (arithmetic_function α) :=
⟨λ f g, ⟨λ n, ∑ x in divisors_antidiagonal n, f x.fst * g x.snd, by simp⟩⟩

@[simp]
lemma mul_apply {f g : arithmetic_function α} {n : ℕ} :
  (f * g) n = ∑ x in divisors_antidiagonal n, f x.fst * g x.snd := rfl

instance : monoid (arithmetic_function α) :=
{ one_mul := λ f,
  begin
    ext,
    rw mul_apply,
    by_cases x0 : x = 0, {simp [x0]},
    have h : {(1,x)} ⊆ divisors_antidiagonal x := by simp [x0],
    rw ← sum_subset h, {simp},
    intros y ymem ynmem,
    have y1ne : y.fst ≠ 1,
    { intro con,
      simp only [con, mem_divisors_antidiagonal, one_mul, ne.def] at ymem,
      simp only [mem_singleton, prod.ext_iff] at ynmem,
      tauto },
    simp [y1ne],
  end,
  mul_one := λ f,
  begin
    ext,
    rw mul_apply,
    by_cases x0 : x = 0, {simp [x0]},
    have h : {(x,1)} ⊆ divisors_antidiagonal x := by simp [x0],
    rw ← sum_subset h, {simp},
    intros y ymem ynmem,
    have y2ne : y.snd ≠ 1,
    { intro con,
      simp only [con, mem_divisors_antidiagonal, mul_one, ne.def] at ymem,
      simp only [mem_singleton, prod.ext_iff] at ynmem,
      tauto },
    simp [y2ne],
  end,
  mul_assoc := λ f g h,
  begin
    ext n,
    simp only [mul_apply],
    have := @finset.sum_sigma (ℕ × ℕ) α _ _ (divisors_antidiagonal n)
      (λ p, (divisors_antidiagonal p.1)) (λ x, f x.2.1 * g x.2.2 * h x.1.2),
    convert this.symm using 1; clear this,
    { apply finset.sum_congr rfl,
      intros p hp, exact finset.sum_mul },
    have := @finset.sum_sigma (ℕ × ℕ) α _ _ (divisors_antidiagonal n)
      (λ p, (divisors_antidiagonal p.2)) (λ x, f x.1.1 * (g x.2.1 * h x.2.2)),
    convert this.symm using 1; clear this,
    { apply finset.sum_congr rfl, intros p hp, rw finset.mul_sum },
    apply finset.sum_bij,
    swap 5,
    { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, exact ⟨(k, l*j), (l, j)⟩ },
    { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H,
      simp only [finset.mem_sigma, mem_divisors_antidiagonal] at H ⊢, finish },
    { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, simp only [mul_assoc] },
    { rintros ⟨⟨a,b⟩, ⟨c,d⟩⟩ ⟨⟨i,j⟩, ⟨k,l⟩⟩ H₁ H₂,
      simp only [finset.mem_sigma, mem_divisors_antidiagonal,
        and_imp, prod.mk.inj_iff, add_comm, heq_iff_eq] at H₁ H₂ ⊢,
      finish },
    { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, refine ⟨⟨(i*k, l), (i, k)⟩, _, _⟩;
      { simp only [finset.mem_sigma, mem_divisors_antidiagonal] at H ⊢, finish } }
  end,
  .. arithmetic_function.has_one,
  .. arithmetic_function.has_mul }

instance : semiring (arithmetic_function α) :=
{ zero_mul := λ f, by { ext, simp, },
  mul_zero := λ f, by { ext, simp, },
  left_distrib := λ a b c, by { ext, simp [← sum_add_distrib, mul_add] },
  right_distrib := λ a b c, by { ext, simp [← sum_add_distrib, add_mul] },
  .. arithmetic_function.has_zero,
  .. arithmetic_function.has_mul,
  .. arithmetic_function.has_add,
  .. arithmetic_function.add_comm_monoid,
  .. arithmetic_function.monoid }

end dirichlet_ring

instance [comm_semiring α] : comm_semiring (arithmetic_function α) :=
{ mul_comm := λ f g, by { ext,
    rw [mul_apply, ← map_swap_divisors_antidiagonal, sum_map],
    simp [mul_comm] },
  .. arithmetic_function.semiring }

instance [comm_ring α] : comm_ring (arithmetic_function α) :=
{ .. arithmetic_function.add_comm_group,
  .. arithmetic_function.comm_semiring }

instance : semiring (arithmetic_function α) :=
{ one_mul := one_convolve,
  mul_one := convolve_one,
  zero_mul := zero_convolve,
  mul_zero := convolve_zero,
  mul_assoc := convolve_assoc,
  left_distrib := convolve_add,
  right_distrib := add_convolve,
  .. (infer_instance : has_one (arithmetic_function α)),
  .. (infer_instance : has_mul (arithmetic_function α)),
  .. (infer_instance : add_comm_monoid (arithmetic_function α)) }

/-- The identity on `ℕ` as an `arithmetic_function`.  -/
def id : arithmetic_function ℕ := ⟨id, rfl⟩

@[simp]
lemma id_apply {x : ℕ} : id x = x := rfl

theorem zeta_mul_apply {f : arithmetic_function α} {x : ℕ} :
  (ζ * f) x = ∑ i in divisors x, f i :=
begin
  rw mul_apply,
  transitivity ∑ i in divisors_antidiagonal x, f i.snd,
  { apply sum_congr rfl,
    intros i hi,
    rcases mem_divisors_antidiagonal.1 hi with ⟨rfl, h⟩,
    simp [left_ne_zero_of_mul h] },
  { apply sum_bij (λ i h, prod.snd i),
    { rintros ⟨a, b⟩ h, simp [snd_mem_divisors_of_mem_antidiagonal h] },
    { rintros ⟨a, b⟩ h, refl },
    { rintros ⟨a1, b1⟩ ⟨a2, b2⟩ h1 h2 h,
      dsimp at h,
      rw h at *,
      rw mem_divisors_antidiagonal at *,
      ext, swap, {refl},
      simp only [prod.fst, prod.snd] at *,
      apply nat.eq_of_mul_eq_mul_right _ (eq.trans h1.1 h2.1.symm),
      rcases h1 with ⟨rfl, h⟩,
      apply nat.pos_of_ne_zero (right_ne_zero_of_mul h) },
    { intros a ha,
      rcases mem_divisors.1 ha with ⟨⟨b, rfl⟩, ne0⟩,
      use (b, a),
      simp [ne0, mul_comm] } }
end

theorem mul_zeta_apply {f : arithmetic_function α} {x : ℕ} :
  (f * ζ) x = ∑ i in divisors x, f i :=
begin
  rw mul_apply,
  transitivity ∑ i in divisors_antidiagonal x, f i.fst,
  { apply sum_congr rfl,
    intros i hi,
    rcases mem_divisors_antidiagonal.1 hi with ⟨rfl, h⟩,
    simp [right_ne_zero_of_mul h] },
  { apply sum_bij (λ i h, prod.fst i),
    { rintros ⟨a, b⟩ h, simp [fst_mem_divisors_of_mem_antidiagonal h] },
    { rintros ⟨a, b⟩ h, refl },
    { rintros ⟨a1, b1⟩ ⟨a2, b2⟩ h1 h2 h,
      dsimp at h,
      rw h at *,
      rw mem_divisors_antidiagonal at *,
      ext, {refl},
      simp only [prod.fst, prod.snd] at *,
      apply nat.eq_of_mul_eq_mul_left _ (eq.trans h1.1 h2.1.symm),
      rcases h1 with ⟨rfl, h⟩,
      apply nat.pos_of_ne_zero (left_ne_zero_of_mul h) },
    { intros a ha,
      rcases mem_divisors.1 ha with ⟨⟨b, rfl⟩, ne0⟩,
      use (a, b),
      simp [ne0] } }
end

end dirichlet_ring

lemma convolve_comm [comm_semiring α] (f g : arithmetic_function α) : convolve f g = convolve g f :=
begin
  ext,
  rw [convolve_apply, ← map_swap_divisors_antidiagonal, sum_map],
  simp [mul_comm],
end

instance [comm_semiring α] : comm_semiring (arithmetic_function α) :=
{ mul_comm := convolve_comm,
  .. (infer_instance : semiring (arithmetic_function α)) }

instance [comm_ring α] : comm_ring (arithmetic_function α) :=
{ .. (infer_instance : add_comm_group (arithmetic_function α)),
  .. (infer_instance : comm_semiring (arithmetic_function α)) }

section pointwise_mul

/-- This is the pointwise product of `arithmetic_function`s. -/
def pointwise_mul [mul_zero_class α] (f g : arithmetic_function α) :
  arithmetic_function α :=
⟨λ x, f x * g x, by simp⟩

@[simp]
lemma pointwise_mul_apply [mul_zero_class α] {f g : arithmetic_function α} {x : ℕ} :
  (pointwise_mul f g) x = f x * g x := rfl

lemma pointwise_mul_comm [comm_monoid_with_zero α] (f g : arithmetic_function α) :
  pointwise_mul f g = pointwise_mul g f :=
by { ext, simp [mul_comm] }

variable [monoid_with_zero α]

/-- This is the pointwise power of `arithmetic_function`s. -/
def pointwise_pow (f : arithmetic_function α) (k : ℕ) (kpos : 0 < k) :
  arithmetic_function α :=
⟨λ x, (f x) ^ k, by { rw [map_zero], exact zero_pow kpos }⟩

@[simp]
lemma pointwise_pow_apply {f : arithmetic_function α} {k x : ℕ} {kpos : 0 < k} :
  (pointwise_pow f k kpos) x = (f x) ^ k := rfl

lemma pointwise_pow_succ {f : arithmetic_function α} {k : ℕ} {kpos : 0 < k} :
  pointwise_pow f (k + 1) (k.succ_pos) = pointwise_mul f (pointwise_pow f k kpos) :=
by { ext, simp [pow_succ] }

lemma pointwise_pow_succ' {f : arithmetic_function α} {k : ℕ} {kpos : 0 < k} :
  pointwise_pow f (k + 1) (k.succ_pos) = pointwise_mul (pointwise_pow f k kpos) f :=
by { ext, simp [pow_succ'] }

/-- `pow k n = n ^ k`, except `pow 0 0 = 0`. -/
def pow (k : ℕ) : arithmetic_function ℕ :=
if h : k = 0 then ζ else pointwise_pow id k (nat.pos_of_ne_zero h)

@[simp]
lemma pow_apply {k n : ℕ} : pow k n = if (k = 0 ∧ n = 0) then 0 else n ^ k :=
begin
  cases k, {simp [pow]},
  simp [pow, (ne_of_lt (nat.succ_pos k)).symm],
end

end pointwise_mul

section multiplicative

section monoid_with_zero
variable [monoid_with_zero α]

/-- Multiplicative functions -/
class is_multiplicative  (f : arithmetic_function α) : Prop :=
(map_one' : f 1 = 1)
(map_mul_of_coprime : ∀ {m n : ℕ}, m.coprime n → f (m * n) = f m * f n)

@[simp]
lemma is_multiplicative.map_one {f : arithmetic_function α} [is_multiplicative f] : f 1 = 1 :=
is_multiplicative.map_one'

@[simp]
lemma map_mul_of_coprime {f : arithmetic_function α} [is_multiplicative f] {m n : ℕ}
  (h : m.coprime n) : f (m * n) = f m * f n :=
is_multiplicative.map_mul_of_coprime h

end monoid_with_zero

instance is_multiplicative_nat_cast {f : arithmetic_function ℕ} [semiring α] [is_multiplicative f] :
  is_multiplicative (f : arithmetic_function α) :=
⟨by simp, λ m n cop, by simp [cop]⟩

instance is_multiplicative_int_cast {f : arithmetic_function ℤ} [ring α] [is_multiplicative f] :
  is_multiplicative (f : arithmetic_function α) :=
⟨by simp, λ m n cop, by simp [cop]⟩

lemma nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul {a b c d : ℕ} (cop : c.coprime d) (h : a * b = c * d) :
  a.gcd c * b.gcd c = c :=
begin
  apply dvd_antisymm,
  { apply nat.coprime.dvd_of_dvd_mul_right (nat.coprime.mul (cop.gcd_left _) (cop.gcd_left _)),
    rw ← h,
    apply mul_dvd_mul (gcd_dvd _ _).1 (gcd_dvd _ _).1 },
  { rw [gcd_comm a _, gcd_comm b _],
    transitivity c.gcd (a * b),
    rw [h, gcd_mul_right_right d c],
    apply gcd_mul_dvd_mul_gcd }
end

instance is_multiplicative_mul [comm_semiring α] {f g : arithmetic_function α}
  [is_multiplicative f]  [is_multiplicative g] :
  is_multiplicative (f * g) :=
⟨by { simp, }, begin
  simp only [mul_apply],
  intros m n cop,
  rw sum_mul_sum,
  symmetry,
  apply sum_bij (λ (x : (ℕ × ℕ) × ℕ × ℕ) h, (x.1.1 * x.2.1, x.1.2 * x.2.2)),
  { rintros ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h,
    simp only [mem_divisors_antidiagonal, ne.def, mem_product] at h,
    rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩,
    simp only [mem_divisors_antidiagonal, nat.mul_eq_zero, ne.def],
    split, {ring},
    rw nat.mul_eq_zero at *,
    apply not_or ha hb },
  { rintros ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h,
    simp only [mem_divisors_antidiagonal, ne.def, mem_product] at h,
    rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩,
    dsimp,
    rw [map_mul_of_coprime cop.coprime_mul_right.coprime_mul_right_right,
        map_mul_of_coprime cop.coprime_mul_left.coprime_mul_left_right],
    ring,
    apply_instance, apply_instance },
  { rintros ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ hab hcd h,
    simp only [mem_divisors_antidiagonal, ne.def, mem_product] at hab,
    rcases hab with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩,
    simp only [mem_divisors_antidiagonal, ne.def, mem_product] at hcd,
    simp only [prod.mk.inj_iff] at h,
    ext; dsimp,
    { transitivity nat.gcd (a1 * a2) (a1 * b1),
      {rw [nat.gcd_mul_left, cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_one]},
      { rw [← hcd.1.1, ← hcd.2.1] at cop,
        rw [← hcd.1.1, h.1, nat.gcd_mul_left,
            cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_one] } },
    { transitivity nat.gcd (a1 * a2) (a2 * b2),
      {rw [mul_comm, nat.gcd_mul_left, cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one, mul_one]},
      { rw [← hcd.1.1, ← hcd.2.1] at cop,
        rw [← hcd.1.1, h.2, mul_comm, nat.gcd_mul_left,
            cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one, mul_one] } },
    { transitivity nat.gcd (b1 * b2) (a1 * b1),
      {rw [mul_comm, nat.gcd_mul_right,
           cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one, one_mul]},
      { rw [← hcd.1.1, ← hcd.2.1] at cop,
        rw [← hcd.2.1, h.1, mul_comm c1 d1, nat.gcd_mul_left,
            cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one, mul_one] } },
    { transitivity nat.gcd (b1 * b2) (a2 * b2),
      {rw [nat.gcd_mul_right,
           cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mul]},
      { rw [← hcd.1.1, ← hcd.2.1] at cop,
        rw [← hcd.2.1, h.2, nat.gcd_mul_right,
            cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mul] } } },
  { rintros ⟨b1, b2⟩ h,
    simp only [mem_divisors_antidiagonal, ne.def, mem_product] at h,
    use ((b1.gcd m, b2.gcd m), (b1.gcd n, b2.gcd n)),
    simp only [exists_prop, prod.mk.inj_iff, ne.def, mem_product, mem_divisors_antidiagonal],
    rw [← cop.gcd_mul _, ← cop.gcd_mul _, ← h.1, nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul cop h.1,
        nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul cop.symm _],
    { rw [nat.mul_eq_zero, decidable.not_or_iff_and_not] at h, simp [h.2.1, h.2.2] },
    rw [mul_comm n m, h.1] }
end⟩

end multiplicative

section special_functions

/-- `ζ 0 = 0`, otherwise `ζ x = 1`. The Dirichlet Series is the Riemann ζ.  -/
def zeta : arithmetic_function α := ⟨λ x, ite (x = 0) 0 1, rfl⟩

localized "notation `ζ` := zeta" in arithmetic_function

@[simp]
lemma zeta_apply {x : ℕ} : (ζ : arithmetic_function α) x = if (x = 0) then 0 else 1 := rfl

lemma zeta_apply_of_ne_zero {x : ℕ} (h : x ≠ 0) : (ζ : arithmetic_function α) x = 1 := if_neg h

/-- `σ k n` is the sum of the `k`th powers of the divisors of `n` -/
def sigma (k : ℕ) : arithmetic_function ℕ :=
⟨λ n, ∑ d in divisors n, d ^ k, by simp⟩

localized "notation `σ` := sigma" in arithmetic_function

@[simp]
lemma sigma_apply {k n : ℕ} : σ k n = ∑ d in divisors n, d ^ k := rfl

lemma zeta_mul_pow_eq_sigma {k : ℕ} : ζ * pow k = σ k :=
begin
  ext,
  rw [sigma, zeta_mul_apply],
  apply sum_congr rfl,
  intros x hx,
  rw [pow_apply, if_neg (not_and_of_not_right _ _)],
  contrapose! hx,
  simp [hx],
end

instance is_multiplicative_zeta [semiring α] : is_multiplicative (ζ : arithmetic_function α) :=
⟨by simp, λ m n cop, begin
  cases m, {simp},
  cases n, {simp},
  rw [zeta_apply_of_ne_zero (mul_ne_zero _ _), zeta_apply_of_ne_zero,
      zeta_apply_of_ne_zero, mul_one],
  repeat { apply nat.succ_ne_zero },
end⟩

instance is_multiplicative_pow {k : ℕ} :
  is_multiplicative (pow k) :=
⟨by cases k; simp, λ m n cop, by cases m; cases k; simp [nat.succ_ne_zero, mul_pow]⟩

instance is_multiplicative_sigma [semiring α] {k : ℕ} :
  is_multiplicative (sigma k : arithmetic_function α) :=
by { rw ← zeta_mul_pow_eq_sigma, apply_instance, }

end special_functions

end arithmetic_function
end nat
