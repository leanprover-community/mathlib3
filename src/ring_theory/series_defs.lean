import ring_theory.power_series
import data.nat.parity

namespace power_series

section ring

variables {R : Type*} [ring R]

def inv_units_sub (u : units R) : power_series R := mk $ λ n, 1 /ₚ u ^ (n + 1)

@[simp] lemma coeff_inv_units_sub (u : units R) (n : ℕ) :
  coeff R n (inv_units_sub u) = 1 /ₚ u ^ (n + 1) :=
coeff_mk _ _

@[simp] lemma constant_coeff_inv_units_sub (u : units R) :
  constant_coeff R (inv_units_sub u) = 1 /ₚ u :=
by rw [← coeff_zero_eq_constant_coeff_apply, coeff_inv_units_sub, zero_add, pow_one]

@[simp] lemma inv_units_sub_mul_X (u : units R) :
  inv_units_sub u * X = inv_units_sub u * C R u - 1 :=
begin
  ext (_|n),
  { simp },
  { simp [n.succ_ne_zero, pow_succ] }
end

@[simp] lemma inv_units_sub_mul_sub (u : units R) : inv_units_sub u * (C R u - X) = 1 :=
by simp [mul_sub, sub_sub_cancel]

end ring

section field

variables (k : Type*) [field k]

open_locale nat

def exp : power_series k := mk $ λ n, 1 / n!

def sin : power_series k :=
mk $ λ n, if n.even then 0 else (-1) ^ (n / 2) / n!

def cos : power_series k :=
mk $ λ n, if n.even then (-1) ^ (n / 2) / n! else 0

end field

end power_series
