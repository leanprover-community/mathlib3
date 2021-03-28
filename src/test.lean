import data.real.basic
import tactic.suggest
import analysis.special_functions.pow
import tactic.rewrite_search.frontend

lemma real.rpow_inj_on {a : ℝ} (ha : a ≠ 0) :
  set.inj_on (λ (x : ℝ), x ^ a) (set.Ici 0) :=
begin
  assume x hx y hy h,
  dsimp at h,
  have A : ∀ (z : ℝ), 0 ≤ z → z = (z ^ a) ^ (a ⁻¹) :=
    λ z hz, by rw [← real.rpow_mul hz, mul_inv_cancel ha, real.rpow_one],
  rw [A x hx, A y hy, h],
end

lemma real.rpow__eq_rpow_iff {a x y : ℝ} (ha : a ≠ 0) (hx : 0 ≤ x) (hy : 0 ≤ y) :
  x ^ a = y ^ a ↔ x = y :=
(real.rpow_inj_on ha).eq_iff hx hy

lemma delta_A
  (A T ΔA ΔT a t : ℝ)
  (posA : 0 < A)
  (posT : 0 < T)
  (posA' : 0 < A + ΔA)
  (posT' : 0 < T + ΔT)
  (mina : 0 < a)
  (mint : 0 < t)
  (maxa : a < 1)
  (maxt : t < 1)
   :
   A^a * T^t  = (A + ΔA)^a * (T + ΔT)^t
   ↔
   ΔA = A * ((T/(T+ΔT)) ^ (t/a) - 1)

  :=
begin
  rw real.div_rpow posT.le posT'.le,
  have : (T + ΔT)^(t/a) ≠ 0,
    by simp [posT'.ne.symm, real.rpow_eq_zero_iff_of_nonneg posT'.le],
  field_simp,
  have W : 0 ≤ T ^ (t / a) := sorry,
  have W' : 0 ≤ (T + ΔT) ^ (t / a) := sorry,
  have H : ∀ (z : ℝ), 0 < z → z ^ t = (z ^ (t/a))^a,
  { assume z hz, rw ← real.rpow_mul hz.le, simp [mina.ne.symm] },
  rw [H T posT, H _ posT', ← real.mul_rpow posA.le W,
    ← real.mul_rpow posA'.le W'],
    -- real.rpow_eq_rpow_iff (mul_nonneg posA.le W) (mul_nonneg posA'.le W') mina.ne.symm,
  rw [← sub_eq_zero_iff_eq],
  conv_rhs { rw [eq_comm, ← sub_eq_zero_iff_eq] },
  congr' 2,
  ring,
end
