import tactic
import data.nat.parity

lemma neg_one_ne_one : (-1 : units ℤ) ≠ 1 :=
begin
  intro h,
  rw ← units.eq_iff at h,
  simpa only using h,
end

lemma even_pow_of_neg_one (n : ℕ) (hn : even n) :
  (-1 : units ℤ)^n = 1 :=
begin
  rw ← units.eq_iff,
  rw [units.coe_pow, units.coe_neg_one, units.coe_one],
  exact nat.neg_one_pow_of_even hn,
end

lemma odd_pow_of_neg_one (n : ℕ) (hn : odd n) :
  (-1 : units ℤ)^n = -1 :=
begin
  rw ← units.eq_iff,
  simp only [units.coe_one, units.coe_neg_one, units.coe_pow],
  exact nat.neg_one_pow_of_odd hn,
end

lemma pow_of_neg_one_is_one_of_even_iff (n : ℕ) :
  even n ↔ (-1 : units ℤ)^n = 1  :=
begin
  split,
  exact even_pow_of_neg_one n,

  intro h,
  rw  nat.even_iff_not_odd,
  intro h',
  apply neg_one_ne_one,
  rw ← odd_pow_of_neg_one n h', exact h,
end

lemma pow_of_neg_one_is_neg_one_of_odd_iff (n : ℕ) :
  odd n ↔ (-1 : units ℤ)^n = -1  :=
begin
  split,
  exact odd_pow_of_neg_one n,

  intro h,
  rw  nat.odd_iff_not_even,
  intro h',
  rw even_pow_of_neg_one n h' at h,
  apply neg_one_ne_one,
  exact h.symm,
 end

lemma neq_one_is_neg_one (u : units ℤ) (hu : u ≠ 1) : u = -1 :=
begin
    rw ← finset.mem_singleton,
    exact finset.mem_of_mem_insert_of_ne (finset.mem_univ u) hu,
end
