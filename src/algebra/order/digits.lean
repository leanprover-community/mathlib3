import data.int.log

/-!
# Digits of a linearly ordered field

## Main definitions

* `order.digits`

-/

variables {R: Type*} [linear_ordered_field R] [floor_ring R]

/-- `order.digits b r` enumerates the base-`b` digits of a element `r`-/
def order.digits (b : ℕ) (r : R) (z : ℤ) : ℕ := ⌊r/b^z⌋₊ % b

namespace order

lemma digits_lt {b : ℕ} (hb : 0 < b) (r : R) (z : ℤ) : digits b r z < b := nat.mod_lt _ hb

/-- All the digits of greater powers than `int.log b r` are zero -/
lemma digits_eq_zero_of_log_lt {b : ℕ} {r : R} (z : ℤ) (hz : int.log b r < z) :
  digits b r z = 0 :=
begin
  rw digits,
  cases lt_or_le 1 b with hb hb,
  { have hb' : (1 : R) < b := nat.one_lt_cast.mpr hb,
    convert nat.zero_mod _,
    rw nat.floor_eq_zero,
    cases lt_or_le 0 r with hr hr,
    { rw ←int.lt_zpow_iff_log_lt hb hr at hz,
      rw div_lt_one (zpow_pos_of_pos (zero_lt_one.trans hb') _),
      exact hz, },
    { refine lt_of_le_of_lt _ zero_lt_one,
      apply div_nonpos_of_nonpos_of_nonneg hr (zpow_nonneg (zero_le_one.trans hb'.le) _) } },
  { obtain rfl | hb := hb.eq_or_lt,
    { simp },
    { rw nat.lt_one_iff at hb,
      subst hb,
      rw int.log_of_left_le_one zero_le_one at hz,
      simp [zero_zpow _ hz.ne'] } }
end

/-- The digit at `int.log b r` is not zero -/
lemma digits_log {b : ℕ} {r : R} (hb : 1 < b) (hr : 0 < r) :
  digits b r (int.log b r) ≠ 0 :=
begin
  rw [digits],
  suffices : 1 ≤ r / (↑b ^ int.log b r) ∧ r / (↑b ^ int.log b r) < b,
  { rw ←nat.floor_lt' at this,
    { rw nat.mod_eq_of_lt this.2,
      rw [ne.def, nat.floor_eq_zero, not_lt],
      exact this.1 },
    exact (zero_lt_one.trans hb).ne' },
  have hb' : (1 : R) < b := nat.one_lt_cast.mpr hb,
  have hb'' := zpow_pos_of_pos (zero_lt_one.trans hb') (int.log b r),
  split,
  { rw [one_le_div hb''],
    exact int.zpow_log_le_self hb hr, },
  { rw [div_lt_iff' hb'', ←zpow_add_one₀ (zero_lt_one.trans hb').ne'],
    exact int.lt_zpow_succ_log_self hb r }
end

end order
