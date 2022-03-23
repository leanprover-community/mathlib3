
import data.fintype.basic
import group_theory.order_of_element
import tactic.zify

-- set_option pp.all true

example (p a : ℕ) : (((p ^ a * p) : ℕ) : ℤ) - ((1 : ℕ) : ℤ) = (((p ^ a * p) : ℕ) : ℤ) - (((p ^ a) : ℕ) : ℤ) + ((((p ^ a) : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) :=
begin
  abel,
  -- goals accomplished
end

lemma sub_one_dvd_pow_sub_one (p α : ℕ) (one_le_p : 1 ≤ p) : (p - 1) ∣ (p^α - 1) :=
begin
  induction α with a ih,
  { simp, },
  { rw dvd_iff_exists_eq_mul_left at *,
    rcases ih with ⟨c, hc⟩,
    use p^a + c,
    rw add_mul,
    rw ← hc,
    rw mul_tsub,
    rw mul_one,
    zify,
    rw int.coe_nat_sub (one_le_pow_of_one_le one_le_p a),
    rw int.coe_nat_sub (le_mul_of_one_le_right' one_le_p),
    rw int.coe_nat_sub (one_le_pow_of_one_le one_le_p (nat.succ a)),
    rw pow_succ',
    clear hc c one_le_p,
    norm_cast,
    abel,
    -- (-1) • ↑1 + ↑(p ^ a * p) = (-1) • ↑(p ^ a) + ((-1) • ↑1 + (↑(p ^ a) + ↑(p ^ a * p)))
  },
end
