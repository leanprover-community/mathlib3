import data.nat.choose.basic
import data.nat.cast

variables {α : Type*} [linear_ordered_field α] [nontrivial α]

lemma choose_le_pow (r n : ℕ) : (n.choose r : α) ≤ n^r / r.factorial :=
begin
  rw le_div_iff',
  { norm_cast,
    rw ←nat.desc_fact_eq_factorial_mul_choose,
    sorry
    --rw nat.cast_le, --fails
    --exact n.desc_fact_le_pow r
    },
  exact_mod_cast r.factorial_pos,
end

lemma pow_le_choose (r n : ℕ) : ((n + 1 - r)^r : α) / r.factorial ≤ n.choose r :=
begin
  rw div_le_iff',
  { norm_cast,
    rw [←nat.desc_fact_eq_factorial_mul_choose],
    sorry
    --exact n.pow_le_desc_fact r
    },
  exact_mod_cast r.factorial_pos,
end
