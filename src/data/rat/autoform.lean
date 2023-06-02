import data.int.parity
import tactic

open int

theorem even_square_implies_even (n : ℤ) (h : even (n^2)) : even n :=
begin
  by_contradiction hn,
  have h₁ : n % 2 = 1 := (not_even_iff.mp hn),
  let k : ℤ := n / 2,
  have h₂ : n = 2 * k + n % 2,
  {
    have h : n = n % 2 + 2 * (n / 2),
    {
      exact mod_add_div n 2,
    },
    exact eq.symm h,
  },
  have h₃ : n = 2 * k + 1,
  {
    rw h₁ at h₂,
    exact h₂,
  },
  rw h₃ at h,
  simp only [add_mul, one_mul, pow_two] at h,
  have h₄ : 4 * (k * k + k) + 1 = 2 * (2 * (k * k + k)) + 1 := by ring,
  rw h₄ at h,
  exact absurd (even_add.1 h).2 (not_even_bit1 0),
end
