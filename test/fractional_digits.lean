import order.fractional_digits
import data.fin.vec_notation

-- ![1, 2, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#eval fractional_digits 10 (by norm_num) (0.12345 : ℚ) (by norm_num) ∘ (coe : fin 1 → ℕ)
